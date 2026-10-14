-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2156
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:49:00.125156+00:00
-- url     : https://prove2.me/submissions/93c20a94-0e41-4fa9-b87d-fb18f982f034

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 387589928 ≤ n < 387769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 387591178 1250 387589928 387589957
    0xe04060c020c130c030c0e010c0807110604081005010e070905040b0109030c091a0303071101120609090b0a0b0301060515072609010f0509030604020d080909010b0a02010f0504020307120305 83
    0xd0f03080b03508070b6030141000c03140e161001c0108010f0700b2002d0391070004000c2400d0002c0e0124601100245441c0d000d4242c131880fa15810302600103460002c1d000740c00580240702d2a03413002404003403506190291034018001e4018100c241d050540009001c1c200c10300a641c06240c0347c0c030b0150810f034480c04100004640048090800c80e80b02d524800182c0100c01001c900c0401c407420703c0d0483d16000c400c03950895440392014040e6038040c1c00658482c0101d0140007890790b0b68040010ba04e91182c0111001c2078441c442000344e07850441806800c940b000703030311b40e070007a85425000d001c0c030340721044c9040410301d040c1680764980500d441c0018481c000c0b0048440c001c642c003803030000d60b00808409801301032401d0b200e0041001071048110b415000d051322207545584075102040150508184245105008190030783c5050100f00c08540701031001c2e80955403c5c00001402130031a6428850b504024107100014810390500d50000f981d184001e001e0716549000241d049020103005d03108882090300c15141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 387592428 1250 387591178 387591199
    0x30206160f050d030b06031303030c110f0631030503062d0906030a03090905060a3614060f030a0b01060503010509071119030216090203010f0b040e04060c020c 70
    0x800ca40c5502c0c04030703401c0000c2800c0c0f44000317502c3c0c50301505903881604201405442580d15445c01c03006070800040d504c041c1700041310030a14010b400d00103441c94030118002406030381054a0713064101407103120340c00c004551905445e82c00c80224515040847d4141c500a07449441d0000080d103010490301d05024400140440400021030001c0d846101d03800c100e41c0201c8603076034007040c19107a1510207401000110425020300c80c081c0d0310f0340a503800440c0034160034900343e251560301d03d00c101e1244141c028050b54036204034618103e10340403c140c1c500c484041c00899502382c04090b040b900505801c1c0b00d441c9a0b1410115a1000c02022845603003101f15011156550030000c0d085030300c01e0040781e0140b0000000039520302d0081d01e0b0309601050441c02002044080f0b508010a480700c01d02c100d00314010a2231544090b554120843c015003040000181e6952400f1980b066440c2560301401d40c411081c80300700b14050100b8400340c0d105400c1600815002800c1804904013131100d00602e43c003031000d91 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 387593678 1250 387592428 387592433
    0x10213080a0b010501180603090c05040c0806040506240d0906020a09170d09030f020102010e03030117070e1003021201111b1b0609010507050304080f010e1501050109030206160f 78
    0x280281c04507005059403001da03601d500045441907201d039400441031840110400c00b1600c6944508003181c043c403610120302d5101d40000701a17804000c00d407400a40707003d0900416151911585c0d4200404890021f08200003d0425030f804401c01c185151003a00800c4040290030304c5d4010450031030b4424000c651b201008400681480e4560241c0c1803c0e40102c081c209000300d001480390403000140c0c07681d8a41e9880c550303590400307103d01d040407411035485455400020340104061030213000070b10000ea91500c03d0400a6180038104e038442d402d07522040007800800d8145000c3c250030380ea015070300420941d040006031400340003404030510150400003070380d204c840a054007000451080e00f064a02c3d02200c02c0c101c8602070f0100e50742a0348410200880b903159800b40d4001c041c994414230550741003c0e9100036150801c0b09a03c1c0f4450640d440d0450502091000d21252001d02001c40c00a4465418000003d0410340d550200034003540c40012581c40c01c0103140000d0081a80c0240c000d2402021171 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 387594928 1250 387593678 387593683
    0xd230f091302070c0b391c0f1e080718060807031a01120b0a0801060b0307020706080910180209040f0203070f060806100c141b0402030c0d090501021308 67
    0x43c1601c21180d2a180840c1d8042c550040383d0410b030803900740901480c00030300780b00d07030b12200058031145e80703929400a010101420b0100d59900c0c4428128100c002000940c0680b070030307458210341c0003042000d02014120107190074846603e60481d282503d00783d41c86202c10f440c00322418002c1018400600e0000030fa541d4825800d0b84280c0440c0d50500c4040000c00d44110310800044100f07003c41c07507000b51945a11142e40c414800c200b0000e03c455100341e603500d0080d00f1501290000d950906000040054494040201200900d41c0389800062407500c41c9440d0744541140c80400315603610340c030445a09401402c10310f01010707002003035480c060600345440000c101007070350201e00a0080380d07000560ba07001e044405088801c180c03500c0203e0382d62002004550a00001c800d02444010741e158030100c0c161682040145082e2002000c182ca90303d00c0d440300c500300c51001d95100d2030040082046c0e00c907081c0252243c1d81160b0743c0210340d4115515000b80079000b030984628034456480000038602200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 387596178 1250 387594928 387594937
    0x220b15030c0310060f0c03080403050d020403050c0325140a0f060302031008030c0c06030c07121101140412030218090a061806121502190302030402030d230f091302 72
    0x1500b003c082032030750320501500d10700600691040824046446000464041d200d50343d0300501c02d02e01513203070004904101081f1380041d001030702c15500c03000e00c0c94600e050800071103070740340b800d500e44103d22003440c5403180032442680680a4540c100501d043c00302d884403054140540300b000810400d031074440500030002e400c01c0342d01120200105600284d4010b02004650944852501803d04c119031038040c0700c03940c0c0c0041c080b2150b0303c40410188000c50254400000780c0d08150352030354404c125001a141c2901c0c488100891f2912001c4148070014038001d152941c0f9011909000d61a082c031081c01400301d0a0985206030405140f0040000d0201c448d03000c0c200f0389800300c80b500d1854105043c0300c0c0c00c0700e07080c1c0510400c3e0300e4544440c01c04a44016802001c054190074090324101204240d0a41000c44441c840c003c02d401100788001c514060003803031955421881e104c00002c01410414580b040e540d003025015140004030140c540d0305030000c8448038003018000305291580b050360203000307601 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 387597428 1250 387596178 387596191
    0x609120206251a04121e05070201090504020307030518060112141009050303090124031119180b030c03060c0d0902030a0b0f060105030403020c150918010311220b15030c03 75
    0x56000c1c04401c1c2501400d40018800d40310001804046d011082c1901c1c10f52010400f607041c410007400009555480b800210f00c100010703500412642007060f005e2500821048c840c03122600907800500c01c607a01500c5869415803c181c0d0b02098100340c4012034140400410118242800c2454220a214000009500941042001300440c00202009070b50b4060480b89d60306c080182c01c04100040740313042d03508201c680402800c030741940c406040c00d612004001d611a08180303c0000b0200c040c01d9103031080303a40c20320080e000f13412040603520002ba1140d230b000f40707030742c9107040d002c2002c07001c0c0140c41c2d022204032940a001c0300c61659a508080040c0c071805c407107158070f651003040010042d5200380c007a640640c0e496001800594200750400843d14194070130410180003e102c4c0e541d06a0700c01d0000c01510078503104135030495045007003030071580c4121400705020f018500c03102038000c550140c54079000642c3d54000075100c0d070400005140011148203d50802c0404814802c0c644210401076000b080d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 387598678 1250 387597428 387597443
    0xa260304060e0d02010c02120310180911040b0d02011d0d0b0f1803031801140103030c1101020c060702040b04090f08030717040b0c0a0e03070b040609120206251a04 72
    0x1004150100c1c00d0b15200c004e506d00580128100f40a200c50020242d9085112180b888905a40310a0281d0000c411031209241c2d071619991300f0000d100700241d9134002c50200b036809014112288020491101c10954024100580c04402814880c050b00c0f1400407008018565a104480790410200c903440540351100d000ea000340c04143e00100f030591451401c42c101e030146013581d680c8035144100d0794488101c90525501c510440b42000311140410b8040c6100e0b44400d0303030079021400d01c5285000d81c90b80c240c2c10b560041030500701d10340e504000e840080307038100c0c0d0101e11000c0f09000704e00580b20070708005002c09034503003101c0704201c0500d01075842003003542c0d200700040e1010340356801450001d480190404000401055000c00f2144c020a84002581403490240c180c0001180c1b402c0851b50042d104640c0101e001e002881d4032010401c01800354841b54041c14400360006400c2d4072502d040014550302c4001c1e100c2c070041e48804801259a004082401102080c030351b400135880c400c0350704540c40c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 387599928 1250 387598678 387598693
    0x70918060515151c110c0609060702100908120403030e06090a0f20190924060e0102070f0f090f0e0606040b0a030b1f080a050a260304060e 61
    0x6500d002003440b55064000e00c08109030100728401c0145a01000c48040c3c041c1c58400142c00000b01400b40d50f003800e5201c4003050b42c034a03080105030f062510242ca00801ca42080c4203000c1c00c2039001440048030080028001044c04c16803901c4520342c401d55600304c0d04601d540080005043d015070040444191910a40b07003150340b080780e180d0f110003070440c0c02880c40100f625880007080200880c1013141c1c2840c610310884204030400903078949480b0f40d110b28000c4220100b4055500c2d24014141800c0c0010702441801c14941c6509074060740d903020744801c2104000c1001401c0e0b100300140002082015201d407a055103651082e691103072030f4090a01c046003030111240d21a902889840c4109508101504c080e4aa02c02004080d04601c0e52481c1e00c144402030210201312020b06440c05207500403141c0590441030f40b043ca00025081e404080c46410881404000c103c000c0f400b411040d42c08048511301182d8080c00c00444080324000c010300190200c10001048010390010180c44012411a0b440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 387601178 1250 387599928 387599941
    0x2e180302070b040b070b0411120a0c09060501020a02060c030f0c07140a03031b02030708030d05010f0807080d030507020a1205090a0b04051302090f1903120305100510020709180605 79
    0x42d441030f4030401d443d0301001c0020703002141da0789028075006071042481128101340781001484408070300d100100940c109260b0760003000710440c841c0c1c0c024200c10f681030000b1403910700040c0d1102014040640203280008030b88404403414401c803000400841704680e2200b60403028195182541e004100c0e80c01d0a0041c1d0203120704d0009030354030407a5810b9071041c0520034062407010040049050480c0c05119a0801264400e030034809270152801c0d40000054035890700c0d04d020911070069002e54019084108240241d4801203010300c08035880b0309001c41c060301ca8200c00c901c0c1102854001c0c041e0500d00d40441c0180b6400001880e4a0500300c0d8080341d050f80300c15102039a40304502c00c09038004510368602c11070101c95000b6080200000b8070035400f403040000424100c60001c3c00c144401740081100748104144c80245480c2c81015140c200b0035458000413180160b141402010b10420b820103091982510800180018001c241c4c4248049950021100c240c0384d0303d00b00440c0c9841c20310300041c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 387602428 1250 387601178 387601199
    0x409030203131d060f0a0e011706010f0e0408030921072a0501030c02010b090906010612050f041e05070305010213052202071a010807170d022e18030207 67
    0x1030703c1d5400b0180031066100c0d00100302e0400030004210380c0058070004001403285180d0404d500030900351442689440561404505014050300000348260f4a48000d0044490b402027148c0d20517030040ea0f0544d82c0c0c4550155074130781415190488482d451250742c3e540c41d000c1c014003030451b6030320a0032900080c010b9051500384080e01900d030840c0b616428501004658070942004801608a000009071901d9501c0400c0400100f01d41803030440d440440104802a8410004480c800c440d0104010070b007404100309802031000341002d0f0400307481c1d090440c400c2041a507400007459002e400c0341c02455480c80c12034042d40050341c444140000380c080025450822101c80c3d0022108801c3e60464101d840c03008070003e401c42c2d00140c40074038030b112900d0003d005111005010700220401440d11501d401c003002d40741080c504581c01550466810450b50540019801148803c103614090702c951680c0d00c040da0000c810680111214140002d071038200743d061112034941030107075003558421900c40e9200c44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 387603678 1250 387602428 387602459
    0xa0f032102150610090f12020f09010b04090203061206040303050a050612210c0f0303240d06050c0906070b100806011a070c35010c0203040b0315040903020313 70
    0x603849212040064004c1c5411118164403812030b080603549561601d40b50300201c59141c11201c00c1c88010f85618003580703010410b000b003100b41103960318900d60510070262000c0c061441071030740c0d0540100200e415a6110310382b0b0b041d030403900e800300d46080c07405041c0100a401d050362007a401c03910389004102d141c10b012070100c404484001c0146040700d440a880002440d90021400d94070209001c0300019010034040958465000f030300958903800c04d10074480441d03008110a80c1060740d540b4481c00c01d600c404448850a80e007004000640703aa41108002c550b1140c1c007042540035500180e82000c100d400c5c80014080e00d030301c0316118445611041c21035644c01e000e001d00811758002c4448061141406401070900d42d01c40d010450086540d001c1e4242141100c0d501d880541482c5001c0750f2400c002c0e01031802509140000a1006400d1940003a44a100d01d000300141c0660002c00104000001440b64250f40d0b0040e10070000c800c0d860900a480790082c0c91b0201e00011960740000d4900300d03c04200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 387604928 1250 387603678 387603703
    0x2603010b09012006040c0816060e09070306030803100e150d0f030e04050c0d0b03010c0504060e0a03080d020a140720030a0506070207060f05120a0504020a0f032102 72
    0x54038104841d001900c160008018600307840c0d5028042c8055500140105409180b06440720607006043c46096810a140c41c0040c2a15190045003080159032110680034079200945480340c043d06c60340c40c00c801904e541c7e00b01400c0c0580000034021820f02c0c0e43c94040490740310f064900425180c00f2880740a00056584c4180d200030780600c5d800104c0c0e850085c0034100c621a0806c100da8080c014082030603030340100e410039840c1070b000c100440c541915005600103a4811402001003101a00010703041e401035006103810001410107081807a281d000b00a0041e64002d076000c1d03115280c814000029500404014000844100c08024101c1210059071421940451850b00781841942400c1e000c0b0500200b05074113200b0358201e10f0214100740706041c080c1899501402c040e43c2000000f802800744070605804005d0304112028034030703c003541460703080080c003000070809481d5400020720a030080e0300b00c140f103404051000000c1001d822051802000c04036038940d11010512000c2e40c48d9a000e4242c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 387606178 1250 387604928 387604949
    0x5150301030c09330302010e0d2012030705160e0f04020603040f02091e1b180a080607030204260d2a0506100f0605071704030609260301 60
    0xa12100f01650441d050303c0c804500a4101c0c03032110880000b54280364240035250a80b991002e01c15542e0004540810230010f86100c129450750ba42c07806010018080d8442a9101a2080203203607030b2540004503103852041c00300c0f80c0382c0e1040d041850f00c40c848481c0841001c4051100080c40b00007000801d4400c0c100064200d000780d840340c00344251940020001ca4003039401280b0007005030f8030700207803e0152403d41189006020000d880c98040000908490f00c2d003801004034100c06603240080300c009000d03000311107542d2041139011034020542d5821040c054010b2000300032000e58194064800c49881103084800e01c3c1a1404034441248409000030345500803805030341c4082d01412001d850a28184079104140d0201e502461000c074108000300d03100d8000c074090100c2c1c55031945450001d0140c0780ca000043c3c91800401910a220b10603004008015140705036502c003c0d010240d400541d0442d0060011040c140b400c0c03101e80e101c410150440300100c43c50072050340590011b49060700c551105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 387607428 1250 387606178 387606203
    0x20c070e06030304210f05060603390a050604240f0c020105070c09020c010b0114090307050112020f120106120b1e040e0109050a260405040c270515030103 68
    0xe1745109442c03030031000590841d0400f104000502d100080d0f020b841c003500181800b0f0400b00b08041c03d0880d030390300c06501840c0d46030b4400010204124030202913a02c000c0046981e1700c601c80400c1a031416580704540c484c102080025401311603485210000071620f10b00352045600c04810707105803103070704020f400103560843c0d400300650185005010060140080409055a40344210144e92041600791400c0c0d445a0307000c0210358003d4030b144804001c02021380c0c00e00c140800884d50318501842440d0412214069509140348154110303040b0103039408410f982d8443c05031503541442003c1c0302d240c00003001c00813950600c3e500f0b40b040c800806001846227040101e01e001100d040021441619130141d41c030000c81c83c42c01000d1003400002c521440c0504003010a9080c21403405184111000c1d100300c1c880041d4940d210910200c0d412388208550000d007041c0742420498604014100450310154111245064205031000d110111841101c00f081d005150f03e00301d05490000b03102c0205005140031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 387608678 1250 387607428 387607439
    0x303091b120a03030e01140c0306100512010608041101020312073c0813030503060415090510150201020405010915020a0f0c180506091324020c070e06030304 69
    0x1041480080e0300620741003601240d14a2207060040d504412008a5a10a4161000f050a000321000f1b0360f02d0482a40c050700c0c000e621802c0b2440020622445801e9003940c5065441c0a001960089000351044c070500d580c42d010040e22100e4240c5090380d58048004036000558400000c4a5004008280c0d07110140c465000a41c0e00c040180e0740080f000c08011300c00c40b1125002d0783e40d04071115840902120040f0031207405400c1c85800352444981c08140c6a602c80800e0b002011290401c006842c001340c4c80124104134034503158a40c00003c4801e042105000300a400048103000f03031080809200410f0300c83c0901a800c0348200d1082501041100c0c80c10400070507000c00c034602600650040d075131410a1039030f410712a08104841207e01e0304041c10240719a88810851800c00b014800c001c003c0760030914005442c1550050a0403407000c0030030380b0941000360304141114102e42c4082d58888070481003d0b51b50194008015140d454442c0c210001507007168503c01d00c0c02050040c01451415080c503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 387609928 1250 387608678 387608713
    0x201080402031c170901360c030807120207140f0d05060726061503090106030209091b04060311010809011104060504051c08040b0c120705060702060702030309 70
    0x5000340e80c98050542c0d00740141c043e03031080310800b00065070780c40e102100042e8056030a80d800b8101208581c50070500890200720a50102094010024449155510702c03035620400349400314020b040d010100c42c00010008031101400120703200b00442e48005840c80c4040f41e1704c1c0c600d84103544070b00c5950150003009041c038441000140707001509008a03614162185490000300703541282c0050329145c1484240340c2080690300d040300902d51711019506140c0300091240181c0550f03003139802d4001020520717001007580000000c6a01401a41e094501743c2580f68640101c0d035024131204a80d413200c071009151034401d6205803540003054103c60360040d4011a90100c00918041141d9a609104081d10610201400043c405039036115515400c02051101011024410035640421072607000c00290307080007078405503466013070343c11744403101c864031180740c010b480c0080c1c0d020340000500d000a0002c08a405889510a41c007110040c3d1030351442240e484c0f000b1108104d2a0304440421010401003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 387611178 1250 387609928 387609931
    0xb010909050f0f0f070b2701170106080a110702100e01120501030b0a0c020309150a02010b0d060b09060303190302090d0203030d0c12020708090f041509020d0506120307020108 77
    0x101c040741d40e21120703480c00358036203144508000d00c15400a03c00d031844a00400003100130340040300320541080c25809107501840c04084041704c28000030101026140d2259658641c01c0b0031103034075038445595481d006008502e054400b601d00c1420400c04480c0b00da50348080f80da4080d03002d030104011140760700302101c1c01403582d4515410000c0810702180c40b0445805020b000e54003c8050311001e042a05c00002240e0784a5a8141950014024422035030358901e40e00c0242c0448007045680c2d00d095100490050100c904065031040060042d0300174842258807480c198101911180c445888000c100755882c0a6056091030740d018185038026010311039006000e9001300501400c1e40320300a6070009081d074002c191013583d000d079521182c1d22001c1c0d002d8a0880f4503450300101314a4425603031100101486a586014018820300c0306142868a5035030100c00d40740315080345180900c0c0c1b0754040350301a6206c030066550160800c80411028908030110119a00c40003008515142913a401503805260 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 387612428 1250 387611178 387611183
    0x9060c030219020d05030a030b030d0f0c150e1b1801050913060207060516030f33050a18060f12060c030e0607050d060806060d2d030504090b09040b010909 68
    0x105013130a01c00040b0104080c00201803071ba01c0100e00c4455070130a1510788482102c000d0208500319245c0001c0b03e4024440080c590b4002d0300200d00500d01c800c45901a01041c114040c3c0c910800303080044480c1c0c42109190480380c21619071030141d542801510b0382d04000e02416074008412004240a0700403804148442413190101500300a00c9032100030444900302d540c40d1a20070308822100407503902d072082ca603904200c1c01041103c0070180500d40391100890401c1469101e00d800c3c8180b00b01400700551004210007020355000c99103070044a901401e904618112003030409501182220300042410244c070b520f02202c0c030046025131035100240840c103850f10181580d407202801d0361402402030340d12940c502c0e02c07050369480b541d015040c201c1d601a88942040d811034000c0c0511552041017508050b90004801c280f04181007404145510208541180740040000190101500040580100c2c0c070f0240c000c02145070640140719403c0c45c00c603401404c0c034408030700510800140381d004920650 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 387613678 1250 387612428 387612439
    0x50307030605180612011401050d020105040305070609050102060901060509040602090f04060b0306120a08070201051312031701082b020a06021305040522030c1a0f010609060c03021902 81
    0x40d0b44101182c0019a450080d50400060788104071310303410440800842511003074000c115500d4104e422012404041c010944540003042c9203005680c4074dc001c1e240519001001e0782c00c00341c0c0c0d076840502040401d105890143c042c0700000b404500041c4a145c1c2115000b900940c850344d11652820001e502032901558002e034221142990354444c4d105080103011605540c41d17885c105038042080011421a20400302d5010750860000500320200342c94a6550a00b40b150f103840100d400c401c0031a0054105c20340f0180c015114800b8107511501c0c4a0b1450035030b05107840541d81310ba000c01d403180b186440c0301011400e12044400405e1840c103003074200000b20701c1514038000e03c41d511030f410b0303070f100940348050425821020322180c51305120f00c03034100650241c1ca811084c40d07109881219000f5010203014014a48950014001219441e075441c1c1d0944810b54814980780480001c40102030051a0001e100c540c00803a0341c50040a544012540503001000720754040c0001113811206848105d8105 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 387614928 1250 387613678 387613691
    0xa0b123301080c071e052116080403050307050c1314070c030e030f1506180a0b0102010603020d0b040b070e011d060405190914010f0603180c14010e03010606080705030703 75
    0x42c4561030380745c0d41e03001d0b00d0031a031074150842e08200d4640402141c03094000000050480c03451020501103895600c28860103502010f024104007903107001d258070203009400001015410800d01040b05103000004840c190440d00945469201f2a102000c541451210300390114a4860090740c3c3d24a280d0310074940300206517000d401090420115000d20a550340c00080740c504641080358082d40d0105003910a1440e02904d081841c14024011341a580f14a50314a0201951391003908020f01854002d030800c18800e0040c50b114248001c1150140c1e0b407080c07039801050020344510022043d03040b0594480101c403030310264003d081e4122400080d80220104000103654442c11f40004c21640b100240c0d1050702d24207099441500c1c281e03894142542e800000601051b002188d004094030040e144c001003119100f2094480d2412000001d01b6641c2c0d90400001c4c040e0114005240040086c0d0b0b542c000c00000741c003030500340e0740c05004c1d010200c1d0343c050001d44014458006143c1c401c45500d0003003001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 387616178 1250 387614928 387614933
    0x501080703050a2901030615020a120c080a05030402031605013f06180b0a090f140f0601020c03010504050d0c020a0b0f13080f06070e0a0b123301080c07 67
    0x48841c801a03014801030764071010b4141c0d0f81500c25400141139920680030b400c0480321000b511003200078401004504880c1c91445450302c219500f330070060340032007a15607036010418050000c1c2c104440480c4030b8070840419900b210000c181c41c00803500180c460701c200074505245140212043c1d110070ba1038290307248881d84455941c000303000e00380001010001c0c607079080800103205c1e2031000e5800440e2a050140c520000e40707905100304d007110309611000541c50301040e40c03003024200d044e00740740c0000c0d105801c2c031090702c0c210300141c1c1c0210700076000c1ba5212840da00c00d03d070030b854040b607000d001500708044078144a4098040700080d00d2005040340d0707007242c44401ea03c045400a584c0c0c10015100440c0c20328034401d4903960b000c05004840c00030102d58200609096075907c00600d241c040002c4100204425255588100c000e0565038101546460600c4c00c0071090110440e16011501a0313200700741c0c42c4c545407841d03c11012681c0d8011188000c3c80c1d600640b90b850000c1c01d182040c45042001001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 387617428 1250 387616178 387616211
    0x1e0f030114060307080d0e01050a031d10061505030105060906070b0f04020f01050415121104030f021005040f03141018052a01120b03150a0f02040501080703050a 71
    0x2030404005201c00d21606003441450b140c0751144d04151100c0e40700465001096420440903242e4250901c3c00741d5482c07284c13000440141522024600c1720800c0d08043e001e014070b000c40c0c40f5591307502011040200b03554400320005070410486140c0042041000140030134201640144641e280c098021403400910303036079000030307040c0450300c030301441c24404148021071410b418448400c0c4000d1900701d0609050110903809075080c0c0d2400c1c400c1c00716a040040d91048250000720103c0ca40d80011038591755070f820101522120890102d02c9090070000c1c00074014060300680f8103581245070314403916425569482000a44440d404401d803240450f042c0451403140210707510380c0d41000b140300c40d00060b8600140303403400410b04240c00202916619624030355529200144010901e0483e0010f02410091801011400402605402801800915001c0054103580076641d1081d0402004216480800481c000c6004041c0000c5ca03400109840500c00e070030280c1c0101041a0000320618461004a03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 387618678 1250 387617428 387617441
    0x1a04150501050f19081603050c1008132d0501050615091c0204020d09031d012a08070507080f0a02060319020d06060f14040312200607020c040e03091e0f0301 69
    0x40d4146c0703c03441c05004015003400880d0b040c40e404d071040d2400d03100c800c1c40034000350700c0140342c1c2c1109200743c41e0b13a8050140b01164155150010103102607051a00103003d8000008210140c80e15800c01001c0b4056007000602100040c502d4000c5030305206103c1c007040000700401c10710003482e101c1500107502594a903c014405440b0352540052140c1c2d00b4a00a44004109650f0f0001030041c84520350326039811402c031500c0a150004925865074460008071049035851901900040020031079400300040000c0c44030958034001e0484812031041e080450703a034069102c0080d0004014070100e00c07402c0101000c111448420f400c090f050050080140040320180d0380100009501c0f0b10b4616101c0e50043c01d003d48450708120030030301c1c00f410740c0c980c1407203d081d000c403200802c14205140300c5d007000c132095030280800c100f200380d031424245240003c4d510030f600f06078244036920300f0b010840c140000004488034244050050121455181090904a1003195200d038111041200c0c00e07845640070311504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 387619928 1250 387618678 387618703
    0xa030b071e050403020405160c02090603030f0d0e1c020703030f03181208070302090a1208070503071202070e0114190b0c0a2102030d0908071a04150501050f1908 71
    0x6a40f10b914500400003900c401405400501d8540a0026940385e80810266100e68058808071625201c02011170316610031403c128a0001020490b03c541640c66003190318813056800803038001880c02a02c01602045565101016921030202000000d010b80d01f207640340000d600700029040c409542c007c10040c00d00b1001c1b203801e03900d880a01342c6c03180c104010030740100340791604504201c00a004607003506098000c1c0c1d144035000c80800020011003100b1940c002c3d90100540b51030720813a29100b016a00000d0b10500075001d030710301c080b40c207601001205040350b101080181e01424142c1c1070092441c16080c108110402c0302101180e4060705200805610800400800102d556402c1c1843c1c4c0d061030810384611807284403500411b6950000c1035410000b80d21000190300000b07498507014a115240c0300416405204400100440003405030501c5140651942440c0328203180c1d815045030005d00446138003d07101d6403800c4003400e0101d10f03131080b0030011a610307610131b80341c442152810b850f25005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 387621178 1250 387619928 387619937
    0x120902030c06030c1201170a08030a021e04081009120806010908010c020c0f0d0f02100507020306040303140603060103201513051905030c01111f0c0207050109050a030b071e 76
    0x6000d00c5c500d001521401080c91000582080341012038564a4800a0201070710041002c00464100101d69045681c03240c917000e01400003941001907a0f00c640c01602c0348290600400c410700380034520501071894003035400500f00035944800d6509903860640030f0061410000800400308030300308244110814240705400a009109140d02000800b0480300b2415018156915082c0d0015080d882010030540c0e0494403903d40071041d44040f152405500e501035854031603101480249a0180c2c0180c3c1070024400307081c4425501c800c1030581c0d070b91081c40020000d41020713001c407a800d600780e1000b007092030000b03050002e180d0031640071500035080105980c90001c94000304000c10310700107841c901c03a20500c0620140417071400000031748442081c110303141400000d07070f0107041c0600c061015034400303c40b2502a00130001c0601c0a50010421807209001501c68900003041030f6000f0340040c0121076005108421940c11a62010815000a02180180b00011905145e138143c6900c000c0b9800d14242d44 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 387622428 1250 387621178 387621187
    0x30c15021305030309240c070b07030f0302070b01060e0303070b1617010b090904060f02030a06090b060f0f07052812050c19020a05040f1505010906120902030c06030c 73
    0x210704002429644658807944c400c10030b2240d2915640441d4004541c9010030405040040c0d607404298400c0c560b0f840358a0080c1000030400710820740207401d080d030081e5660780452041c0e071010b4040784900a03001d049404208010801580305002d086041340d0064252030421980396603041c2c2d4000280d0341280c090700801c04251080d5401030755076110551760f10417031710780d94035040301d111442c450191102e0003102c25500140174408950001c1c00f4050320900c00715074038034180044200605980c05504032540c2005082c2d4440c1c50701200f0b6034005040c0311503c1e40b405280416074581d9a010550468440c0200d0308c0740041f4100080ca054000280080d424280d6802450010303040718100307a0f0501404424011040401e10008032000307110254000700c224040b0358000181403208541c421a401400c2040001d034203060340e003010006240c56034250304030307d40380e80040d01d054000340501400616030b40000400041a904400d07941c50024040c3c4080744421000324039140e20440c1c1d100d030f142c0300015 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 387623678 1250 387622428 387622447
    0xa0b06060d09051f092307050604090213050121022104141510050628030f0e0105040203030319021c1b030902060d0c0212210a0c050313030c1502 64
    0x801c0300f010b81103840c1040081294590307404074001341305081a0b5242c0a105521b501c003044c2000315a01900b001000326403511750b40c1c8d00c00c201030760058402403c00c1000030710010f0a5406183c1c840e0340c0e80344034440104501e0406d41700c04001e4010007548030341c1b03002d00c0f16082e01805190364480d0180d40100000c1d0003c40744110410f280000c0c0c01401b48552040104001141c08041e001000f0344400700d81203503481030010000601000b80d4010b958060314804109581c554142d80115441000b071407092049150407081142211000c4130047c1d05500104009800510101c058502029902c0001810400e01c800302001c20704040107040e006561303c08244c5c040010b92000301680404603d42880000c21a074003048240c0614074240d6085038850303680d01c0c9401d0090006c0745805602d11011902c815107081d40b001c40c00c05100c0303460540d450100c003140d400c2402c0d0182540740c0c0e034036407542e41c80e5444401220615864110f0103404000c1e5002404001039100c0c0030803400740809410160b294003508 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 387624928 1250 387623678 387623713
    0x15030506010b07110f01030e010509010b030c03280f050304080105040b010506070c0303080a020417030d0e0d020c0d02010e040903031a0103090201172d010303021e0a0b06060d0905 79
    0x182c00c07204040700305000c040c00007060201c0306200c984c2c040d1a44460310901e2070050700606001210600c85500703180811031427000c154081911000128207d40e40710700304005154482451a02c000c400e01d28a0600310264400c443c0c8005225100b101c4c0640303951200e8850508607042074000410a944030b000303100c1442441340c105805401c08540303403843e0000ca6955240d165211748070003414807801c00300088603c1c44580c1640e0003040c40740d4a030a03010801161154803940500d0500c00b015160150803e80700000081391142d2441d660002c0c40081551401c008500c003460074105e040111540d6030030915142e0340101c1740901d2007901c01280d060b00541c41e40e00e01c0c800004445040500d440c04110140c0c0c1e100d03542c4400c203107070b41c008038502e512645510040016007801c50554a000b01880e80500351985c90654101d80c020344c262110b01032450700c00c050b280303170307285a0341040d81c04070345420003040ca94500c1982000340280342c3c910302899286080260713810014151070580041071080892000f1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 387626178 1250 387624928 387624931
    0x2060c040503030a0e0f040612150209010206070e130e030a0e01030213060c080408030708180405010b03010522060906030302010f050c030c371e051c06030615030506 73
    0x49518160619040201080c1d03203000b022500070401c0303444007801d80310b501c486562014100001c0c00600905e40c42d00031ba40d1032110f8500c4103c0f00450041240408000d0324800d41d07500480503805080ca81d101c0747d800300c1c1c3c01d54107203400b585c1c01801c007101a82886280c0c812000d6030440140030759101c10031490058800004907800606060041001741c61080c0c80c3c0401c04159042d5060050410b40e2500b0b000085000c0c40d007213203815110000d0388d40c040c0000400640408503943c200100066890010300040e92400c0c854020705000605c018400d40c03a00400e01001d14005a021002138244c05129005565095000381e000540d51242402419820300800603030b840064014002d90404051005061000401c60600d03001e02144d0100c0c1003c0000411703188204564106144092992441210740300018024000ca00d00d80200010031580d0041040c0e01680d64903441e04140b2145904544002070102c4036198542c1ca500101c0000e40c01c1c8162004406a0407240f00c18070708518045240500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 387627428 1250 387626178 387626191
    0x30f060f020a090509061818030c0604080304150b0105040b0702130c1e0e06181201050c090406060f0e100314040605040b01051914061b062406042c040302030a0206 72
    0x20581500100481c8400056030082300801d00c0b01c03e0220903810035400d5025485c6040c1d5980911014481402143c01c0507502480c0540c011200407040342c49003000301c40300d5412243c0894800e0104000190030030024111190014125500d94001c0d074a59004a0b0048244600440c9410700c003401c01c44101062488a4000c90a14070070181c80180041c4090065940220442d41c182d442c0c51404d845520300c401e83d1503d984024426424046040c0609402110401d030280d031801350000780b401e104080f0b03440e1841c820307110804007a840405016201d403081c481142419100c2251925000108004e644620b0090200007182e09246ca0104c070320141c1070344464894690141d41c0e400c09400000900121904901e005441082c402d02040309405048803000e0108900b0004c040d0b980c00100f0a1032160300c10110074020900c07107080000049003c402e809030020b030140414031046400701007c145181201e0250941044c0d24001d5140200080fa001c50040e000810180d0000c1c0d01044059040070307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 387628678 1250 387627428 387627439
    0x60509010f0c081506070c170d0504030201230903030406352a030705070303060506030c0702090907080a050a21121a04061715060a030f060f020a09050906 68
    0x51510b01c001c1c44010b0103042c00003000d00c0d08258036007665400c01180c009680c001102020a661044510403901961482c1100c070700418080d045400d119008580549a05841d581c0000200810400072618400d0b00c0100c1a8820000c05c1c0d0343d42d07400c2000d132006102e15910245840443c001c01904000e04a00d02825110500400c54000e030311003d1059005030403660041c084600d6620190810f0f460382041908020300100f0300051304e520000405040d406902c0038410141d4070070030b1000500c0211840e00c107409092011000501c0e1064005404c03010383d00854410355180c2c030800d81003c484901c00c64855000d00400da080007102128a206d90402c081d046444004d004005400080304601c10b001c0c4640c0e4002c03c03440001c015200c1a220704020307000f0000d5039140c03120a40310034a4000d07018040d01c60a0b00214008102c43c004601c1450003409002c45030345980e13920500409003e1045840300d407681c031084051002407019002d0740180f980c4240f9034a02c0d240603c625034001510950258 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 387629928 1250 387628678 387628691
    0xf09090f0c080d0315151d04090b010302040e12030a0218310e06040609030c1203022502060a08041a150f06031e06030a0209090c0301060b0c25080307060509010f 71
    0x5440130840ca040941c5509010301c2d01c2c0c018021144921f080a401164410f15022190052144109040781624403d643c00c01042c2889003400d692801800002002c40c142040000c81640c46500034004c14102010b46a1011100000280c0c110202284160300c01143c0407030782501509012190030203c644000402c520b154802d880380e2100700c010000780034991504032403410103100e0214101113980001b02400e080d115440c0040295200c22050302c121b000d132607c40c00300c90443c500008402907000304050302e002a00d800c1075a82e900c00034070540d0002c444240328a080e042d00c01c8110320644c030640208590205c13038010011080d58505417980100c10070700c1001400042001961003500b062055194142e0b541400030b86854082e000003500071b44290140303c880d15002032910a540700884c000c0c40362a480c0c0218108034041e1880005589e030203d59543c0e5441000486600e0b20000d0030f0000b86460b44905049242da030200d9030460f01c03207665004011141c9000c0c07140740030800388a90700340b002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 387631178 1250 387629928 387629939
    0x3010305070909210e0306071b06050a150308040623030402040902040e0111030103020f010c0510020a0c0c08030910030b0d02010522120512040f09090f0c080d0315 72
    0x100e01540c0903800c1d2003950751140e9402d10098030807185800a000b00001321800e0b1000700184034001c2a01211301900c5520301044a16004100c40c0c00d05103120f0202400c05000c031f84881010b00030103003181030b041c2d030b440d008100d807001c0601080d00614010015242c3d1245800c10080503054200c803001d80c207400c0351240c441c40c030006104a0f41c12035011200456400f4031400000e00070911691440304640c601106129400d00352409107040740e0080fa0441249a41c2d00d0040d18143d614080c010030680000c01c000c18441c45650241914054525000100c0541071382c4002c8443e106412010340b645c0082a43ca18900c0d1003078400420307003810b1900340300895000000c200315108a100080c1440804502404038074164400d620707500741e440d8940042d6541d10882d0004e084142d000549207401141c0042d0404a600b100301c4081b21820690900c150745403244280c000e2149800031510285000b90020118601c20035400150001d0b1000e0042003200b940c0180032101c00e46014204803001c020100f05 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 387632428 1250 387631178 387631183
    0x60305030c1c09090905280512120708090712080414120d052d19050304030c200307030b07111f0207030516080702010f02191217151503010305 63
    0x4540c80f607600805c07100c085280503810f1802401102007160304c0002c2c07071070340348103415000040e15000303038181d1315802420380c101041c0c1e02c50761074080744004c0e8142c0454042d904c80c0d4901a03201e20703c00182e80c001070300c840010210f034140b404181e5050034081024032408805507132100d4036803401c49500b0400e03101d48801a4450381c0400100040c080041840502020754042050106100f0380c003443c40d070010580002c140d03822055005030501211840024000d016104413405540c0545441148601741c1d6070b0200c0610450102404011902c018400e80b80c50030007100e005144103a400c0c0300d4900c0d01d01d1008040c2c0c0311547c0032440701c3d401400c03454214940d002d07429802a96014025039144c0403070805942c11320900703143d0521880e410198205001101300680002e9100340e90b42c007060403851404980d5400000103820041e00b1850f003020005410300291580c1d40e20703c0c01d01d01800760380c161580c0026071044400701b01c03c4001c3c2082d01481d15003805144842c6020561305410b55046450306035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 387633678 1250 387632428 387632447
    0xd0903080a0509030a050a1b18020f0405030d021b0d020607080f040f1503050c190c020423040b01050904050d0e06040302040203090a020f120a060b1201060305030c1c 73
    0x906a000c0014280545403045080310719032240601214107150072450001da4400d9803490a07540b0400141d045d810041e00c2d00c2d24101110708601c0050719600420100c00002d42c40b081700340407030034410000042c450300e041c04034100c0400c240d005460b0810240c240d00600d4080c1c0a40070340700c0c0340941d210900580d61801070310380c21500103820644501d49480382d4040c80c1b0542d003105180b06054040000c1c1c8001c0e50b2032040c0540d030a69000d03c050b44420318074010038020112750b03a81c50081d2942011940c0d101d0b101002079070740018000300d4110122142c564003e40c1c5184a403034607a0000d0708020501070540340e042e0060000344c6080781c4900c0c02d605c40c29202d40400c0050030412044090114071503550505031005103030001c7c0211340c0d906101003007603600c003220303001240140e1902107003902e1890110758548000c0c1041002c2d0403503a6440c1d4650004100703401040e58800b181c1d42d5880c4403440c09210b000f0240d071041c0d001350313540c4c1100100c4614000810018a40e20040d0b10110000503a00507c2003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 387634928 1250 387633678 387633683
    0x120618060611030f031807030506091b060906030907030816110d0b06090c0409050c0901020607030903140f0c06040b1e04020102120306060705010f060501030c0806092d01090207030f020d0903 84
    0x840d16034a60981c0070301c4071b10038000d490030984101d03040401442000316030180103031880c41c100c0740744c421a0030b06e62002c3c4440412440c2c0c040d2080c8018041c03801d00ca0000d640c080743d01c0f4103650b0050b480790b0320360100d50003a86402d4a001560003880b4104035080c001c1d4a0b954004a81500866500d540c418550f0303103008001c0c9004a44c50004a500c0902d15403c1d00c1c05001140420300071490205410030380c0d07030091061240140300300008980c0c4a8001e118840d40340c0d4240e038400b0401102c507030100081d54060140c91214501c1005003611003202030000c40e000310b1150b146081182461200c1ca0b130407140400c0c0c8180090804028440144e0700050803a02c40010300a9440d140e0351100c0008810b070240f448040c10f50350030400030131500b4010341e1102082c0c40c000d032000c20041c1d810800466a0764021241c59800040280120310321800019030b03100380010041e050342091400055040d1076541c04e034802441039401280041c109604120074407050344440c4014201c0d5001c660005201e2070051001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 387636178 1250 387634928 387634957
    0x1050904020613080a08090f0105030f0406020a0c0804031412160b04140114070f2a05030405030d03021e07031209030210180c09151512061806061103 66
    0x30a1107110303443c54032100a0105a054800750030a07802e258020b5404003481c0c6201d45080b2150016945c001da0640e40076030303070908a41c02981c1d90750340e070301000f58401d100340c105000882c104440010295170040002c1c1d4419840a0780b0203038403003030851814112800c0c81c003080310f040c060846800d103d110000005030700590185540c1d21141400c1d0301c0e10000f002203544035420200c142c0121240c5401c80d030700402c0305640346c00c03903405100b0003111680385404072114180c1d0418030507421350340d2282007141300901400a9a19042c1e075000081d20309151502101c02080d0007003080c210304500c403140b8403442d0b03500d41962480c0003556640104802a43d41c504601e050791806002c2c18180708015083e03580c0d5505008201040e1130341c40f401d02c4c160a0350011640d022261344042645d070030601a80d1011290318842d80c540c50b0600f8103244640e41920040402c20034001104e04032400d1034010310008107000c00e50120040b074034200b031070191a903580280c402c1c0320503424031402c58100001140c3d001c4068140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 387637428 1250 387636178 387636187
    0x10081b040609020301120b010e09030d151223030708091011030c032206140a03150e01051309081b030c030406081e060102060103030f050d0c0e0103060501020303010509040206 77
    0x580144420b4200406407803020002203024042d000d01c0c40c84107401105a030b0060fa0340d03a02042082c0a00322121000f540092048403c0c1c14130a4019414201a40d815180e80c15141c44514840c0b00b1010b10641715401c9111550f445011200c020f10010b1206c070740039614101468940003001d101d0300f540381d8002d8280000c02c010b0140304000fa64001412001660780d280c441c001e6040d600d03004144200e03c0c0f400801c0b0400054444070710204120f4030b40d900d840c58418400322501d0240e8200504400502d85c6500d00d50141b80c03061505072003d40321615029200b5414841400402e40112107907060052504903090013003540d0701c1c00d0b01d0f070340e90316050039041885442c0c404c9820341c095070840c400148404117003c101281c0003408203116206a8890b1440b0720810b0700d290304202c0080d1900c90151700610014800311307101d09118240740206090542c0b40072206031018080307804208018001400045c2038a0b882d40e4075001d0800103003800d10017035040d0b504210000e00b0110f0041d0000384500310024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 387638678 1250 387637428 387637483
    0x30311070f1403010f090b010501090611100506060c19030806010804030801051302070c0b03010302012d0e0d140703020109090c05040513110a080103120305011409041b03060e061008 80
    0x40005e600d00b50021020700070000c451038020081030080c01a2800300d480b405010460354412254003003880c103070300020029040c145103420000c04010388180e030450010000307549800740421000788031120181e000311008540d0b007030007001e40a0240c00e150400c00001c1c1400003281e404940c00c1d041d6801120140f14080580e040c6d40020310440000420107040f100d030001c0c039010740320055812a4001e0322015801b07543c803140710740d4070142c0c8030012112030b40181c038005000740b08421081000b18003500d03400740d14485032610b10002c005128028041d500c410424011547d0007048007004000c040418050f1102440c4060b107a40070f00d000c6c1074081c080c070466949203108240c00600751300320b00020003682d0b103100800051030b400090000b610411207a444410306503200344a8079040f5009042013a483c0c03800001003026400c4050010703150100c2c0c406407010440b6035983c000c4000c1d0320940c0001000311807907201500b0100300400040d45500303010020407030005c000c5000070a1513044c503407914040a058 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 387639928 1250 387638678 387638681
    0x70807090801151406040302030a0f15020712030e060709060806031c09091b080109020306150f0901021515120708060109020408060906041707140307080301030311070f140301 77
    0x70303404a1555800d0060f903900801a407500d40302036800c0603d00d040701446140a01c0110f11803031000a40607800820070001040602000e54885c030b100c1c0d4003100000303001720302440990704590380540d40d2940601c1c07500d0b0701e140c00d40b0584000100c404068549032504900c003904400c6140f003018140404200002c185607420302c0302c01c81900440700c801041000c491001014008a40112002c07503150000c07c1c0003002c240194088040d99650758400180e0902a0703402c06504043c05440e0002124a1031031004005040030b829081d03402c40c10980c403001d048000a117021034005003101084078080038401c0d4031803415044e403410401661591003060f000c81c90a46084110f80c0316181500880e00085040d00c2d0039001042140c1c4900300300d664030b80b03400301101e032100d00a0300c0003041c0580190b4144c10000c1c180000d4552140281602508408880601402c5902c15a811a00c00d0000001802015001052942c1a8505600800c9401c0c2800c1590340f0700441d5019500120302e5640ca0f488180d5400d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 387641178 1250 387639928 387639947
    0x60105070203120d0606180b0301150c06092006030925030501050f240108070f02150f01080d080403020307060207020f062b0c120923030d0c0314070807 67
    0x1000c0030659440c0504e00000051070305006001c0040c82000301640f401442d034055800384d42106a106145903c0c0003c00c02020b00440440e04c213020309d02e007645c4082200c03446100c155502807a1503100495150300200420807100441c0c074460281801800420880015a4500b4080c070381c00c07464070b201100c2c503600140d172499031000f8051341c2014100640d8420076070782240241e80c18600d00e00210713440c80d640c1e80d001c21301218882c0012054400260070030720172498860440c0450040e04d40d90140c8074600c03c142c0c40122500100349088000400510740104071181c4125100c3c60b010346107040544d0025101c0c07041200140c045500422428207542d51500d03600e0b00884000c001c00d40d5111413260804444000201c49c0e00601d94007894100b400c006401003a01b13080399a0303a43e00c090040103040300018100707107000f500d4400c000108038007102d58202c0c8039507030240014011a21036001c2000c0a0030360f9000c086410030542888210003283c010f81c000c050700420241826503040c4d89010085640030031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 387642428 1250 387641178 387641203
    0x3210a1107082506080f1f0b0702030f010c02060a24080109020102160f2309041a070c03050405040c2c030f0606030d120b060a0306260303060105070203 67
    0x840c0d90009614100140002081580112140081e040140d650783c03004400c3c400d070f0000c6504140000c4101000c016a1a481540d0070f100003500f8002803040b0349540b919405c010301666000900d0700c10340c5001c0102180f02c84e8284001d10040c006664000c0d15147e001d4003100c01e1540304e81c03140c0ca507810302a1070100d50325442c15800741810303510320341d25000c2c1c101004240d000d0300403107094040e1000506040d00690b0b4949490002c21440d0a1090145a100680d40030800c408004054030603590824454040e60044500d80301d145040c1c840d0544842d00588494284400c0c0c0c815500080c2d040f01c1a942281d108550010b4036002102060780c150312045805480c003000c1303c3c41d144903244003200b43c20603460181e044800c441c1c243e59110380d0f603031010b42e01640e00d644202000c14001c0d1160512843c410441500480c1021442c004541030b90440000400403d403500d10501c580d0409a02240080746014100402214280b222548030711000d08031504024000400c80190344040102c1864102c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 387643678 1250 387642428 387642433
    0x4050709051507061e0509010603120f0219110112050609270a0606170c090a09050708030301080a060e062802070804030b1b0304030e04050726060f03210a11 69
    0x18031100303a104461103070080f1700f40301d281c880070404903c014400c0d40280d80c0d000d17141141c1e501084a080d02c41c592031412480443c0304480321507003064010403100c1c07082d502c100c103082c0d0b80c0070f003140c000b40030110f6400c540b6001c1460003007080303a82d43e1444481c0341c022407031000c1011400261a0282c280c0007011b05800103901c00d0605440401070f0b55406681220060002c001080000e0301411f5121802d00410580c00468ac8001c01c1c400344a55010715480361150b0102e0301c0d295520b186641c1140c0007640140102c8d003201c006881404080c3c0070f4a41c0c1c02404c00068490751400002c8001e00503d42c00340c001c0e0b60707000301d40d403115032a106604403900180c1050a26481e682e5a140860408904803000c02e459480e14031140030b44d040040540307000317541c95141d035026119400e05000003000d004002d0010020100c2404102404415511074011082440780d4000c0c507220081c030040d03120800d0824000d07405403d280c18414120340d91030361502508100c00d60b581c00c80240844200d00c250302400c0060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 387644928 1250 387643678 387643691
    0x607210f140402040605060c1b030a02030d080703150b1c0b0301060801090606141e01030b0409080a020706021f0e011b02060115030b0d022403090d08060405070905150706 75
    0x100380c2040d0340d10543c4200c60511400340c0310404d200ca540100507014006034466a014080743c3c41e400406824101c0203000c688c1d8a400b02d8000070303c0c0079060280500810150f0041c04071040d4580920146c864481d080100050700c1c0081485c1988205902d120064a5055160a04c01c60030341141c0039107000100284a03242c1c071090700c036008040021049405c03038039000000681c0c046800100000c18001456804040c1028a40602c1e500c0c000040fa410103a036102d40c04001c0d030346c5110b1109045c0c0075809050f210302003040043e02c0c045180e003050042d50701980c030b50f4a0581c04039072440c2e011540c122010518400662a060250002061902c410917a0b0b1020120150f030008002e03040303501aa17604040c1c10b103040404d0f41121040b004441d005079221220f040542008203a001110241130f0404210b543c000750120341d0341c0c00585212140d41c0000500f400d40607803010800f50000f0044130304102c00e041048018180103624030805c1e0141610780144900c99503883e0517555220b810001c2407220 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 387646178 1250 387644928 387644951
    0x31005010f0807080705030a020d11090a020c0114150d02010c020604060302030403170106020c0108070e090f0711010b0a120f1b0f140306060402030c130e090f0607210f 74
    0xa922039014580d4240315140001500d0301300080c040e8216007028001d403800103031580a002c03803141105070945102000c4881183d160726154100703840b40d180c8120060b2140c00c000420307801d5500d40308000c000f6560a00c14484005032031030182601c2d010803112800101410320050310b41858604001c1e501c25804180003415a070507070002d40c4100e110f62380302001f41d1290040c03030459070000e000d6a80141d01000880c4002d501510b1000c0d0401414200f000355420b9000024440c0101260b11124414589003400202500080d10403420080300c3c0c000c0c0a05e202023404505102c07210710500c9001c05110361035a0501c2200003d810459801c142082081e184800d01403a064070305125400c4485000d420018483c4a40c608051407194010040d20598480d041004007039000a007030544000001c101980b40b200812220100030321803015a1050340c0341c04c2c00b0241c00d01c0c110031101001c9800c00402c200d0342b40c0e4003c41c1d22030030469800c0c441013032180c207048000040200b02c481203034851400454600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 387647428 1250 387646178 387646199
    0x90c030a11010e010206010b0f2811070515160c0b12070801050916120204210219051503070e09130c05010315090e0c0414070e09042003100501 63
    0x10500820380f00c0d411100a07200049a0301c030003d116100641e1024042c0210742d0909400402c42012101c11818400503502441c1201d0360110681c00c011402103110101c0001d8140117510040c00708403040040e400150364507410500c2140007090b132a482e0300010b003040240310031400c005041c07032005c0c039a00d4103401803425003c150199201c4000ca210034000240c545041da0301c5030b00c601e042c54041041e08410040a5071440d0440c1175a84260b6009d01c0f000c104d0b0b00d008114042040d410106408146d82c9900500c5120499094180b02010309803074240704a4503885521031611011364011680c039911503104444070606010720300d038410840018089418150342184050501817504861019520001503049504464400c400011688420010101194884e0010074250700279a452284003e001408aa03040d441000c506a0803c040c0000c49500540302e40214800b503501002d103007000c0c4c40740743c01c5001c00010030701c02001c1100707803e085031014064001c1c003901e9240e0512465031201103965 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 387648678 1250 387647428 387647453
    0x20f07061d061314010501030819021509010f061e0e070302090901030804080d030b0a060f0908061602070902070512030406020d06030305030108010c091a030907031709010914030606040203090c030a 87
    0x440e03c4134248908002000180308441c1280e5020300e03c94500a0344601e02d050240c0001140707803c4d80116080d4200c039100074022144a41504400010316140100c00c4c40c00f04c0707655401104120f20f0100c0c40e01c02c5a50015900d00075208040c5100728a45d0702d01d10118040e02c1107141d055048500c05000004001d07210000e4401c0d00d84400c01e403088008140c50490442c3d0302c00c0d1520b80d12084c20707002004035501941512a41c00194a004a041c0c0e440e0903050346005800d642c104640c0001041c081c1030309034188801006402004002d41c505903282d11842d80d10129590325100448001001c40c040104c03a50483d94a5088100207105465076401c019085410074881c800c06542851030b00c0005a104255200550f8940c214421000d48001440710746600001c0c03c02c54035214110001c404202e04182d00c9075422518a22680d403030784014001064030f181030b4011084026042041c2c4d40e544d8000c035145a20540075500184c80b42e1302c00c0401490300010021071344e094001c0c044a01d051064100c03051 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 387649928 1250 387648678 387648683
    0x121203050408191e020c0f0909031209030306011701030b010e0711151b12161812050712120e011e0903140f030301030308040c09050f1009020f07061d0613 68
    0x800410954903016a140c0580c10720407980001c00c001860703d41d08d4030b0310781c0d00c0d08040071108882c20200e82510040741100195080003941d40301001300101981c0c01400a640700e29500034980f02549540d44450000d0010702500f42d034010340070005106a4810382d8030154446909084400070215541204d43d13003181501d900c801d80c1c01c034a00741c03990103080d807048600b00c024010482d0107654030360071f140ea09213100100c050b08000c2028020310b0035582240031440030340380441081b41c14800700c2c9841482d24000ba408984a0120140041d001c2801040310031003240c2141015402040c6160041701e228807069420844c40014060b00c1c007486620441c2902030b0f13446050003940640c480c0382c020340e85494400c0075142c9917000f007005000080c4140b0706660414411401ca055070f60f140c590903029a801202c800840080071402c00101c00001c00d003010042400030030451801c19844030400c054400c040c0c01901850b2900000409200c24220850000a68600fa030b039603030510018805400e040118103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 387651178 1250 387649928 387649967
    0xf0e06030112050f1c1107091b09050d020901050d020a0e07051321120311070b04062a21060602030901170601080a0e031201030308060a12120305040819 67
    0x5002445900203110429120517880500348203803007000894071101e800401640c280a0010001440c60003801000b11802c9450400203460300d005e100201018181d5100c248035040c181301d44805038465070b06003410f4820036550505041100d0002c5036039030320389034891144070303030b14508003c0b04660040c09480c69121044500000070755805006c0026451b40320128180d0703003680d20b40d4000030750000c1d20781c20000c030a0501054150300e007011059181c1101c0c009680031280e000400c07041000c1449840c0d500d0011041018804090340000002c00310389282038010701542d02810117141c400081c51b0010560701d0701052180544030b080007512904858a81c502250002660046107041c1d01540c0d485140107a4818a07240d403100e1002d4084c140d24081d408050008000c4459030b0402c4848540c06035009884d9030076036007401d02c1489003020703159100854241034040c0807000640341600703031285a04146000306280d181c600300380c0c00c640304401400d5189040e80c40c41101d19a0002e00700018100c1c030020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 387652428 1250 387651178 387651193
    0x17131b080f210a09030f111003051302010e04090f1a100311010302090105040b0a020c120703020303180118141003060608040f1104060e15010509030d0f0e0603011205 73
    0x401c0341d5030031074038a03400385426040c1c07901e01e90701c040c03403018261032101d5161040d11107569485980001c0703640181904c0c500310341001100c0d5820824500610242103203000c102c145088100030860000142c002070401c42200c3c8080865661500085402c582106125200b61400e1a05c0d030051070ba00d64803041e291040f4000943d0551404002000301d0742c1003419151400702810044000350b0083c481e9138103000052102190314411070014007400c50041c0c000b03207001a502c038104005210300404400003944000780600c01a1008815112144c1040d41c0c50400c0501c032200695814008280d00c0220407004040020303482e10306902d10002c401c060b0382000c0385010300342d411400e803010380c0591404504520081000200480d151f10700e800d02561000340c40e10b5040000409070703045980604014916582408040342c028445034200340030900f08140b40c81841d40100752a0344840a0040c1408600c1c3d90000c20796020b04011070300300d50004c040700e82da50f0f1203c20701400850707030003025a001d105840 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 387653678 1250 387652428 387652453
    0x61204110d15110715050709171f0605040c020703030f170705160804090630021c05030d021b0109030e060c070f080a0209070203090117131b08 63
    0x41c10105000d4100030800451000d84091030007600d1000090151840e08002040214804114105142003c0c1e41c0c00705041c04c001da40284070b6480c5402c052641061322921000c404800540004c1441e04009844400702440850000900c81a80103a070024100110440c3d5281e01003044000d82e8829142e608403100504000c50f183c0200d4005d1040c01e00100020840da580140d01601040e080101a644001115070300c00c0c0207034101c2d038048440b19440b00030902c0707071620420301201c0a100a68043d515000740920941c0c0020860781e010303000b039050000c841d1030752071540c00c918010360300700d021241d951400c0078200000354012400e0418204e170b04001141158010f004246590b44c165841e82e40c1c0700801401c00140707500540003a2002d210b4404001054101041c12400414850004d05520320300e81c0140305916100801e500c0854200b0407000000d607030441107101491024800d111065598440320550120f220900907080c100f903038040c0400a00d40702040c1041c1c1d00800241c404001491 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 387654928 1250 387653678 387653689
    0x1e0f0d0204151d090411040e06430212071104110901080a180519060c090f14152d070206030a020904060e0108030408070609150e0301020906120411 65
    0x20800b02d2140d24200c640b0004604d0011086a0864045c01d104000c000344180084c0c104c40320707801c044109401000800000c002d40a15000816015000442c00740402c48041c030f21500d009001c10480c007130fa49a05440c070ba48200482001c041440c003130035955070303200d082c00f002c3d0612450f40d540c4140e0070648804024040001603c6400c00182c503081503036100c5d2440c010103400c18030322900310076061619202c0071640c208075811110742e504100f0610406582070000030348030a0341596040c007050540400400c4560b0030881c3c200c59014041c1858401084002420489020a4030242140100300c8a0091a82a480700d9090600c0301000e40c45031001c00340c40300103005240c5d01079404030090000400008541d001850044401440000c00c41e40729000c0042442085c3c0050015600202c1d09000e204400c110042c080c1c4000d00305542e40307a25000300b40402c240c1440b201000c005440d111001c50f0388003501a1546d00030001e01203600c074240b0054003000310000711010307100f0361f0240d00c5102c81410311 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 387656178 1250 387654928 387654947
    0x3070c0e190e03031302040b0d0c030b0601030b28090e0606011d031009050106080d02030c0123010306020703090812090315040f08070c05040515010809070b1e0f0d020415 75
    0x400c01941c03c640d62480170000071813915205030b810545640e84c226507a40da0181549480f8410600c0c1c08640d030550508050b00c1d54002d0406050603c1d08035501d0030b03543d8030300801c1c41124016640c0c0c090400c5206c0318803150055980008100b50628a038001240000b20f2603500c070304001c0c0d07100c401034409402c0e8004100c0c00c8500041d00742d00460101c40710503110703030407a01450b400b910010645d0b0340d541981d10b103010145801c040042e0000304030700c2400803003805128600c4007006805010081c00c144034000d02601848020240c030760000c4ca450415001d040c0980050180300155406071001840a904a03401100607920900558a00440c90001c801499000329000180c03c1a00c0b211683e81c49580e03844907000790303030b8100c0c54040050559194020303140b14003c81d44180c244e0403000c40c00035004890151804240b50483d90b000e102010065064403c0d5034017150300407c01c2152040040030b9841001c0418090810000f00501c8a040f9600141304441c01d102d0010f0301c803081d80340c0c1104c40120 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 387657428 1250 387656178 387656201
    0x1206020720270c0d1d01140f04050d1101090f03053402061b01150905010509090d0f03090b040c1403030a051207120f0e0607020d05031803070c0e19 65
    0xb4944003148a15801c103000d40b0b0341d099803080002d00780c0c800310185e881c1c00d802c9080024580c0e4540303451014807500e0b0000303560090074864003180075050a0f036500f0b032030b0140081c42408110031151a0342e030310300007500469002604000d0305020102e8901b0024010b50003140c041a6000922402483e22808c015441d6071081090300c1d42021541d15a00b00601544209180a8411080d88064440550a101c0c0e0604182e07007070300b90403500d0700c3c0031b10000a45005a00c0b981c8207159810801c0000e2101003040c0c03140d00201d03d0000880d00e0821030603001080040406042906480704000c20080c01c441443c080d00c0001203d11402d4050104040c0e5174424454141c0000c0d00c2440080c0c0e40c080d54034182a0400c14500303081d102510001650411aa1a901716550b525150210003050380c400f440140e8001c916440500744200c000c00000d00907100c0900400003407000070300d2404a000b41071080e100321a40c8001440b150030781e9142c08041007002600d040d10320a40e10041d2144e0381466200b0300320740d1007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 387658678 1250 387657428 387657499
    0x10020105041b0501020a1101091d0103020103060506070201081323030c0c0a0b0a0315170a0210020105070e0f0301020708210709030c060807030e0f0124030c1206020720 74
    0x982030b03603540b00d04547d80000f580c103120403000c0100b0b011010361303008859100040a101559032442c000141521490b03407105025400420174000540d03480710105a000c5071582ea40a094103181c0f404826005840c1c16580e103043e01d8149021000d0000320080a04490b01d40c103d410620a040410a00c00200e10a01614420400c01c040145010750000842d0b100300054282d40c080d91240f41e507421121b200040c0d449038000795514421898914011030700141944020021450401c80207040352961101c143d00c14000000c00441d43da900350100d40708103502603001625151760520031411586001c1c0c0e9030340c030200003a000801c01c40c0f04291640450f80c01a00c1802801c4c034146054400395005012501096141d000001ea405401c00031f4480840c210000014400c8a00c0c815480303925049040041c41c480261040010030141e10f000c0b002d6072803c1a4a030201d00a40c0740c940020b124807400100403690824101003904005e09214242400607107103841401c0c1031000d8120f130f69400d0b8207a07100c0300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 387659928 1250 387658678 387658693
    0x702010212130e0c210702030c0d120e070e0114030705040204091d1b060903160605031005091303080c160503030604060b0c1015050402041e1703070b0a0b10020105041b050102 77
    0x105d260502c003541180e168010b9078540110301d05854200403a14160f040890358404000d14000024484e18100d1201403000e81882e0b42008129801c000040c4188103032191031088648481d030742480031100411004004540e5903640f1600e60005d0100c44889013040050030464a0205101003450404400e480000200401c04401008525000700410301d8140c072070900c8803908401e0344034200018041e142c071019181d18005440b4500c150040d0072040c0100c003400e09020045e850001105c05056040c01d00340055a11400c0120090165000070340d480c2c1c0003102450700380306010000f18090710050324240301c041e4440150424602c507a030040c2d00150711480311a912a46035030701900e40010000c10101c1015940c000142c10303a046070308038029601c402c01003c0c1030200c41c5103248004088100444004986480c4c149840303000300701e80940407282c43c000248040100364010041c081c8020450035a041c1f001c18000e0007000e04031f404a41c01910f845217106443d0840960310304503a4141c0c003c2801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 387661178 1250 387659928 387659977
    0x10050a0810020708040905190c02070f0b030c3f061828060e0603120415030209131407051804090f05150702150c0f0702010212130e0c 59
    0x2903024400035620f004c030a01c070110341c03900d41b409100d000d407030785140c1c2401c0c7c240281c031030b581101c90101a203029988000020482c20941c0d880d2002103d488039001c680366502c100001d0703010320641c1800d0354084084e1048040c0d6412407000310101030f00c20591800e00d40e12418144070080401d81300d1940c4213854030b01800100824072262940841841403405203003841082d82400c1e615004050b501c0c2c0c81c0c44007018004441440702e00c0c3d034011000c0b8000c060311590148021030b10b110303500568180000c0c0b0b82812203035500030b4040720758a0001409031100210f40003102802800000d6591020740c09000108408900c00c0040e500c0112640c4441840140014100802040960380031111140902050004070380244240c14001110910402282c03401301002814054184010230305082140144111200c81c04192661040c00c695840e513142d000b400142e01c0c0c5000994001104c2d40005a9080e051100001c801c0449181c038401c00b07019298414280c081d40510000c1403d40e4a0081c5407240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 387662428 1250 387661178 387661181
    0x31905040614090102070f1805160e1c02061215031f090606030803011412030313031115011e050117040f03091505210f06090711031210050a0810 64
    0x340c60f00c050040791165540d4620b0740d0004240e80d4441d82d10400041a02000b8a00303a0140c55484400015010082008804d0282141580c807407a28010a0903804540d5a81060b11000c503442d50011b2400e03490701410040240f0120088404604151040d01000601c0c1000102e03a00c180c6d0058402c0c048004040340760a00800c000d460036900251a0100000404c65000003540030301510084101110850424800e61403c41c28004c0741941c010400c0103944010b1200e131310811545460840c00c10306200e4505460019041c03903c0940300c420100000704850b03a040710000314104c00800f141242e0b95100107441c0825021716140c102010040080c1c00104500090b002c0d881c401d0800d40f58141d114821003121454817040c0070b010950014840340c1410080d02148404105062054000c1c40c00b00400f0a0581c5d014040500802103a000308030014040c841d00622901d504c4112038842c803240300f5290750018185e0300c504916040c03c1d00410181000c3d541c4c0380603a20190020429070b04900000300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 387663678 1250 387662428 387662437
    0x3020909031c0605150a0806040518011407020d14250c060801031502160210020f0f0604150e030a05090f06032805091203060f03010905031905040614 66
    0x540d600082000004030041c06150250100b00d40d8000a1081e0506050100003640160b155501200521000b0803096000440d103900550603603000c20705484281800c925110315880da10388035424100b5010b0007041c0c009000c1c0c8914116401c54154900660059640c0081c42c1e6142002100801031081c1e00300d501c0c002d1101c080f8809041c6100140e80d03488803a80111190041d01c0001c842e100100107000490200050b50444078108504d00140c85a02c44565421500024090780c0d901001144142c028040401400e42240642c0c0b601216a180b040d10344d0001c98046402440d001c9102d8030400f10780c8259007541e82c642000b1450800012030648107604546005584074143e400c0d0010705441d5507020b540129500518008100c0c0d042c021361646a40301c046201e4460301c0c000800000282c0028040c5200ba41c00003801e980b07458000102d020368001400c40c0340c140d0701b013a00041c10008004024800b41041c41130740d489190000c00101c0b0b9a21131841303150002604000e08244d111018130090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 387664928 1250 387663678 387663691
    0x170721140a08030708040c050103150e1009060f03031709030301171603030306090b0f03060106050d060803040e04030f0915080601020f10020903010624050717070b04150902010801030209 82
    0x98406001aa40700410b03a0720403645040014103040c18042000990150100a000c09080521007685001d5106c0c148c095148140100d00c00c0c1c00700800c00a0003a16890300c0a0018042d081c4a5543c50354110010002d05110840001c0c550103003c000c10040e10b0b48031030080c100607024519591802c460f0900c0503070021000b0300103010740000c1c1c002c0c20f04403c40341e200a5110780c90200d581c0349040210001c9030001c114681c01003200c81c5001c6070a50b40410201c0c103503049403d1060319410140d154400421058002c6034141c800002e010071400f8001d09800e1244e80b00e039658100c52100c001c021140c0d1520340c800d000c43c040e075400d14000c0d0540103403440d40e400b41c018412280382c000161246071070503207100803003541c0d02d0380043da8640500742800340c0780140c41c1c0c0c1c2c404498080303280d26820022595130400f800800c85d01040480810106444082003013461400d03298a440d81410f14081c00700c1c0644041f41c2d0140d40707002e0016065090b010750700c84c1c0c940584950307410740c2c80c64084c0840010001c025 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 387666178 1250 387664928 387664933
    0x80703050d021809070c03020607050313150b10170a0b060c0109060605150c1507021903050a1209050a060903030b041406100306210501090c17072114 66
    0x3401c0d00e01c40b071015001040d900341516580e00c0102e4180311101c03002504050030400d4000381400802c3e0002211500300840307242a65980c0e88028003c1c24403a25000c00600016280c0600940d0052540140d02a80000c481c0c0803101070080c4415510380320029240c014210440b000a800380d0229800302d688010003405080c0b412420381082421a407030b000b02140d016130b8070042400f032814804001100e8120720740010b8580302d9803240c00781e5070300e4103d01e0382442c088166000400c5588240004000c440035a12540d15034001d500e005815500b04c00134140000b00180701800307214501c0d0160740b00013034124002e0040d51741c09803110009091210402c3e010316454803c181c0003601c40741301d500386400c255140b405803828001e0070000a605820082010542800018411401110040803a0801070408000b030142c083c0750460150045030005400b105803640005440050341c0907810540400c80c0c16518110386908a442c9820460452016a4940c00300140d00041e1412280d03404200c00c0400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 387667428 1250 387666178 387666187
    0x1608010509010b19060503090a0b0f0a06082802130204170c06070c03060902011e11100b1c150516030c020a0302060a022b021b010605090703050a140109150b030f0408070305 76
    0x64004044ad0180c80d820160043d003000c024032241c0c20b10401c400342008038054840d000080b542229403c408103450454101c07072000350805c550b261007004008082114056456960b21101107840c1e1380031070007034126405020100c480d05d00d044811500ca150340018104440c9003591202d600074942184200d0510040503201c2132230750428082d1000910b15580d035102c004182140da24141104034680c20380560500c0400c01d0581e5410a19110724032480d1140505409542001440510b00a0103c0c803031340e00d050144005400c101ca0700c18903038492a1004c0c0900809c0383c0301240d0300e01d58200c003d80103030044008038003a00f416400401c020315804c4002c00c1c01d0341c8031140b21000014820070340002203600184c0c1c80324080e40d42503140c080344501c10013040603e107080c021070b1212030010b105004056440340051104065907115503500400b06e40541c20f950f844050f5240100501d040c2c3c550b41e001c0c0c0c5280017400c00c001c04110f81c451003400703091440e00e85070780d03561810070f4022030412000e001080c031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 387668678 1250 387667428 387667433
    0x60b040e07090507030b060301050f0103090201051216140c0d03050702120408032206050304080a0c20040f020c0a020f0111030f030402041b0203090d051608010509010b19060503090a 80
    0x32a078400b82c00e0395080081e80f81445603011781115004240c03035008800510041240b552400501e20401100703080214140c0c00f544012a114820780c61082c8440594130140000b9160000290546880903140c03d00012200c50380c0390868080c45070319010359030000c003143c2e0900d0300c6504281c2c1c00040f039004071204038450741d8400070141c00c1600641660f0b03201041d95840700850090102c20f08402c108440c0425051640041840c84020409002000001880440c4500c42c1d00150122500464901c00b03019003090724000340301486003640e1041d0300306030824440384058400c031029040c1240c000c10004406609000e801c3c0038500380c0700d040c0607401c120f25249100c1800200000d18401c85103d69030726184c8104011140003c090400074091441a61800e44d000000c0b0380e2400342c00c407401d0703040074200e05d0300c18a0980c5161061003495041500000c031031505402042c00340055400900120b2401c000748111f10381c0c5500b44280c0030840b4082041060b0140c0300441d0060b1024040d9040360301c868 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 387669928 1250 387668678 387668683
    0x1510140f040311100e0604060305150d0503030618012106200c07080a24090212010b03010e06040209130606050604060507061404170c01090f0606030b01080604030c060b040e 76
    0x2d500556254054140030001403400000401600d192420952040c2900a011618034003d60195600b0b040d92030300440c00d100101c03020244681002864020143c0320740c900103459402c20f80d5558000c400c01c0d88001d502c144018425410b8680350414003407044480d00a10041116a007020b5900c50340e900824050035446250454a03240004020317652200c10342801c3e482e0100690028400c1c2d0000501517002a1180307480f22400f01000c003482ca84c00c110410100000c016481d00250302c28130003103500c0030a800c103402295448200310002c01c1002c40e0181d0981d103441c802c9034003d501045500004250b00004046c5074441401070300001166500c50000c01d00a0b4801d0700300c0c00c00b182c0c000c15100204000c5d400b82e40b181100b441d0441e0528101660f0360303003507880c06140113131074001c0104280b80da0603000d501402c815a044040b500640326981000c02c000c103560302050341c2a043d03000000c92117013000900e25003c0d07135155407120542682611410700415007003e9050f440b03a00c40c403010f02d592008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 387671178 1250 387669928 387669937
    0x110d0e0a050601120b010b0f090a03051609090c05210a0803103203032a210f090406170114060301060f1502070e01080f061510140f 58
    0x9600140500402410418039020050b0301400d081d00c0c2040203680011403640f409811101507600d5140c82c1c580c0540440600c0c06030001c040e0304511200c0001041c441d00203440410001c08207016140d43c3c1d21000c50b0b10940c0c0035100d02070015410031108100342c0c01c0203001040ca215003410444481e10b42141801c0c1840c20080c8160b521100c040144014180304020700785c000d0446d021080c1049100100000c40d14444035000600040816201000c5481c144122064200d40c0c00c200414000240e03028407400c088020130000c0317441112014624034607041e80980006c00c1c5001d48905042142c01581c00341d40c0701440780b0f5081038a407000010f00002020181e00190310040000c100134156241c005d001807001000641309030305108040240d50350342032980c416290104001a543c1410306030503864246250302c8100f02d10400400080e0184012803c48602083c850545282d900c6818915008940046101c0d600844540070b12a000b4003c0260020020054000743c0c10414030402c1e038100c0d43c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 387672428 1250 387671178 387671201
    0x24040606080610140d0f12032301080c040b0a03110409020405070302070219050a090e1203090a0b0702010b01050f0310150306080106120b011e0315020c0607030e10110d 74
    0x22182c41400480100031004507035013015118640d078030840741c65084051002c0740001e41242045018001da86200f500424802ea01e010f117141035408256200c015582030074071504c1560301612000c100b59250500410505000042403000340301c0c116250095600003251030b40c0d07841503a612201740161504e0140d280b00d0a42a00c0c01a02d400340ca0050101041031000c050300c00340c1030f65006000c1d69031182c00f01c0003038601d0702c074001070240c0d0f0080b611381c6400054101100030030404001c01031b510400249106200c1d01c155203448054076034020030b03401c4e16103071654140420800e000034088005a40d02a50348100311180801c2d03015030700c03400c1854420f8161800000641c4030082440300681c01d01440e001050080300c00851541d0035200d0407201c1606000d146228083c0070303005400111000c1002d000356802149050086820703440910003944460140c040714001e1400042c5d40c44c1c000d100c0c40f02c0c42c42c003090240c006a100048000000d11592014002c0010b007400803000b1019244541c115182 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 387673678 1250 387672428 387672451
    0x30f0c050a0e0907020d0f0207030c0e060a06050f090f0301140f0a060f08030306120715080709090c023c0703110907052203120e01030c02240406060806 67
    0x107245840080102c00e8003840d242c0101628410320800a5000030341020200f1a8500b0303601840d01600700b24201100c41d4009403482017801d03004129800e4a1500341d0003540700b12644612603994130f0094540c1c2c01103120b4503407a48020f104555080c100014804090b41005000042d54280d610f0490000304041c0c1d074100e40c4000c18010000c100107079210f140060700c07401c0d03002603c85140076406a601d1000a0200e800f0341c03203000b038807103000004100b104050030141300158400c105c4018018032150089a03020b001841449001501007458408c0481404456000e81170141580c0340c19948942880300000481c034445200020020308001c00c0480c0500700c0d400340c074001745542088e180501106a90714800c0c1c6c2c6c1d0005010300e5940220880b601c0300ca044040c3c140010031011000c8440510307501c00f402000a4084c1d40c006240c1c0310120115802e000d032001c100040c00258201e039031b031000c0d1107802455801040303460b10003c5981081503006108080c0800c1d41d903150070455040c090141d5030074400c04c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 387674928 1250 387673678 387673687
    0x260a030c020d020c060d02180603090d03060e13020405150a1202030c10090e130609061401080304060906030b0607060e060f0c0304020a06030519180b090106030c060807030f0c05 78
    0x15818071800690b8900341c4014540b01c0d24203800640d040c0300e00c1d003c401c41d06500160707500000340055460a0300ca100105503a449250100b401900e61418024100000380340560110708100c401001d41c0c0038102d0400b004800803050380c01d0000801014028088000c02804c41d802c05a07909000327580504117842c1c0704846000c082c414185407030041000c0900c2000840b04041c41150712810030011191003c84040c40c81e1219500100c02940d080400703400c00382018000b00a1140a401056400500c0395000ea060b0381d940c281d0384c0c0c9a00031781c062400010007014042200522941000705200030040c009031070100599901c500720346024601c43c900790004001c000c107007502040101d90080a400030503180d0f16250380040e00c0d03840f072402500b09266a41c80460f00d603c00c0501002c0c40a600c0740c070f082042c6881e0581c90395084030040400c565200c1075000280e0081c6043c0210812264002e0708103400e02c0c04d05c44240d41038a4000d08800c1019601c01803c20b03002014000c50225005070348449556 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 387676178 1250 387674928 387674951
    0x4030201110601060e1c0206030f190501081b040e060106020601150903080d0c0201200405040609020702090411060c030301030c05011e0f08100f0305060f1e04260a03 73
    0x16401e4407480145150005801000001d030001c074032400d840402c4a800748840b40d905070f40f00c0f2032100c0c1da50280d004080402005210160314100c18094000c02400d5001e5580700b00e00c1304c040da2424010600340b50400081035030f0300150007110305034000c002000880e940b03201491003032a0903800d80c0600c006a00c40350040203003440700d94184a002000d0710b4928410350a58032006442d20070200e000a07820384d0307007055101b070768401c0d40130359140c005118482c58170b00c80c1d968400c9116000381c003403d8480d914104c000a100f41c0c1c28401c40750481e60143ca818101e55030340d100e0091040114110384d4200e241000f00c40001a0b041c0000d60286108500d480e8516080000050880c800d504962203198030552421020311b0300000c00540d442001c0c0381c1800141d5541c6005a00c02106a0042c031995007041d41c080704202020480b184074080c01511660b40b0f61f104070200d82684a1000c10000103080c0c000800d02249a14811350043c101d45007030400c1341d1030115a81c01c00d079030045e0300317810019988042d41c542 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 387677428 1250 387676178 387676187
    0xf05010c0e01091d070504150309020112061a091804030306150f0518010210020a091e0b0f1e0a031d0706050d0213090501060207140a060509010c0f050d0504030201 72
    0x4641c0000e01c0c01445a60915200d40039040c004500c031400000030f0000541e1962080d004c50700503082c0303000661900010b10744041c010b40100c44049011680004680b48849100d101d440100c0d40d03404003003400340e41000075140a0b64451480543c208101d0707007103604020044120303240110310964000a0300d0b49018410030f0f500f0b02c1119058204414021072030100342d804004d45d1703c1500f0740404d07640544a000d0046c0c1c80d00e07451841c04040e0341d0010030400400b0b03802c40c0304172003101c41304150716400f40c80f920f81d078859500d501d006420b4654418090401c00880801c0030b1b043c403120b18104250012403030203515003140c00c040c07101c1c80001d455070200ca118440c04e000000340150018020a181428208080d025000c0c40200b034000d1940821464280c1d003001900c5c00040545110400403545c641d00300940b2000c0318014090705010400900340a41000035101d0115081c0d650390609200721040119030340a140b88c420741d0440460f02c2c10101040003800404020405903c800c0e07561882c5100152 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 387678678 1250 387677428 387677447
    0x1b0209040c0f06031b03050a0e070f2103050a0c1a24010c0b1501021504060c1b030e0f0f130b130e060612030d050106050a0e040e0d0513030f05010c 65
    0x3c1014207120350b41c40c000c0b0300050241c103a6821401c012440c1e580301031a0900901a01c0c6004500c3d10500c034000071803011300c111000507508481c807185071a807090001032008a1124800800044007045101801c0384075000804cc070700e2140a8101d80381c3c040340622011001c0c29254101407982c402d00c03040c0c0403007162100ca45059000e081c1502d40704400c0d180c00d8201030700280314100c1c43c5e000a00300d03003daa10a0294030308a1240381c60700c00722070800d4107145c0024000b03400e1102c0460225003000d10100800031a801025600d0340d940c0020742c1b01c0d88180302c290046404019040008103607200d005075100d904c1c03500d000a81d03801c002040c0300070a0070480c0650a0000d070840e42c0b464000c898500340c1001c01c14507800722040d10811681d20040700d0092031403150703c01130012146420000315240783c1c000010b095000c219a0380c0340078441c0c018100001c4610002e9004c41c6a40600030040c0300301c0c00f40000c0c042c18018040c4402519a0340d84441768030740000382c411a80741c2d40d1030205440c2c4036000303203159 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 387679928 1250 387678678 387678689
    0x1309050a021c05040b0f0903160503030f010f0b030c1c020c0114070903050a1103030c06010e1905070516080f160c0f080703060b060d0c11070905070f1b0209040c0f 72
    0x380304500700ba840e488004007000e0002c01b40c0480074130005803003140070003c4500c0c004801180c40e048010600305281c0341e40041d01c4004c10307000c4030000058040003050381c5405071400c0c602007500d151500111040d895000c140641007000185d250801041d0301803000e021245d02e10400407a08030151414000c410400a042c00148600804140080b40c3e00107465803020341c3c072032401e10700021104002407541c05600180302c1944500800820940c2c2040344a5020f6800c503004140074001023004542581c004480f200009074050040a1400d04188140481540580c0d84a803820b02ca15038818002c0e445032030b507004c41c4070035807c041e820804020380344002031801030b6107204610700302011036440e28218880078010b582c07200c41003240c90b40c522040b04c03000c04070507800f005100d11140020345411040303428000f0b24080d5820000d0101414000c251242450b6590100c01c0c4100d04000c1e0b890001e42040d82e96a0011125054016101d080320f60703000720300448400601900e040c0e031080d40031601c0d4100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 387681178 1250 387679928 387679931
    0x15070614010b091513080d020606030a0b0718170c09060a0506091e03011d0c10020c10020a12030203010f060e06040e130c090209010306080f0606061309050a021c 71
    0x41045446070b0080d0703210402c0c00c481d1941001402800002e450169020480c071100741c512000400d0040001d074455844000d8080e40c1e040c3d9a080201603c480d00914060000c0c8010b030006680d1901c580c0c9001100500d4004400c2c03ca516840603c40307502e081c14010001e0781c4058140200342c5400075440e5800700341118490107681c10034001c40d0701405070704509409000c0d903103240450340081000c00181841c0c080d000308000403001078190300e0031100b020782c06054001d103140e4601e170303080c001150001469684c009101c200c2c001130901a4901421101100310301941403044002201820841030004051f500983c903941802440c09900c2c1c1154061001d0140908107404075840d40c10a0b60121038101d109e030019540c1e91040c0300c00142804500415a401c0c071100410001d0b80e6038050f101403442a6810482c09446020159851403110321128480e413084002400ca4a0103800030107001c400004a130007946c0c2e540c0c803004103481081d00c40c040c895402056071241c2d4022001e0144014110080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 387682428 1250 387681178 387681181
    0x60a0309050f0c032b030b060417060402100305060a0311010e060304060903080708071d04060b0d09110303040e0604050606070c03121d09060d0c08070311040e0a150504030207030215070614 83
    0x3903000513040c0f405e05506040e2681d11030403030341e034400041d100209115940203800c55641c1c3d0160f0b46406040728201d1198584c01145000c103403187c46a10702c6980c0140003001182e040d51541007007400032800b42030421030480540d641a0712200080d42c020f5206030000305440307020f8500900302e42c4005104d2010080b0780300400a469912101516801e900c0ca10b80340c1c0c0d100100404039001c0c200380c0d04540e00c0100b0000c1c000e41f8400540d4070a10f4418000ca40d00f520341c4003d9070402d91070f446540700d180300348415580481c0b51860240e0081cad4011100038607513441d10078180d0303600e01c000101d5072081e201451170360500c03d0b00980101c201490000703100c041101c886282000a0f02c44000070300100d00071102c54a0f04000c206524000e0000341580f001220621030340c1746032022082004051740340c0103504001d04002607040000304807a020f54010101c03603d02c030304401040c004002c010020307800c5104402d000070141e05e0390401e20320102c40c0c0c1c102895a8200c2420140181e460844500008000c1d480 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 387683678 1250 387682428 387682483
    0x50303160c0b040609111f020f0c0a050402030a0f06120b09070e07081e0c18040c020d181a07050c090402012f0303070504051002010b0a05060a0309050f0c03 69
    0x64002d5030250303000c00002621201420706944140d6941e0b500b9812181400030700c10748a000b950341100d600e00c01c1c1e08540d90b40d51081d00e126201e190300000316400120040d001e12642c42e00740c000d140c0c071441044000a8060000c400c210a441c0d00790301c2400c544034603910800c24400346041c1240e00544031801001d0b103c3c542181084000401419601003004c081c001c54a082c0c44210020110850a0410400d6040c0309005020340d9110388144541d00d506190001d11504050045840d04041900507007002c407034403081554001c9042c540e2035900c25100601040c101c01d2040348500300f000c0080c819840f400703189042890f08010807000c6100b00004000c010050f03a00903c0401943c0b03403205801021418000c56101012041c40d0714048c601011081000140d403250181044400444410301c1d4490b400303805030308a40d81d425445030803e0000e04148545d0034200c0040404400c5440c0002e641c0405440d140d08148481010303803143c0d040001141e40f1454200a40c2d136150080c9a01656032107c0e82 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 387684928 1250 387683678 387683693
    0xf01030f02012706030e0d090f09051018060303080c070b01031203062c0f0f04080a0e130b040609021204020d020d021305070305220f0c0b07050303160c 67
    0x40c10003410021006090202c1d0641103119103114804584114030035601c500010b0b000d44a00303030081103244034005080003d14492912070040b6900c20303494124003814a0810070150400030203410100d54055000180313030b401040254440c40c00300c07100150784e80c00c614000340703804005040c00207014000c0c0040340104a040328170904503903209600c036a1004002c4002d802400300b60740060070350503050409400c581c0c010b0811081d10074200c0c202d032103260f9440c8403880c8580070944400e4000326100d40000d0000e55880c1c000c04c000300c1581880b010a48084001441040400c7c0c225020344e80c9505903004142040c3c00354402405845405508000048070954003840c0010800783c0f00d112010101c1c402e40d11640c000303030b0080f80c000c0e00c004c21442e005c240d031001408060700d40c2c0700040d1505000509110704010034441140a078008115541170030703182c481038107020040555000d80c489500060a80e44140100b81d4240300310043c40c0c030703441c00744840742c000394110391070360140324210300c0381030008130032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 387686178 1250 387684928 387684953
    0xf0109140f07030e03160b07030c08040b13150c020106050913260301030f0b0708040201050a03021b060916051804081815040503010e0705060307031a0a0902040e0f0103 74
    0x10519071816503628601200070b88041c1013200510301001654071406100c4500940750f00d03009811003800c1e0349500b4412011103800041c104c0028800c40081400200b44850b1550000412030080c0d80300f143c10707184d4a004214451419400c2540c1e41c05d24040540c0a005200003800121180b0116241113480c0366024044020000d001030000060002e03400000644e03180034070003002c08641c17a980c40780b9061003040c91900083d03503c42554400241c42502c01c441484c0b045906035105428100d040d1025170194014a2052070710440f07223045900a0403007000868850380700074008254800803040c840c20740401d290480c2c1d02505000c80609201100c0c020044e410580c0310720800c0e0f031220b010b11304d00181c07640d030b40c009644417018400140390801000060010744108900800544080340310341603441e6424820b240e04400280001007a10780258402445082125201500003640c1e0b0300042c5501201d4211040180e4040f50902c00507030910b401640c0003c00068050f560750640d2a1480242c01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 387687428 1250 387686178 387686191
    0x4330906050702030109060903050715020f040311010e03120426030405060a12020f1206030a1101031d030d0507030507050301081c05040302090a050f1e0a05040c1d0f010914 76
    0x41c001040000c40d1802d52001d418250009004c2204200e24580140190300c42e81c03043d500c2180d013866003180d54166100700c508620880c4240c901c1d280c40d580c0d611604548003180309050250030b25002d040c6840502c4250103090002c0d006558a5003080305440a0880080070781540b80700c002500c08031a04000202c5095032011186c07180c41d50002e2a00b00e49042107214044509400804c0c1444c024404070007130311200c6010356401140c2d42e030303840525594540c085000362440b8030032441144594020b0f0b00607030740440c0b1401c03c9004141c3c003c03601c510310740c05558214200303035403a000c000103940d052146a401003001d01e070480c911b508d005421687c4400b060f40881070250b14800c0c00e089180110105d07802560701620a05031807608030208030042c0402c407068114103140d040000c1c0046090301d0300c805500081101c05049d5140d88190344010103000348100c2d0070511494012491540e00800e1440e1100070b030003006410314000c80d41900350305069011200c080c0c00e01030f0380304550005024a90b401306 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 387688678 1250 387687428 387687437
    0x5280206090d050d0915030207050a030c02030c0a06260705030703020c2109100e0d060e0a0b240a1820130918020a150c050304330906 59
    0x1042080003501082c480c039001441da116291070030300d2094000e903410b004c8401128040d500210b02031410780036413144203001405034028800ca100001e002b5211202000c0c0042c048403c50310444000c00ca481d982a0400782c082240802481301c944886030846115081500403179400d81048140a4803902019103003234140754010644004181c010802d284881c15090300b0307a000148a0940300071580e0001c04401d01070060a0400c0c0da4560180068001c80c0002038807018040e841900c800000f00b102d81c200c20018051840600b0100d454824002c0c025500342c5800300d4954040c10f03418070020902d0a80d1030081040040412a2400403c4610f18070034100101041c01000881c0d0b001e406c41c20a850401c6440001c5044100002c44d14101020345003049070801c107500701000124112044000000e5004580a00502031420000440c4601008900f072000003480103903a441e00b141c0164014081d00d40c1c069041d4400300d08041000e03411480e41080c4140242d00e60b40c801000400107009000902 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 387689928 1250 387688678 387688687
    0x206011a0909130b07110d0309030c060606182108070f02030a03120f0b0a120201212a0c060c021207080408010b0109060903020f040f020c010905280206 67
    0x3400d15088401c030800040c0601d0312442d140c1c030310703820305032080f107080d034030419110300042000d402030881000a01e0300c1d2005082d04224100c003103010340287c1000324204001e0000d10b000280150140a015013085c0d1107503034118400c110018250701d05640050555449858581c80c070381c0c1d03030000d40c015a503005103000d07540d000e807410b0983c81802c00240094261141030925030605130b100c0703211810803480c0e14081c0305010b000c648070825248181d8241d0350082c4d808008001c401da04000c0038418502c10f0402c0001615000d40004d109080c00118040386038803510000ea150310119000e014001031010607103120440350b0f600030510300c00306000900d00c3d03640d0700101d5100f41c001c0000c403040c1150548155035071079a900c0d0600303080e0041c1c41441c0e440d6081182100781c940c000c002c0e0328140d806655410b20461701c1d40e020801001450f4a2603a0050f0f5510011507080c6013600060902102000c004150070401d81750451401581c8504800f040b440795035095218040c880351a0003803a0125078040d00c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 387691178 1250 387689928 387689969
    0x22080f250f2006071a01090c080117010b090a0902090703091115040504021b070b0c0d081f150930050f15070e01032c0c06041211060703020601 63
    0x10005044020382c0c0c40350300401d468040000c0620a200b581d13100301744091040e681d41c4003c000b91401c054058002c034080c0001484143c04d04215510141100000880c00983d40c602146031a54251244c44440da240c42c082029070800207499604141280f408101d104825111708400500e40b940302c2c0d214441301e0380c08400040c0a10107507409018010811903958004051205415250542d42c2166005007100000d440580c00103941401000c0b401409601e44000c00441e034010b40180514949007005140d500801e0f544140394026001c0d6883c003446890380040041d007006141e9002d0031421001c09000030030020322103540007540b0071200341080f400c1414a000d90406011040344003251045152130000e252a5201060151625407a148a400c001400440640b071a4a15510303070720700060400e550f050401c04e0b0900c41500c03e1015140641a0b0310002546988240d00c9019290f080750103640a03c2541e40c00c0c1d103020902210907030f1612020b9500031752540c605200365803501c1515045180c9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 387692428 1250 387691178 387691223
    0x30303090203210c12070803270312010611010510093602010f1e0c0221030409150e0c031906031a13030822080f250f 52
    0x400740320220410300380020543d5012001d41002261408510400741324044549002d0100e400440e00400124519074600f24101001d168031107903603410890b0080c80d8081c411007400607282c0b40150707800036141545000c400400d0910780b00340d040d0784c59240205100b03121091704490012140303525070200391568100906101000198881c280128804804010aa03442d900e00d0071030500c00d0300c1303141d100c1c2c50212080314101ca041c10311940311000403000c0c1260741e000e480c41007103103480208000f2140601c0298002c0d03200641a4100c640c0c0c1c00400d09005001c510301550940004410051103c40d00e1700185292008001d03200090038000000072504c2c0b1001040403440503954240107010180d42c07440c0c43e469210100b800c15114152101c04108040d0b5004028103c1c55059501d04541e900c500307010300c01078510a03020006042c14000c1120024514501034085e003810554096194104a0520492000050300000950201c004a07a0018850706502c200300380d0000b900300e0303011003164103405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 387693678 1250 387692428 387692443
    0x3070302240d02040e07170105041503020d05070806010b0705060406050709051009060305150904121b0303050f01051f0e01030209040501032003340e090f0d02060709030303090203 79
    0x6141010006042c003040109400400846019000b40381d20f641d280e06088806440c4004010030013076a40004000a2405400c0001030b001d140216140b12030790b0398002100c41c011000704951a0300400d004125210050002500400030f2003042c510b00000c2c3c0d039656407a6440200010200c42c0c2d41e1022a480718481c0c41100054074003c1d040131185c89080398003515500c010301c0347c40b0009003003000180b0401000140711000c20406400380d0392070b850b2560703034160b4190030b401501c00308281c03a00b981426485880c542606103009482c001142c0c201103100d50840c1c10305802c9140104a4950020903003150310301071420500141c07a01c80100309403000103c007c0d1080c0d125040e0b00908000000c801d0007890800d0a079031044a000c0020760403c1002499104c0845134044140e04ca41c651590b08001d4032168941c05080d8442c00420364203841c1c84840d101220f0641e944c80d4254440c11000000d046d0810100419490a00041200d0320f8540d0006200c000c0b1804003c04142d00c90344540210f480030810103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 387694928 1250 387693678 387693739
    0x71809050601021921082a040501080613060927030512100e010b0c0105070f02120a03020c0708010209150405101214070e01090b0711011b05030304150501060e03070302 74
    0x507807026000d80002c0100d007007034030140c65144840240300c2c542840e10031f24415035506881d545080528000040d6009040100b0154104c2c02c8039603c074508840754801c04000c0d050840c400655140c0103a229042e05480710b544001106e8489504400720b45c000301600e14584040706c0917141e40d17844541403840d1601c1e540c03105c0c0c0200c03074110004c500a95043c0c054651001407000030401076503840c00c22a040c842c440f21540150b00f1031507505402014200c000c14002900c1e06001d0702e4020b4240a080c075200460b4018295a5400318488440b0701e001440c840c0748a01481c0d08505041c200f60001e1102038040b040348082c0100038150010105d025008126040700d01c0e14000004d1078000c10180042610070051030000350541c0022502004400c2998103040e007100a0402c012410130040d244440c0d00060354030102c12000d00c50000500810065201b507214403d02241c1901c100d00050a40b80b041c2c014009202e01100c0c0781c005a200010031600f01d90701225040030901c120b110240581c1e00c4032050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 387696178 1250 387694928 387694973
    0x7021503040b0103170915340b062e12020711130e030f0a0e1002101a01120f0b150408060a0c1e05120718090506010219 53
    0x1c100a00000800d0a41202d01503105010101c1c580001c40710188107036404540c1c0f15846051503241404404090994090800013140524503142045861400c80c0c2c481c0601160340d200001c0100400242c10a401140070baa0009000210301c4a076008800b0381403004200b01468a0104c443d10300c82c407141d40c600c036400fa5003155680d505080a2915040c80c8624501918905440d0540c0c64014855224001c65020155040c8190300c06030600c141d0021010108001b080c9000440964884000440280380c58005261400c4011820340540f84228548076191098840f04030701660443c08101c0360340b1003900c7c00540e0325240070168009200300350ba96508805180c0403490f000d101d01004009680039001125082d5941c0b614142c10386406030b01c540c001a110541d05182003c805840310b24102090402d54101898010814840f41040b40c1c80800070340c11422101124070807483c8600689035014003070040303150035030020356202c40035000e00d2060240160500c1c10301821407200d0f103000060008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 387697428 1250 387696178 387696181
    0x30a020307060f1e050703050603030309031608090306160f02070b03040b1e070507051504210909050c090f0a0812160f031e02010c0806121005040804090b0603150607021503 76
    0x20550001c117402c40d0f010010903d4840400d41501d000001c2d24454000c0308011441c0401100c0e041182c6808003400b00e80303035001841400c80303a03075041c06082d1051300d54003900302660416180003000c400d414450710741907400101c818001803800c0c5007140e9200307420070399542d0307180c652207400c940540c103950070760313401301c1c01c0380280220558040b0040c41c10a00440895651060350380e0365440030300050700e00401040c8a800c4d90381210111402c180000301d50340c01e102c00d01702e0f504c1e1126020340c2d6003221003c42d01a400246280c42e450706041140c4180c0050300e41402890408003480d41e28400460a80d0085002140034010364440140d10f4912690000881020710103038a0054814800c0304000241c0300c001e0303188580182d00c144070b01900c000d040c0e685d503003ea03164102802800014168104c1c0d1320f0280755003070810b00445006041c000c0e8800c54840e541c2d5464208400c003241e400c103275260308c142e0003042800f61b5205c06894591180c50b00310750080d60303200640700007182c05091501503001100d0100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 387698678 1250 387697428 387697481
    0x8040e0619090b03160e0103020f01020a080d061a0711040e070f030803070801080d0c080306040b03190b09160504330f0b0408030a0f020c0a0305061503030a020307060f 74
    0x10000800020240c4c1115425501045099000c00c00c81c083d4129100d414001000035182c42c454141a0346c1040c016140707507404c691202d031000ea0081c04481c0f40d00d9211340c0304100e941110261845281078480c1d01a080410b980d80f0442e5083c034940e0110b01c10350311806c0000c0380c0e1a0510543c4000d00840241308559a66032400f40c2172a0003c03035010000c6806440006180726021619846c0d8001d5580c5a141e10030041d6160005908050600c5400590380c05c3c041d401c40d101000070f07241c1e0079080700c04070002c1409031030b0841041400909001198101c4096541f60b42904840340e01510011540800d070714103000740e52044a103440b2040c00400000461110550480071345c3c02c015907410385000503030700752695200507680c4103502c5010543e42c8108450940c1d030b84204441c3c02001d8041c030581d100050440005840200030350000e680d5a0088014000303004080310782e20410043c10b81c00795041190441019413070303004111007c3d0040342c480c2c4a00e00301c0c0c0300503030060103501c04480e0151002d02074032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 387699928 1250 387698678 387698681
    0x9010f0305281e091205070819110f0304080a02090a0e01060605030907140906010e0a08030406030f0f051e1f140102010b0a05060f0c010f0c0305100b0708040e061909 73
    0x101002ca84940e9001295041042103000f050462078000081901ca0340b80d9805c03c4895900070b01c0e040c1c80b40d25090043c0d030401c00780c050031141c044500359600200d01c80403150301410851581658103491703100300020440c044010a0310f00c00b054049810301c2c034035030720740b40c1103c0a82030303210f00c0070065443c5c900007181e52a00200a5801403d80b1001c903030829841d0102a101000c82208403a030085240001507601e40c440c9500c030145070400760031104003565525001c0c0c9035030841d0704240c010076294211490010001d10030701d0181034240906100905084040c0b0308441448000240500310a00010341c4036040b11084140d140703038450000003100c1da80c201020041d090b80c0301060042d4206130f01c00d0320510f4100b040106071070004020300c0c07508001e4100403901d030b445088600850354132094610300410192088070000030f420b46004c81d861030b001c6460100103440b03401a003002d003010711003880454141c0f000c0e03e09071007025040c0c86050306e8200000e84001c005012040940080720000f1030109050f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 387701178 1250 387699928 387699941
    0x503070501150e070c03020606060705150103050102091311030106050a09330810051c0236040b070c0606030b090106090b061c0506040623130209010f030528 69
    0x3c0f01d108070360315642000c070340b114500b1801400580c4580007040841c0340180052071064811011210b402d0b2120b200104a03200c01d0388151166540801c0c0c0c2c0103681849014988080c1c44510101703c44150b22180700e01500040c002c14003000000300c2d0020b4a94010f0b503202010340007d82459081e1480104500020001641c001c40050142c40960440d035005644490091b800c1145450100f410902400b402150404205190001240c103640260311404e00d403200c0e40c1c1040c1d1600070018018041c100c0d102070b01d00c0d0f03540784402070402004085042c0500c03041c3c210141e480c214220002c0c0d030900c2000303489540c0015246004500c180b1026030b50541c000c1046420f00d1409001842c601e00c00c000c5d85c0e010328401c40c00c55201e04040c08034071072200e6000340d81c00304004000080ea2500c0707215810b00d10080d0124000080140c500c43d03a040d103001c861000041c400080c00b94500481400020301e003a101c1e03089101455142c801141014440311514840004d010000a400398104114000a0302e034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 387702428 1250 387701178 387701189
    0x3090a060c110c0909010f0c02011a03070f0b0d020714030909061e010809100905030d06090b01090e07021203090a020405090309062d0a03050105040b01110d0c050307050115 76
    0x341115070078100d80500c541d10540b02000014046642c0070005100c401e040c0103105803501c0d5640e6070348103404919445048400c0d801c1e0382c0002000247c013280700064030300480c4094441c1d030208804201e100c124034415426a0220034010343c03209208103840c0041c0c050302000a2140361107000126480400001414810108940b0200191601410300c112805045109070100c3c00c00c4444411a5014180c21604a02d0796412500d0ad0508004000121030034220b04658980001603601c552510703d002e0003003d452048003c0041c10715580001e01200c40c0c41c4035038285030095a0018107081e00078000708907411001080f60b076503440c2252810b5111003a183c03089110f18540070119402020000c10b03904a6440541418a01310a90f101c03070003644d010f00d000848a40e146481d000c06006094040c0044808588000c00c20394106070400c4240c4545c0140f480c1000302c0e03440d081e426030781c0000307a00600b86058144400c5640c03450506a045200d0200054403660804e509002e91003000a4000300302c94 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 387703678 1250 387702428 387702431
    0x30c120304292b050c040b07020604081e07060e0a030210050c0706030e0106080601030b0a020714100c0e06090a09020d1104030b010e0603060c1e07050d0207051306030c03080d0b0603090a06 83
    0x2d0b07101000c000300d48059034105d800c06010300050140c2d070003a100810300107000520b46401c00380d881c40ba540c039058000303660014400704080032602d224001c210010103050356040c287d50280e190070104840320081c0c807001c0d10404081404c50404c5010708103d9003a281c00b0070649907116244c1001802902c03900403120381325840c00308001011840072418506a90740301c203401c07440e6111650b111000c0c2d040104185c6111541c50b8030f111481c501041226540d105041c1d02180c9641e8805002e006050190360f4540514010071a141265aa01d45141c00755618000c0058a40c040580da0340014021104007020704000003c010060182c00f0340d602c0d0484524aa01990360794500c01455254502601d048803180024401c01140190789002d40181c1c0c1c9501e05014100304854507024500020507540b440136030081d40c2c040c0310300e00b040600c2d14244800802c05005951440c2e50b21642006288000b502054011641c04c1052205402c60381c10f601004150f180c480c01c00440c003d4880e00346200884025 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 387704928 1250 387703678 387703747
    0x30f0203071112041d0a0209120f0d080601051c0204050a03060b090903070b010b0c120f0703110304080d1206050d0305180a0509060409020d05010507020705030c12030429 75
    0x19520200301d0b415a030b503070220014170b0400c20b6050507030010040c1c0f0a101c002e07024000c184540d2595039102d10358000b40d4004000610000c0801401c00c20f0000f00042001420001c1041590b000011220900f503114190695141b507010b40c0e1000340565004141e21083d242400004d0005981021381c6021080704d013041e41c0d4440e03c0926541e0304c41c2c03200051410f420003004102d00b000f820702804054041ea030542701c0715141b42c0c0c0c25192607489800d4012444c01c020520000341030340406e10740091041280110b1626041c115840d80d507104021f040004c0041c06846880c0c005600d401a0004000140020700600c4891901070706a03000170850b030030144ca02011a8910749020004030040b26000303040b9088030703180c0d0014840500440c54060360800d95000702c0800240c02441640d1003005140c0c040c0c2011401c1c02c08150810444c1c240b8a4859211008940441c3c44080212000c4034078100c421100d13a5966070314641c8440341442011144180031030b01c1d81802c3c8a20b840d00700d04540782214006003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 387706178 1250 387704928 387704953
    0x103050c03070e12100606080f24060c0a05070602031b0c0109060c060209090903030a0b120304060807170406050a27021009030b0903070302010507080405060c070201030f02030711 79
    0x450004454090004144002d0036115080049103000310303100e411305036405403070000001002d072000c1d68003040c0040c00010806c04540c520289040e048400ba03a46482c0c000780c402000c1400f1901500403034480d050020304090720a00400c100c101030784d4058155491590742e600065100c0d00070703034135000c08249030185261710b6680201d003400c10640140c5404500d24203201c403c6801500d400c00403900c4603400c11000e50a50740b400b07403242c440d041280003156030349001e010000689804031602c600950030003581a103090808010b4400f40c0d00d01d450207039495990140c045880340625030b200850301101a081c4418040c4a80145129017044442840741440c10304104200c102c00d841e244e028110302da00c26a0051414031000c0c403c5183e1860202d2038151a506d90103100b0f2000e4502401f580d000080d00c0c0f04054080c01410741c0f00d080c0707080c41d419500d826100d103901c50400a104103180640054041c0071607009900030483c0003a100310441d242d141144010b00903908000c0040324510808540c4000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 387707428 1250 387706178 387706201
    0x10c0807092d05030604140c0d020a140a0e0403030203010f0e012301020c061605012d090318080a0201110105100504050a180f0c051504210203070b09010305 69
    0x1100d0300420180700341d9468140015018000c042c502c880040900000107942d41e041140500503405600305c0d28020809416035840d041c2e00070f5020340214091405000035a6a1138001e2080303a008065590180e4030740c40c00980b04503840e030403440c0007501314010300c001c1c1903040c2c0c081d6040c3c42c0341011030a000340d291142002008424802d01c5000d144030800003580d03220600408401e04010300440c0d9245002c0c07000100242c221a00460300081204418400c0c8031003401000c0c0907400c0c0c4034002c0c1060490460442e080035016901e07042a5403940d661078101481909078031142000000e030000700310f403101019174650b184070b01e0a070b00282c80d800c01d100300001d040c4200b0340a54490b0790704e10080c81c500418007006d090001d050050407903541442d941c0c01e070500e04940c0303095445101c0ca10f8241a03603103010680400c650f040315000b40f4030b520640c1c900000317040881c1c0940700e51448410000080c0140808140f9074404025054010168006800d400d01005008042c401340c8050040d0f035140320881c031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 387708678 1250 387707428 387707447
    0x905010b09040c450305030f16290f070503240d050d0f0207180216021002011e05040c03031b12050702011d130506030a02030708010c0807 61
    0x1120410401d040c400d103420fa000103550011410a0021340108402503050422044030700616810a8011600500a81d1411070441c1c840701c030314003038464195286d0755601c0c0516050701c1e40c50074000400c00000c50281c0302c3c81c07405960140c0320000442ea201d0050402c078040700d550400307509075200415421003580403c02d210701025941d07142103a81c0c1041c0c400300c51044500701c41c840c14030345120320006c0e10340034280800342c1d00401c010080f01c40d0800000b010303c11008442021904019010300c10b6107058115002c820381c400b45d0150712400500c5c0c42017074003000d002d0000c0d8000c0c04501d1040101d034042d013200c000b2941e020002812101140c8440b0161030302150024221480c5036428070000b801010290030084c801400d071740004400d82d4406c10380d002064410700c003141000c40d41e24115070707008402448010801410b00171807003515000c5000c4200c03006108541a4549000070341c2c603182004881d00c10354004048855132595010f0031402808035140200000d0309250007d600240110860f1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 387709928 1250 387708678 387708689
    0xa200a0f09060807170c07140a140601080624040c030b0108060409020303030406020c03070506091609110a0e1201110310050405010b07110d0f0515010e010f062307140601090501 78
    0x203130450b0b0880c1740340b1200250028060540d000050000d8000f2807000920807000c0d2804a004000186940c105440c0c01d90900603004c0103540910f00501c805000801d4080e0050030090740c001c000454002d0030107914084d99465904146030400b00a40c1c150300d03802008054200380c803004801e0319000c7c140025520398010107034040d803042010034000b031a50780c002e002c0006060140e0f81082c4896482500b0b08000343c0d6410003d034000c8160b04564401c07148104001d2000240803c110144082c41c4280760144d5406c01003400078114095185440c0c683e43d0300703050f203070180003007003d140d0035030300c498607900190703500c909035030129601280a00306442100e040c1c601e441d900f1800e1604a60b24448800c0da100e4200780c008a5070a076200c0028080c001c0180710310b2041d000b9000442245505e44d1a0b12016805002c0c2e049a060040240c40c15204001c420786241e40391200c4014600c070000e81e4600b080d58040307619a10006054018440a00c5c401381c040d003100000d48020f0303661200c40d0405d5981c20302aa = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 387711178 1250 387709928 387709937
    0x509060708090303040306060b0c0f1f0917030123030a030813030e03030409020301030219030c05060d020f0309071a0702010e121603030e0301060f0e0a200a0f09060807 74
    0x1a0000705081d9406000320580040869103400e80300d998050540702540d00c01d000204010801101e1003605020310b00d4501030410040c46150907181d0110800c20180111031401d6a5412250003801070103403c104504801881590f66541d440401031900c1002d558108100c00088100482d90b10380824605030150b01540c0f5290ba5444140d800780300303c05103903022800d02c200822a0010741e1400d0003d8401003180c000016101c0d0301d50300601c0706840340d040c500179200600c030100348000781036122134505480051f0b96058980c070407015910024032903a4055014034801000700310605000003004804e03644058241c64144017540c4844510380204000240810000310444506050540850710700381d001303a0442d09021083d08a0104508264009030000313144601c800740c050500b40070b2a001807820b6007244120314031b170a490384950070000d005148100d4aa22240040500150381005082c1c0072a08096844021890250074004d61111000c00300f0008080010030601580540340715003156180c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 387712428 1250 387711178 387711187
    0x31109100e030a06060806040611030609010902090d060204380d090f2001080c041406070203030c06010e04332a030203090c030c0121110a0f030b01050906 68
    0x1041e6062041c41128603014407500e484500813410034001c0400038540c51014060702d00b02820100140c0380310b20061100b40401b0810f001c015210101c405c0e04545208500607110055078000602d540c000b94409000b950000c58084ac0329940c072168041c0c906001590f52404a070b210140d10b4035402d000d01580c1c0c5141e424400f050030a41140c0248040612501040300e111085641d50307030030051604507a08070011390089002107940c1104015070040d0740004200d041c9031070710504035030010311609018080c207400314180c811502e0402c01c0c0c41e07840015009544896840e00c40e008091041200c0a5440c142050007214104c0780c000d04e0b20344016621200034000030560710104020300100c941c0444075020303101002001c0c82a00c0d0302441c0d000d8403540c0c05030b83d9090004081c0e1a0601000c0b01620a402001308940a41e03042100111840f100110f9041c8400829102400410682c140011801400140d903403009900070810824061a51001c001103441c030001141c1034045d81d800303690084403c01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 387713678 1250 387712428 387712459
    0x1052209050a0c060e010801051e0415030c030f05010510030c0e04020a031202030705010f0b0108180102040914160309081b0c0415081c05070809121c031109 69
    0x8200603a200c1c0908100c424041482d680d041c062140303688034a0008010030501d00c140c1d0381c4070107018018401251103a1403e0002c0c0c01e02d80449164049184c8900e036101012204c004100b6400e03c019074001404011056407810b0140308060000f43c200d84039440d000002d040306840c401d15600741e0360001600521a0700b81807482140d501d01a10699101042a41c0000020781005131903c7e44051540030310740360b44842c03410b1800c1d41d0540c01200600e90418049c048a0b0340c0c0014441d40c0700020036141400c7c0e414503980c4600a00c515080400c1080c20a00810002d81440083c940950ba009617044c200125214044040303030030341030000b40252000c2140010091850050110719040d210070317030b503607500b03403000040c00c07242561440b00c1c052401400802100342c0034000c0030281c41005500340702100800350010030710f00c2510401820b80e2408104102d9a0312815211002000c010088500f109403101410500420b184400d4002030b04002854800c0c449250594001c004082e1540180c5010031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 387714928 1250 387713678 387713681
    0x3080a060807061428090909080315010908060a02071403091809030426010606110706050f09100c060c09030f140120030906182e0204031109010522 65
    0x40c0f1942403400c03060015640d0754011742c2901d044080c030104e0001c0300080744000544030b2451b030360029110320b180909480114031070f58201e0b0350014107158444042401800140d40e00340c0030350011480e512426042040b18059079005146460080090b0506040c07020a040c0c0c1e28800d20020540140c0c580c040004810300850701c3c0c0383c000d05018252400e080e220b46048145500340065a14140c42035195a6a000c100b80b184a003d00200d140110850b000945c503195074005900c030302010400b00180c031030300c003000110541e80c052400601020880c5101c100081813040781e002c09a03165450546500021030044c68000d0031258400c2c3d016504d020701b0703280d091001a684028003070035501d070000c020055500b442001205219441c2e1aa00c2c1d0600484a524000d030013090404465044400c41041e0b540000c0c200e100c0b14800500c141c1c03c41d03141d603040d00344500717090204603e8500100303010040180b0b105251801c89130075503142010f80c2e43e50302013110568094882c0302c5208100196040340300c0300c6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 387716178 1250 387714928 387714947
    0x80616020c190506131a12073e0c01050c0c0f041506050319090c05040c2705010206090109112b120f080106091401260403080a06080706 60
    0x440c42401500f56a080491150350010030b03403801124209106000c0d03001d0300e9400065901c842c075002410a134903088420a480c80c003030142414081d00c0744440070602090001400c81c043e80701106118480d0083c604004030100c542041a24000c01030027540d1944075500f6269000c411000421a04c60b01900744074603d81c41d04003454019494200f4580380c91040503e800040429640d800c0c3e4038a0000e19480001040315411311a50742040790502c0403030940c1200300709850781101c0c0000e0701044c0c000107580c04005240007201503d80320320070b00b248901c0c2c40c1c200c400712842a0261a01a81d0b009885807c0715009800180184241031010b480c81c1040404c112003281d2200040c1515044045d401d00c602c2c0003014212101c041400080301d4061f0300c4928125180303458286000554141100a80081b5060042c03604540c50284040071984c420440c0c1c038400c01e0703c038603400d542d14055480121004012030f02540800d2500d408101d2100d6030f4851801201c0589015008076800c0c4102140c21294 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 387717428 1250 387716178 387716209
    0x30f110d230102120408130f05060304031d1807020706080f160909050c03042d020112140108010207061b020c0112060e0a0507020c0f030613020102070803070606080616020c 76
    0x609004e00c0622101c00700a0394016402218415200c1d50b0501c02841c80741c406822003c804040310004001a4454105498001d50700d81840030710820441c02031003c01d024481e61030361116080181d071031038000c0c03001c0c00c50140c071165003502d103c0c5468020988010409070f4034400d445943c04005000a85404c03076040803d0600d2400d0b10790550381d202c003030040d1030003500c1d42e509880c0c0000901041001c1140c25803020f0095014090070f00014655001c80d180d9040700203414003440d101061040d040036400070b204460b0705117505d6001e50311924001d000703401c011030486003036185c0b40480d18480c10401c92506902c1031a801082d54521074001190582c0c807000e2400189a04c851000ca44400384c6807415200d0500c25000143e40c2c81c10f40d0000345010a0120480e0240c04880000d1480740c0703021800c0303548034180020202e44c00d101440100d25100342c5074842000c501000c07a1010401c041d82d04482e003181c02070070403201e60792100e1401c0d9040b80c101d00300200250748002800903d034100081000300011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 387718678 1250 387717428 387717431
    0x30703020d0c0b0f0a170403020607030908040b1209010507030b0a12030207050409030e010206010e06010c06090c080f060907060f080703051305011503030212040803120c090307030f110d2301 84
    0x665983c0041e032250003240601d1465280401d44c1da90481c3c1c4040014805400d41c40003102c14105a14003a40300c5001502880c10192107810301c1081c803c124007140e00400101d81c81a640d1005101e04d070504600c140c0e5502c815500308800329001c3d034800c0c0101e07100050010009948280707814211421004d81d80000c4055000d603030400582580d0300d201c0c03c501d0a000f9128500b0780403003240024280801604000030500115080c040140d91052003064020b500501c001903801d0941410281042a80d1280300725100e40602ca1a40744c0300420154001c1300d40c1c0e822910515241c3c40e0079182003190307052040001d508100007800803880b03504201d812120b00c002441c6d00c0c18040d00c800b401e568250301c0008006a95007002c0040541c10005001c0e00c0d540041d4030b40c00c0038144105a03403603114580c0c42c0c2000264550200c0e101e14011001c40308000c10080850340410f90b280b13401c1200d0328041d501a18600d02080d00d04505003480042e81101c55841140955032144c2c14506600c2c51070186117020351503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 387719928 1250 387718678 387718703
    0x1e010905060c070305011406091605031306060e0c041509030515040f020a0306021e0301120b0c0d021305010905060a081612150521030d0c050c0105040f120c02030703020d 75
    0x150080c461411f50700b400301440001450088d0038011020000380c8681034151421000c05046580103003640c0c0c109010a01d0b030000100c0d5401c000010300f8064000c1080003560005210710040d031000144100c92011081c6084120017003030650308074009100181454001e002444040d1003850089680b0901c2a66191210030141d004108005200e0b0030031101c0c168006000341c00ca0024035005480ca003500b02c8008d01c0c544c10411210019584040010031400006002c0340c03921a04030161020100d03c140210f48541c8400d00131130f07102010b131040e5030119941d080085001d0404000712051030442e5198980c0c3c0b074894640e0100c5004030070000d0010440b10000e48107501240b4060000706010f01c070000403003d0306003010080848008907803074100c00c2c2092022043c111000c030a48460380c00910300010512028401a107162141c503450521075464842000308001441320904d88141c024003403000501c05601c019100d0003c02c00740658160b01400d020401450031000743e0540a104090420340d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 387721178 1250 387719928 387719933
    0x2403080d020d140708060d020d0b041a1f05060313020d0507051201050a0c0c0c060302030c190f0e060310030206031b1b060907030809060a02120d0b1e010905060c0703 73
    0x88070000c0d443d00000c1c6201409125015030310641d41c98000c2400c036200c118a03125540012061661410000d02c2800b1000004080c000d01e032920002480040303209440034070f44100160786204020150760f4001009420104290400c201a03030310829400003c0001000c654003002801c1d9480c0c08101c0b00c0c0d214603007000c202038490102542c80c1c1216940041450b040152502d0180c4a51144000400028416800104144851410403100c0508005076030391100c3c9091800303442503600700705200c20112482c9401c254402842107500714542c0d0b400100101c2c1c2d808000700ea11064840c05c800c0c0342602c8092015140c124002c54000c03084001192401490400d02c1c00303250406480307560781da900c3c8011154002018400307140d000380010041c001107400c6680c1e010041c018840c0103070050b030000c510044080d008024242c410006202c5c4c40d926804000e010764094001101411b0052104822500414007004020001110140c550403c41401e00041c00030542260a5500741845084c000001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 387722428 1250 387721178 387721181
    0x705060412140c012007030b0c0d0c020604020f040c030b04050903090a12050312090307020a0906050406080f100c17010603060504050601050306011709150a06092403080d020d 77
    0x900724074201d6807120510341455114680002c0040700d054120921450207682d0000180c014100ca00c404440340c0c1c0c0800922a140c00c942c2e404c0104204140d1081c09100c09910014244202c3d41d40300031700001488002c12078403003005407802500600490b024000c01c2c0740c03d800408001c1d882c0d01d000130b81207c040c00098142c89066840302e106410025119440c0e0501d2031300c03940981550500d6000080c03143e51025560302c1601d01d6900f2100d405c1012032035600040c811034004507002003081c000365480d41c144130000d02e2607129041c07056161200c00204408003080701151506140040c1401494a038000c80180c05194442410020500e9600200d0244001120301901c040e0360009070482c2004184421070301c001d090300341404418010460247e030310054016403190150702a021070344802c00e0092a1142f1702c0500b801d0391110a007084080c143e154011400c8500c540c105021384000d4a181e8003000945014a1800c22860360052012820000090000400c080b0005103440c000001060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 387723678 1250 387722428 387722437
    0x2010804122307050c010206010e150103020408161418040602090102010e0304030c05090a09080315030c0a2c0c042d0b03060a0e101e08060c070b01060201140612070506 74
    0x80240d0700403c002e01400420003041144020030700040c4025414030550012020300205807103003000e43d20020b4811640300e074060f20010110401110051000d010440c1d4808200b40201100c0c841c0f59260f18410386000d006a486141c0c080b41000390a40365625480301a512080714181590f40b035014005000104000410055004408200b0707024200810001d94100142ca41052607050410360300c045100442201e40082445204a80d140701e240013090030720003c4801c469110815070000540d080920715060722032071542200904400c9841500301060381c0507100c4000020043c80280002d00002200905038502c034004c0096900c1503410303039808001e4640007180054004024404141000040d4102030620400b403c0c400f85404910100d00002500c0751001c2c1c5600381501000c80d1205046100c0a4400d603000c0d20520300c0e110032a14002d9100400880d8484409000015010310621079141118603003199200d80b900e5480421640b20307884481d115050207104070001d255a5141c0c01003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 387724928 1250 387723678 387723737
    0x10b010f030e01111c0c0807090501080702070b0d36031d03071401180612021615020a020d0809120901120f0e0c0a0f0314070902070308061c0201080412 67
    0x540d8059685c480c40d4058a907405070ba681807000f0342c01800a07558003c0c440d0815a036007881c01c1d2440da9101c5208900d028410303070000c915a50001211800351502c0e0300490b9811310340c03079410840341c0c0545040100105a1b000c00341c0308504c004280d807001901c11041d10b0800c000000c403a0002010076000241001c0700f0b0b0340001d01c02c180301c030600ca900d560002141e04144180329650320342030b80380c0040902040344070403409a10b16170004da00c0081d41030080b4841050707a001260a040c103007030f109402000f0b6114508040c05449081c1c8014802881400c0c054810142200500300000000030100e0840d0030901001c2d042c05204075203640c00180c10700c105008031001c0c1401080a11441c82c009051990a1390405e0007154141d0043c411540072180450072658044603106282d42010001410302c10103400403e45180009180c1c800d02d9840800180244000c595100268150f8211500004810389000317001c6500140094081202103040d130040708214200007500c0ea50030131105194141000c0358 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 387726178 1250 387724928 387724957
    0x3050408010c0f08060102030a082a0f070b130f020f0d06230c070b06090402030307050a0b0a1815152c01080712110402040e0f0a0e010b010f030e0111 66
    0x883c1c5407a900c2082280c1000c02800914a00184050300a00180d030003418100c2e480b00c60130f00300215041c0195100340d100b00c0c0224454a940d80342d400c408140e840f840041d5403090400c03005c1410a02c50007c6405015880790a001c40044207600b40000ca102c64040c65900040510060002c01c41038040d00c4007010480f4484041261041000300ba8103070b000e80b0005150742d080c4040ca0001d0131356101c481c2c1103841169100346945d95032001900e1489850001000f500803925040100f06030000d2460144c540300e4030038482c0080d080360b0301e014909001c0d0042c00d500000d40b107251216545a20010015021401c000615616070803092005c41846082c1405d00c00c3e0b8503500c0b6808004c4042980c0948500310203070003850f151030b001801c03500d07003084050060003031080703102160b984d290b040b40d00608854401c2c0d40a0314100141d10310004046803446a00c9007030988502c90801d06104159091340141c5843d000c001803900d0840041c81c5038045003010b5941c0300d0285c8114401d10025104102c45a480c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 387727428 1250 387726178 387726197
    0xb0c1309050603120a121104081501290a0c0218010b09090c0903060c0a02010227030d030e031c06030c0305010519060302030703080708090a141518090403050408010c 73
    0x41c9441c02c905281305040c2c04800784030790003107203501001c1035040c2c5000a00125070300032205c108004500c9142e000314600c9c4240041c0101080a2007034060480c0ca002029400d004074403000c018444140501514046800700034822189004d9055164080d002900312985003099044000c10ba07142030f049284404c00c04580007109151014940fa404038178004454189005040460390b0b550000c0d200c240c54000c003203480c85000e03100354183c4420703491300b66210b00540401d840cc51080041c84c900c9038060b01441c00542591030080c003400314030b52034200040d842d0000d038081100750368404580341d0060f035444803400404140000740c00c10185000c2c800010b05401c00b018010400400c0350403407aa901d00300001000035a50210b100e9080b40d0f0441d202da95204d000740345c040c0d41403140002d1143d220306251030202e0400559988000f5058081d100304d0765803100900300c9015802010700e502c07c2c1b1000035207540e0940c00e112a105801611034180b103410f00d925007014a09454982c50049c0020b4000700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 387728678 1250 387727428 387727441
    0x10b030111090604050f190e040228050103050a0605060408150115020a030806010c1a0402030f070e0105040f06180207060507170a0b2404090c05030c070b0c130905 72
    0x20424081c1040d1100c103070301d0a502c0c00701080301400b03548182840b0780d00d1401e0041040d11241001c02d1612038545441c03201e00d480e41029104244103a0302607025001810300c0e6140c2c203400518442482695500c4030078140d140c10011406464000d08070822991140780c00070707039900e03203801401c003800002c2d01601c0c940c02c602c14a032444100c1644000414648068000f0102e5004564200b5054251600c1307480d50b521000103844040041000900a00714144000d010400e1041424050b6101728162030041948001c0d9540c4d0300190b0044020f00c80d00d140c0100440c1c60300e0740c440d0b460380c1c4400343c011880716a40c45600507031400001c3c1103010f80f80c0001e120801c2250f28031907954003a0303060416a16000030070000b410a010b0060036540142d5035044e644c030750341d500c02c6200c2a0709520107000b5841440c45000c42107264206110f0941c00c0c03400d05c68041c4101e802074059901c10b41c841c0a2403820042261110000408060280880c488003000361080b0b0b81d1222200c1406804052004a80f508110b03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 387729928 1250 387728678 387728681
    0xf060705030301053a081303080c0105090f0d0e03210319110313050a0b07182301080a021c02040303081308091e13090b0f01080303010b0a1e02010b0301 67
    0x40400e03444061000300e4400680c10290031400721703144000f8000c10200c19807801d0040c9210f1114241140c561403400001040000700080040b1100580288071540365145400e50f900040704803400250042c41c1c4002c0d06a1042c4e400012807000101140c1e0030081b01912049001d0340000d220aa2541c00420071141c94000205c1010a40c030003001000f140001800076581400701a040f850303a0f00701207603031400780201080480250341e0800140c28107824201000382105020f01d4004402c40c00d0701c203000510b091100045d0b030100500203803000b90300030082c004480c04070b0001d0030780800f02d500b800300c05480d16002c801d04d400003d00d1440140c0c0d031400d40c10040d01d00304008046051080401c40c0c4030001038504400d8814686003500e41c41041c84031414418505030707094007000c0c0c018000851070384c416605600801c80c21400784800c807600f0f0b2544e4412080e0b66000f40103606080e030041004000800d103a100910040b140c41c600140b8141c030b20440407034102001e543c5500140e44406415030985030a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 387731178 1250 387729928 387729949
    0xc1e031d0601060f03021c06140109270b0a08070e041a090d120b03030f03040c0b030106080f04060b0d0b010614180d1a04080304030318110f0f06070503030105 70
    0x2040d009001e10342c5080700041c25010303081c510808154020035512082a065510307030b02012907810080c0320b82c64542014200511911b0315081c0014030301c29000620800080c01d2550244a201e1003213070404280008c0d0010306481035800340c0110500d200041c2c5028188038841c0680110300c12180f142c1001c7c1040e1003d02640c041c507031840344100c000e0156a0800050543d10400c50742004e030040405800680001c15442558503007501000400031078144401000b103100c0c07440b800d58514410b840e442070040d40c3c0402d01800010510307000104289a2203500c00d940c1c000c0c4a00c9020030031000a9001c58007481410804440c101305110051268503040a900045106502c1c28181012040c0031042129200d094200d07004992598040c01400501003000c1790903e06032010443c2400c0c140b1700300e005503004442c140c000a00c0c00740b25010144200705070003540d035080101400e00001c00010000094400c184041d8404015900c2241c04d40781c00d0003070300c404c0e0b01400207580c403580742405011000c0035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 387732428 1250 387731178 387731231
    0xc06050a020c06040f050f03130906080610030305030901150905060f030f030d02070c090912030506061c180501231b030f0a1104030b061801180c1e03 66
    0x10700010b026100000384550b40641c00224040903200c050a1172400c00070b8080c0a25442e00000640720408102440d00404540f40118208012a581e003921a22044103481d505500d525504041011030301c1400510342007000b40b0300006260301305152040e41c6102c0c2c0c0e440039030f000383c0f40c00c200701440c642502415a01e1805070040c1c240212100340144e02d9201d00c042010083d40c1c04600801880000a6079001514001108100c0d0100c07500300882609a4031030320400080c00c00c0002000c5040c11410399010702d10303c40040c0e141c840003202c0c1c04080c2c051211050006481400e20401107403090044690458000341407182e2003090303014410003020001c2c131044011601c1554810f2820070302e402c85e81e009880c02c905201c00d4880d4200b42d005070646a980c60681180850040213009a08800754003414003250b803095070540007501c104030744009106840340500e07480041d42603074400d40c000201d03404c11f51402075400d083c10300800c071861040040183c00a60703207550b00303200c245e000300c0c0031000e502 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 387733678 1250 387732428 387732431
    0x2a0103050f04080412110a060e0a06020102090105090d0f0c0e1b12041407030c08010203010e01120f080a0e1507140a050a11010c020303180301060909020a1a09060a0c06050a 76
    0x19190321020050721031307403181402c8040102075070014001583d1060030142002031100c403405030f4071440200140002c1c0d4125204070090300000490340d005100321000084180c460504051a800c07c001e0420220b03501030b140e4094101c41800002e030b1300004d241c060035510811802ca81031111203405680d5070700d0000500c5540800c400754061140316103c0d6031142d0310203131038420f1034a43d050704c83c24800e403544010503d41079078070042040c11041d009103043c0c0f1420702d50350050b6aa07800c4085e403084c2a800c400b40c5803c0303000441d40301003444800104540c56084c10229004444000410b001d1011034005140643c00071900c601080b88111000202083c0d42e401070494601d103841e5a6120300d00c0442c010b2000c40c5003840c8200903401a40f001100310b80050a41c0d4542800c9880c1194603084c06900c2ca11035481d001d070208101c0000e01c1100040c6402602c00c5844e07600748151921802540c0000f10303030200d400c0c0302090b46903450f40d0040034200d605944603040060b107031a051041e2034000e40420b4016 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 387734928 1250 387733678 387733681
    0x6060803040b030406091103061501020d141e0f0c0a050609011e020a030914010903080912220503070303020a111e01051803070f1802040609060804052a0103050f 71
    0x1d002c44802d0320f80181c2c0040d00000c1a0140c1d242c88019941041e580d623405000318003c000007448613480740300b030313007402a005d45100d003100c0f2100315416556442c1d04504160144040c1c0c290070041da00102c0486c000b041180d1a1041070800017525800001c8191040e50290b049542006010b01005070000c0c00603009004086101c41210325a035803030203468844a60119140214038031030703040000180d41004a0606103001c4180b02e43c040c088040c0190040341c0b51001080302e071000091000c45182407411210308088125190f2130032606a6801c0705100c045c0300401140c1503509014500c0214460b40042103103412500c0c0000d8071581483d605482035541300181344140b002d50100000e820405d103806941c5200352043c1c1c5024110064050390944510100891618040c950f144140d4150f101c81d000035805505260003603120b68003c12000030510030040013442d018820b11034106105400751001e102c44a2400c0b21035207000e02c15194500d9900740d500e4207039600343c40396903080510111021110f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 387736178 1250 387734928 387734939
    0xe0f1c14060f2202191e0605030c09010e1c030f0e1503130605040c090605031b10050d0207080306010905060a0f120e100b090907060903031b0614040606080304 70
    0x15982c010b290150b0b20140003044502000f1400c007500e40507034020410040d004400301c0b070000c02c1d030441c041c0300340c6003080250394041c81540300c0750f100494002c0d43c0c03003a00e03503603440503c13000ba80c200c455500d0502c00c40c144100310700d643d0082510080d85c00c200c00b2038000d0030181402403892400308420407d1080101c0202802d0301c400032124541401c1d248034581c3ca803122943c09010003804540a0546441c10003071004200f4201d03002c40860f210358405014180e280c208058940405207440d045c002810390f00c59107641000046c20085035518200f10307040480c3c04540c5c1c8160307445800101c032803000000070000b0a60708144102e002c0d06050b100c840c1002c0e80d909000e8451840c404540c003d0002d8a044021041d032540c00c030015074407052081e42c0e106501002000c4c080c1c00d4540001e48130b86112000254011030004100040b1500d42d40c82c0d5050500d180c40556040644c0103d40041242c01884070020030100c1c0a100d80c5680c0c40312181d0000d160034140001220000d4100100942040104201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 387737428 1250 387736178 387736201
    0x703080a031b0816110a050d080a061d040212060708010f150f11030f040803070b010b07230c06040e060f01080702030a1103070203060928020607030e0f1c1406 70
    0x82c0180c484c6450b42c4151062a000e6545803544942591544582d4600104114021881244240b140d07111740540c0e444040c45030098404a000e02d0b2001e40781d1004074096821015a0540c1080c005802042d10380c400b03603003507070802204680c4400400c000714010003031a50f2500c0c0710740017403046804602c0603602000d0000c01150310429003504104c0c0c40c000070244007000b4021218240261000349580340c0e03464400a4894200c00c1003550340d4001100009801100642160319160340942e02e4400b515011010f0460050f50364001449442242038010903511020010800b810507140005410f20380340040290300e020b14041c02d410450030703900b03004100342c00200340c8000c544a410107807106d8240034009451406000e2021358944103010601c80031032000b241903003452078490025041a0020240d1044284410780000e4210307100700064000b00c0e00c41d181c616079801c0000c0016648240b888002102c00e92811b0820b41c070144105660401c02c82004d07004240181c40b000600a2490500030052 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 387738678 1250 387737428 387737431
    0x20904020f04270c0e1b070503040f09021810050406030e100f02090a0803120c0d09060504030e010f020105010302090103020d2a181404061d0703080a031b08 69
    0x340100018450070640340d5854012418004091204456080305410424004040d5030f10648800012000c040303130009000b026944903942e41c000b00c82038020160b40141041e07000b45415a0180020f01010940090002410700100380d0f8400241e150840003c40301812002e0480c42840340508411600321140c112040c0d42c2190003606000501c1411942164241224410300c154802e103000504018540d40340e0240042c1c0e40190b80c0314568940b160025a81c078818400036100101c0c0b4000001d80c4045c0f08002003121121a103408104084d041e030b642000c0c0c82059601300c1c045828890b0340641c1e560b110703104000509840c40203001ca5451034001c140f08940c1070202901070500e180c0343d0014000d01160040010140c0340030806c20b080140450081d40c016070003440304500500749003284a92081c0185000c0c0100040c05180c10b4540d5a600c00041ca804909165840310540b07040250708020b00040c40114040d645045e5941000c420040469800141c1090000d1100780084d541680c07085103c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 387739928 1250 387738678 387738683
    0x10f06140a05120f0a05101508100b042405040c0e090c0904020c070807050a050d150906150902031906031707110d1b0e0112080f0c151e04020904 64
    0x2044210300c0d01c03285908100d06044c034100d982c0700d504004820071000068105503d080d10308100100190034644c88401d0b0360504c0350442ca0380c000201c502540c0a50792045041e110001e1002800400040700c0410344101c0d004102070031500c0d94410055401c02e8011204505000c0c507103c041d01240350000b4004400280124411007400f150881003038503154102d42c543e08450044402071a50307007003020384d1500c560080601400a1740800602c50400700000e02040754885041d0303c011180101000c0182072880301540c0d030700c0d2201e81c08800c0d40b0000505001900c0d403440f0250b030340d10b0840e00e0300c0d091206d140030350a181e52501c0740c10808620820000180594034000040ea07403040e0f81003809106400701c156580c40f40c28205d24004010f580c81104c984d076034079421419501030740c961b00c0f04542502441944514102e01d0b40150000300304800600030480d0083c1c01d2400c0c0070f58503040354580041d4007035288403500450b052003003c61483c40b048208866441c240720f0185081d07404100c075005c000c0c000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 387741178 1250 387739928 387739939
    0x20f06062409040b18090d030507050306010e0a0f080d02060130030908030f071e02010e06220623030106050703080402061605030316020f060612030f030108010f06140a05 75
    0x21600b0598a43e0407110315404002c0849101c0d12108480c6080b206041c3c0f1091043e20400404800207802801418805d208a4840d1415540c803000199407529120124070b80c4003490355400f191500f0700c0b400c01c101034626003005110300c5c680c03007401034941041030304003140440312507009842408ac00c6094900c19041d848403003001d0042c902c0c0070b8614050b2504003c045001c0800d0310542075036400043c141060207a002d5400420030f08280740300540c2c2c0c1d144040d00050280708464590b080c500003c1c0035204880d070046908c1e010a0800201d01080c641040740082c0f18014107190008240480b6034481e03c2c804002495075140010250091082c2e543c000d0500c01881d00003415980c1e25415038070803c19070f6641f40007514040c6030668903980b0403940718004c1031200a10001c040d200194282d14041076500400c4103445810030008104d058a07881c82072031100700002c1c0c0c804100350020718000c2ca402c0001107140c0d207001381e80c0401c2d86c00b140c10044191010652000c036940c0d070070483e00c0403183c06544 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 387742428 1250 387741178 387741187
    0x1020714030a14030f1c06090207020a09020315030a050a030801050108190b060d0912120c05030a1104120f0203060703110304020f04021e090a06260a090b07020f060624 74
    0x40c03d600354043c4810501180d003000c18522486a0494078445503502c3e500c2c41040220749540302d21040b0b00502501035005454401c09101e086115401581c011a501c041e076003c40c07041400182c80c00014403821501c40d0440c500c03490400d40c2004699000d0082400c0185491601000003441a43c004440c00b07561920f502d02d48845403100c00440d43c0110901e2000d010000d041c3c00c4c542d003020b424400d01400035400c881510030302c4207588036140502400b07a40b0304d4038646a104005000d00020800d105000c0410400040c401d03804030040550203100b004588034541c0140109420444020900821f25041005c0c00030951a81c4007126402903044581030301c01d55110b000f08000f4013034510b02b807000481404801940f1107058002e44030440084448005542d15030000326110482680003021030004a881000c45017203a400c2103510400320800000c880e45680c58041c0c80440668401015800c001c01388400941c091000e268040002e40382c0000311410001da0030754880421155074074014000c034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 387743678 1250 387742428 387742463
    0x31609030803010602060907050303040803090409151401080c06090f120703060204091d0706050412052a041a010509150f0f0405101404051e180601020714030a 70
    0x100404003540d04945425100c0d80c450030060b5407440155400f5016100b25800000c00345000001c0718141c4811501070350900700b03418180006044003c50465040400d2040c814103440c0e9407044641100740030184401a52400f0112400c020001003418000c4908000a50190310303034018500215009071961180f000d687c4d0380540c00c3c0710054100410042c000100003c1541c85134224031500c1158040401c400b0f0044803445036501c40790300c9100e010440500040000109441c1081c40c0d15001c0c03000d403044903000c00440e602886105440400020b000f2401c3c035400e0805209138640c1c001260710314203210040c1d00010b44180148030b40307988624040c500384695500e0302001d454071402d4050099880b529800a2440c9035000740c0121406444400350400f44140704512200f400c00b56098441e11b45824038050040c0605201648800c0d50b404851103002c070b86a503000d411014002d20300842060529070002810612154451010f4206000b8040c07801e503804a140203006500002194405c03580b00d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 387744928 1250 387743678 387743687
    0x112030e030c0901060206063f100507031d03070c0b0d06050a0e060102160f090213050d0b090c0102121b0109020901230901060f0c020f2d06030c0316 66
    0x5400243c02c0480d41c00001a265000030b1500d000d410100c80020b07804264400240064080c1e9041075228080070100212141d00b03007030a252409850401c1d2005511b07956205070583e001138840305c000980c2d0b04041e011a003e240c01c4102074840b4440036601c0e02103582c880346e45c2d085190080030030b000800a4034100c0c084a503405203000b0304001d4400c9640039900d0408440c0c007041160070b5805030040110101e206d40d80105104156250220849000342c04d0000a80081d0400c229185a0052141000c1500e030781c0c80b880c400b00d1354400c1c04901001d180650780c060500310030002c1d403815940074a046800300c001c40c0f025601c05071101e800d2100c0004c0f82c4442d050141c41761007006074000e1b805d1800451032200003000c10f403042010071080c240444aa10500021a900348924400070320444480c2c0c0710740b8498413900f00c3c00e90000b03004003a40b2805100140c40030026000150b4109103880d180c14407080090a1001c102c1c400b21145401d529100580541500c8011700c8601090002604111602d024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 387746178 1250 387744928 387744943
    0x30c02030a030b12070608060f010203091c051f02090109050f0f0402030405070f12050106054608030714010b180a020415030606020606030a050d050a0c1406070909050112030e03 78
    0x56130115280346607120009892240f007070320054040c0c1d082000480326940000b04461660740701400c91191801d012104540122064804491070300030b103e804000c00b040ba1520402c104440d94005a0380d40d8880005003620005074001344c0a91181c080d86031046c0e40d11401c005000d041070390301683d2036589151040c1450301d46e0b0400013030f070201c40d030340810507800003801618218840c4008204580e00da1041160040843d0054040d049104c144c034003100100f40c1d02241d9246100780c0303441c1c005400c2449050407040d00d0f0801c032407d40c0085280707401d2100f6a0b600703501811071180204060343c00c0e036020810144000d59076101100c800300c08070305401d215a049400402c070000b445a40e40564680c001d000d4842440307024014450b00f00461400c0c5004121010500d038817000905001070402d0342a01c0395009124140c051200098120000c914461403d41210003e140607204601c0d0910303000c0d140b440e03150020103000349085c1c014882c0e403102c10800000913815041600820681e200040e140044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 387747428 1250 387746178 387746209
    0x20604030506060108010e011404020c210a121107030c0305040b030a1a061c0b0109120c0303030e0d1403041e050d02060903090604090e190b0108010c030c02030a030b 73
    0x40016001003801400b14207a4003504090344c600c403003660b031402030907030400082c000c15258001d18080810149040e600415242c2000006d94071a038010b4040b00314800214071000d43d11207400241484544e42c00000d841151075400000c11140d20500322035801d41c017403440f004050100020101c0180340c06501500c00800d42c14056690f64640409180d02400950000208081c01003084410501e40101901c000c3c0c140c0101540c00100102000d102501c4034141c001d06002c0041c03008110104020b6220706143c2c040c000400c031480c510300e8000e049500307090501d50765802c50034190a0540d800500b43d038600d407c0b40102c9403607441c1d506018500300811040321040c1c0c0c0044946400308100031424400c07843e129000e440e20f40e51950001c03516480346140d416403000c01004207210300400c961084507000e41700412141144203d03026200c690303032039140541c1c05860a000410803007009024442d5281c44614051100006052029659002d00300600080c55181c42080402e80c039400b1140800b0310 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 387748678 1250 387747428 387747439
    0x20030603030f030903091003050601020a171c0b191503050a021318060e153f120f0304120e0303190905040b031504030c0f0c08060f0f0612010902 64
    0x140281040c0e0781b40d029070441030050300c001c540c510fa004e001c0d1140d584a00b07010780141450b01007517a156a442650092011580c0006121800109601800c2d02400c05201c1100040c070407458801c028414400c400046075030300e0746280600c40c6004080d0381c215042103078140411503498000c1841d000e4000c0c8a414809107903070030400101e460901d09025001c0708101400c20507280c42e040510300a11040f40e10304680428100085680c0c100b11001800560010300c00c0301801c90100034160200b00b66010a49090306d80450210700a0410b204075203981945401e882c1c6090214258501d241c08000c00107005080b81c4039511300030034000c10a8514040e0010142c950f200000c00144051569076007c907400100c001d40d0110351410325205180500c08000c1c010305017018585c420300c0c0b65540040007101001010110a000100c000280da0344c1c0e2032190140007180c070b042c1071006140080c0244101c0c850008041801035030302e0208459500b2140c01e81e0250440004103200038054103516070020b4100317 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 387749928 1250 387748678 387748681
    0xe1005010507050c10080f0f010506091212031003050d0801060f030905210a140f0403080c03040b0705030304060f1a040b06041a04150914091b07030c110420030603030f03 75
    0x2246c0c0880748510030904021804c4e42a1280000c80d0401d03207090241c01d0700301c2010803070704602d481c28043d0383d008a58982c00301c0f030003198100700c41c0740c054005980740c200c050300348401802000310038085080060258500740c010703507151070b0b802071009840f00303130110a0554441d1400c013408420700204981c1081c080b54014401c011230a80356083d8031171039107000000d01c86441c00400300c1d0381004071480e90b80c49800450400713080d525070017144d6000b81300e40f8071140f00401000030f14061981c0a00034840c080c401541d2a843d00b400c00344162003142c030340c4030000b900d0b0000340b4000c0001c901d640c842400c0282e500254010300c180c04100d191140d0f82040c0302c1102008081540d4040b18030007442511080c0487d02c0c201034502406554552180c01104002036200e02a041366081000c0303c190302014146c08032001c0c41c83e01d0100700c40c1d030b4408101034001401441c1050280151080400c81c446401e0b20100090059603552490580b00901a1000381c03600102013581a5000c105690311600740100702684c9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 387751178 1250 387749928 387749959
    0x10b030a0608011a0a050307030201120e030c06010311010306051c11130f05010305070611071e05040c0305040303060611030f030c0d06170c012a020102010608060106020c04060e1005010507050c 85
    0x3080c0018070110700c240030301400406c2605000c51984222541070711880b494007000154036020340000f040505051100f4000b030203044604002c00350003180522002d600103041d020004003a290030781c1001c3d011300c012000f000d10706190b00454100440d08200c02c00f64064002c8000f40c4c1800c5502586408030341000d0848100d06a96400b007130480c0d102d0022101200e5440070b0070388810003458030004d49600404001c100c0241115152462039000c9090b40d01c96079116400501214044124800003a07944c0782080105500342c0b01300e402505503810300e8010810b98480713643c2c0e030323120703000502c51290004008910280c1d070403c262001d101d120b0200344030035601c814440503d10888460b00459100301c01541d55254082e64012010000b00549000150b40f0303ca59601d05100c005800c0f41190740e10000080d10900521189028198580c050b000c0031010750100019103000390000c0c18040c19400600800160b103101304003c4800c21700700107071140301e00e0074440d05107403144500d650441d4094900610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 387752428 1250 387751178 387751211
    0x20a0f05030105060a031101080703060b0f0403051603020312090316030503071203140105040c021507030e0d1106070c021201090510050c0304030c1506090212070f0503040b010b030a060801 83
    0x35100d05a000700541d99802c01003024921641c0710250010340007103a07000c2c4952054015580c80300c282d04010950720750f47c0c0c0504c207140d4000811a41340d00c1002c0341c181304021003400221000801343ca09418014155000a80c0310050410515944100000c19031083c0e14240b002c0d000c108860b50207214100d54034200542c4903408100101da614034003146446a15002e48541d20350140c0f140e60781c1c0910b0303007058284401803402e4007001d42548240e03011034800ca80c1c000b01e441d216124603500811040d1140c0c3d081d9103400c413100c0d00e0b14140900d00744230f01c41d14080040c400c0e900c5202d80c9010a440c14003030000c6054800c2c4c0a105007019401d0110050502c60700061640700051450402c118955505000c0180d6000c140c40040000c3e02e21440840071032200b00140a0a20850000180b156910141c20040782d1059130500d049980c0c290400c00302c1a00038400c424000f02d82d04000e07240d86403d560300e070801a03050040241131400400070982800031544428007514401d0001c005844a0036001e20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 387753678 1250 387752428 387752459
    0x604090b100f05030f070e0607030e01230d1d0307050109020312090306040201030b01030b0a06030509161503022d12010f0f03110d020907091505090a090209030109020a 74
    0x740035140301048506224401d4111480741c6625a403a0740c01c40c0c54000894600800250068040066100301c9940c20341e2540f00804186100b602c4101000f000c1000240c041c603549480d103100c583d1004084440808030030b0450700c0301d0340c14580010f241075611807000406086840e26811a100104440c420801e055010058881c000c40c21102c0c441101900c0c40032600c1000b10141d050341060020034010f5001c0e81140d11481c1c4141004107200b040d003030225444441130742c0040000303601c41092200e216018001212041040004008118200f503001c440340300507261240109a400a0460750075170100000650b070136151268061030049801c449141508038000c80ba00c00c41c1ea40000061040d400e038200412504402c4004000c680b4588401503041035006080340c0000c14001c1c200010b94401d48158071810b4a501c1e4200c3c04c60818002d0f40d20401c20065034028040c0401081000303030f0f545544d010454000c0c0c42c015a441300740d04042800340024440094010745d4070b0502240d5040e4848012 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 387754928 1250 387753678 387753701
    0x6010e13230718050f01090623131409310501110d0e07030201120c030212090303240a050d0f0b270102130b0906070c0b0901091401022a060409 63
    0x21050f41d154000c2000800980c0c040301d010560b080b004100c100d0007082c5482d8031401007402e525408400142000c0d581d40006c0141c0c000b065254001c0c018920001c1450481050076108030380e840c42c1500c1822005071007074001c902d8409480c0c03079006080e0000f0081d904001d40c850300034001514681c911020350782101900151107403d01c1029035000030002507800c01c4a4050791034031560548440540001c14000101c0c10070150200888000032079550223081c0948a4400203550301c0c901007a01040c00d8500e043c610000c0c01d14407409504d00c0c1e448a001a059400440d0480100d60795031614103240c501c4c5590042c003859a0004208803030034000c090308000c8828441510850390b80d003c24500700d1107114030381e102000c01a1018020f00007080c0c00b0385014113020304242c0c41c00c40c99851380c4c0303019800d940c4205600040061360074441e50784a0b1511005010158402040c90030046c00070791200e1103540c0c40091214040d4801018402d02130b2200500da0003d05107070b96071038607031140e68040e04807042d09 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 387756178 1250 387754928 387754967
    0x19060507080f04020102061503030403020d0c030201140f030f1e07090602060601030e1e16032402030402030a02090702010213060203040519081f1401090b040506010e132307 76
    0xc2d80602281207418403a0394140e015114a580d400f0340c0080c100c20726418190180b20074000800140c4030044420311050117256040d1840b07246100042c94145031815802551200b8030440c030208030024103036034100d4035003400000269100706011010600c2c0d000750b03011800685050011140c1c0109110085c5c4240790300f030303505d56607903400150103407840703080c04143d2603000b000700a13000c2e000b40c4a41c4010000743c500340c40f0640400d6132240c00902464006464402106200d00c000d11039100c203205444074004402d60451616400080d20348030003090190040c1d07203da00040c50b8510030740c1101c2849800c012400c0c82c4036100c601c0203550b43c100f400f03211702491141c24400401d204e0344c1014000c44400310010101c2c0622600451380020340c0306031100210341c2380c90001c01e1081280c45240e010b0300800e400064107800000400080e00c0028040c14141701c1c0d4000745500a4541c07240346000403a004001190001030381c03080901002c15495040c1d00c1d846c40360180281d8607400544202c50065080a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 387757428 1250 387756178 387756181
    0x81801020303061804080903061f1406030403120f0c030b01030b120a0f05011401060806190e01170a0c030302011409120405041109040f0b010f03061a07051906050708 73
    0x103aa60b44400d0f521581d10101c62450034000340301d8600c055038000d200d54a400d05001500707000c646040c0c416541016060f8500064201d8201e158560f1720052815075400c00e1f400401102207a2a884045c0c4007808001d041d100381c0c5480425a00840ca0400c04c20008014002d10240024010b125040381d0030700190030680100810701e07140c40c041d1100b59040d00038051840c01c503a150f0000b1400705004032229500c42900c118035a81e60141c15000b03101c5d6442e0001c04e450400100213008a00b4000b65400840c0114244080c101ca010403d041d501d01406041026140590051511001c0311005000300c2141d1030200405a042d0000d08100b80c13030042d412440d4a52140c41c40e05c8610030610740f110b850341403104001c18545504400c104520700b0407180d01d482c0b03035080445c080d568880620110180c4580c0c0e5103410b03503800380c0000d0420903245403c001c0a41004804075810101c1c4480380041d000100d0700e1001d000c1d040c070245586c80841465403800145610300203001d1300080717401402007446c020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 387758678 1250 387757428 387757477
    0x3020a02010c0c020609060a17070201091505150103050c040503031809100815040303023007020d0c08070305040521060703020906070f11060a02160504021c05060d02060708 76
    0x201e000000c0c0e4010107186c00c062449040c030125410038046034041003800d840803028800c1c0580201c0c02660700394000f14502040d41040016101e1004030021458500810401c0d07a0b4507030f03440003e40b03440074600411300d900d03940e01200d40360107141c02a56142c04000f90303044a0000c9040c103840c400c4016030360302065a40302c05482130021514440e82245030407800d0901c40782003034440e2150f489486400c0040c2400110451030f40190100c1c0a40ca807605074400c1d07904c05001c41c480c01203034000c2c51480100707040103092a00070010303c0341c202c00400d60394010600300708041c003800c1a5405080c02801004440d5011a410201a940155204102e00a11020401543c4a4022290002e0028169a140540654401e40040350b0032200b5140907400703580603003441d42d41c400201200390407940204a08141204244003048003a800300340316a10422103406500544107088200540b010300003e1555141c5000c5421010702a0000b9400f8100048010400141c40007400090842c03e400c040564000d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 387759928 1250 387758678 387758687
    0x10e010221070c0f030215100609051504090e03180102011a0909070906080c0108130b07050a09080a0311160e0c0c0c030d020f19170a1b0303020a02010c 67
    0x20320107405504101400003500600c07107426540164062030201184085074403030a40060b034800b07046006070080b80c01c994003002c3c40d40206401803810340301e0240580ca0300c00041c00c1101548503060088020f0940e900040e0000415140200a0540c0500030740985035441901e9900808400101010725503407100035520500c510703070110b407480448582a105c9401005100e42006041040b40e1094032004241c81c00706000b0040208420002400b886407107800150102c2c10080c80700207899000b00810012035024070099810414608115541d8440081c08588601c059000060b0920900350103a04140d423000e0700b030140080c0c100556a0207032140b080c200b60a189889080b41000a80010401c02640700780100351800321581102e601c804628042801d05403034852050158011480509800c2002d00894480c100b005800c00800d2446070749401d0703903540c1541c81d6904850042240b604850042c015104994011841210f00322028940180650700c101c0c1010019400c1a45214410307014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 387761178 1250 387759928 387759937
    0x140f01060f1a040b030c0c010e0c131b0e06070b01080d08160f1b061a0a06020d1205060f2e0c150f0b060f03071d060a08060312040611010e0102 63
    0x41140311440c06203064000c40c51038102406d80d200107003003040401140b0509100340d020400c01400508991105041041644545000000c44990410302c100c2000f01200140500d41022800c1a5040301801c00c082401c0e4040c450000b41480d00c86000031464107000502d02010205130b5483e440b8a541e007910218407071240f800300c0c0300031608140a4102c02c82c0a00100c40c2000138008074640c1510081e1140c03001d541c140402d11a0b1a00c02075121411420041c5460015040c1800140103000c031078240240010310f00c2c0c81c01403089603120045000e55840c40c4103084d03541c60040c80c0303900c0720719a2902c05505c09103285095080000e5811024009406260100365180d040b00034811544903881071107016000044620027410b0750f48400000555603400903101072928211100e445c6d141c0110090070400010100209009a0310901d0715203503260390480b81104101d242289807034803858042887c044203140e2220068001180c0402d07030950000c01480c04800c034134003d1044c01034030407c440c02c0740304 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 387762428 1250 387761178 387761219
    0x30212010f0507050415081801110306040b0a0308040902131a030703150605041208130807080607080f0a0f0b0301051914040201021c021f0c08060406050603060d140f01060f 76
    0x1800da000400d1030084912a43c0301e008239100f1004031a0302c012607821100d001d0f480340300d40700d07002c002d01016080602ca12008510b054800c00078050460721070702c0d05d0740110310070781082e030390006041d14509408802000c0203103040981031410115454030841c142c2c00443c0d0b0070001038a00380e203844086a98030300e440101e6180d07464040c40d040c149801800300c02c94060094034200010130440348035904000c0307140c1c000c11005014280c024107141102e810b08a000e040b8030100a130303403020b012050307990960362034001d0b0404c00f00144072110f17980c40d90050b08c0300c01d540c2039243d4a001c04000c0c80c150506101c0e00c154883d441c003000f15214002020340718000a581c041d005911641810032114020442c5901c01d01c140e0045640745140c1c204074000d4a580c1e007041d00441a21000507000b0181c224521581260044138180101802c1c08040b8805000082c500c0e8403400b5503400900030300c410514042d540c00150b03402c2d184550f400e0b80030140030f009540f08001a80c0c47c0e021001520900c0051001d07060321 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 387763678 1250 387762428 387762449
    0x12120b0904022206080f0d1101050108100b01111b030c0a080a03110a2a05030c031c170a050f01080f0303040201031a030a051c030207020a0b13030212010f05070504 72
    0x100c1c4074190f0000da503000a4040343c095685002059a680030030071900311425102c0140f940d00c0c010100100f0800d001898000144e05000051003c1400480d4004901d07080c0d0100049104003000126001203480220100328000e04001000449541480024a0720150201c510486120781400307040b011a00c6946032542200410f2070019200720450705e2950300744006c171800c801440d16080c0d5201501580400c1c00881b03091451015001a40d184000f0003085002e400c0840704100866215500210b0980490911b24180e04030180590204000c41d0382031181d041c043c2c40c0417040d410091005035442c05d4850f801d20000140450300059204020714a60080c50071a02d9540c010350141203c21400140034599400781e42090300c1c03c110a1808900a4004181050f000840c072100d0030500065901018010094800580c40322828281250000d26100c0c0d50380c030110298180811003900300a40c001d07140000319510502c15008605005c102c0030080205842d11042a07590b803007184216100314 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 387764928 1250 387763678 387763699
    0x30e010c02060909090705060307050702030606010801081504080d09050124120b0903070803190c02060705070b0a020705011e050121030309110a0807030302161a03040f12120b090402 80
    0x44c18a4030109401218040441e000300343c4507070021300303250001c0700c030b5900103200030a69809610307040044a1300904d0a0800030144c1d41003038100b0340c8440300101c140002d01000e0010404003c28030049815041c004682002600d20310310700280039150040d40c00072034a40140380c1c16040b40410410404448141882805410300e55075009004607000342940c642c0c0c0005d11006012800d03e40c01144220290a0b041d050b59141c0f51182c004c0350742c810259011948800200300310769412004444580d40c208020314000d0ba91a1901c034064820780e840105030354248182c0600c62201c1c0d141ca00d000400e100024003142c2e03207415a03c5844041c80c1c10400c404030440344580d0100f4025480f4000090003240c000c8a134441e03400100300746460f294000700040d404004200f007819410b000d14a1842545010001c1030751404040b071150000c5c00402c41e00481c03001002c10b0801c8070305283e002049512468980c03141c00701c440060101100c9807440501c1a040070b1b0120114503100c01c1e09803007940e000b0b0409610 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 387766178 1250 387764928 387764947
    0xb0c13050111070f06030e0114010302100c0f02031c080f04020307050f0609090405030c0c040203060a05150c0105010308040e01060203091003020f0f0d0f0c0203040311011803080a020703030e010c0206 88
    0x2c51202040c1c05400d805125404901090800440009400f081e04c0215020503101d4510b42140c840050101c0101c4034000148016681d00e4180619899603181c210101301e400d08001701c8401103003030000d51501c01e800700e0f5480e0541078040d003650a102c54882400035614016210040d41d0202c0d00250300d6000080d090040c0d11f40b410902c140003802801c11400c013003480c400708129482c03c5c0c809485a03440403a8000328003d04211810381400e0956055040d8140440840c40386c1c1070790301034284a00c81d0b0018a150208a0100340c50b103601c03007000280030710759413420414030907071260242c00c82981c10076002064450001040342c103040809805200421b0003000210004e40140032099040c0d4000c003e00e0118990543c040c000c25031641d0740c001054005190180b04803400c03084404155042440304201182c5030a01100d12500282403c10309a102c0c808041e2141e20180c1004001d04004140d000466034009410800d991094a800810a030010015a543c0c40050b1f8000e60001f0100310f04d104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 387767428 1250 387766178 387766187
    0x303080a0c0e0618090c160609020d12050309010501050a03081206120f030c01050f060a171005011e09020c210403060507020607170c0405090402011101180b0c130501 73
    0x3034403250385001400d1900420000b89140d200d461106440041c1c10a404c95a10b08046002d4101c0241511503107804402c070110454420030a0003d0041c964801442065460700804194510303400f50300d81d0b400d0b21000f4405003c1d07410035602400c0640c039141c00402c860511050301019290000300c2a810f1140f040e03a108120301300108445c0e00b0000d00020700d202240c0c100401c4078441906406140c03142100201c0a003140c6004042c2107a441c03800050120a49440003800155286840401c4508080701c6503c0c1ca0540700c1c009080546141c130000140c100020282913110a0022001042d65a95200307580164010b5000c014542d40061882010001014001410742042c044509080c2952500c030310080310f000311100390160708120204001180d0140b607038002002c01608a180c03038105006c207080a4010350140d98052a062030219003968040c145424030381d000b0b40020721504c401d00c480c43c2d8000d19254170032034058080f0300210720350f000c414042c0e846000c41c010100032050f20b030200469 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 387768678 1250 387767428 387767441
    0x15090e030a140d1103010b0c060a0c050403031404030b1305010b03010b1e0109051003021306050f1603111b030f010b0f060901090801020a031b410301030f0302070503070303080a 78
    0x109902d9652010741030404c1e841d07014600805003046041d450700c0354505400d0a21a000b01442400361519044032511508074080d9030643c0c3d0140380401103c400e94082e201130713200715040a08644420270411641d41003506002034218401c81c000d00455081209240c241c1c2c9400921951080100b0320484168010302a0310300c1903a0140751600c601691900843d1410003030410744400a6000505400c01d0380d03580070144000c0c5881c0c50441d10f440071005d2580800e000d0b04a003403280982c22803502c1d051600c5140c00c009030840e040260b40d81301c2c800245814100e00300d00794860180c001d030317070a0407003484040c41080b202200240c2030912010000d010402d607076010050040c1440030f81000400d0903102440505001e940315140084c815100c1d0940c01c95580b203210b85a0100a480d0300700c000340811080040c180d00c2214020b40342d00e1041d0b94036243e19031a43c0c9a91010341d40b404000003040c0320070008031484480c041c0d02070300c900c543c50f0414551601c510b17004c042c01107804000810030000f11a484075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 387769784 1106 387768678 387768697
    0x21209030918160e040605040e0d1202040503060f040204110703020c190321091e14090103021f0201060512030a0207061110020f0d15090e030a14 64
    0x20460f04642d0101100300301c4070002407080d6440e590000406050300500a02840b1907407580d181e695040100e0850028101200d00c2c01d07180071910860301a980080d0107007250741e407100c0e400d141003007015004a801907074820002c56081c00340c802808486110345d0142c1590b00d1f1100820603038501504421303640e1003402e03200700300042c0d591900c105059241540d2900c0100812012758600c10942e00c80142c0c002d540e800c590100d54000e418600740c03026003c0c1c003102402d00d0000d000c4081c0003400000e400220080300d2484807038280c07045071035004291002003412900c600105511a0380b951031441e41d50310110358800b10716014403145010b0503003031401002c0e03a40c1031010590750380c44400080b422907030700082d000100c00043c03048030059104560306101901e1440c2c1c4900141c8a81d00c52104203500c2c041800b124080040201e4900a4495985991840c0112198403242d4401c1d0100c = true := by decide +kernel

theorem cover : BRFrame.Cov 387589928 387769784 := by
  have h0 := BRFrame.cov_init 387589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 387589928 ≤ n) (h2 : n < 387769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
