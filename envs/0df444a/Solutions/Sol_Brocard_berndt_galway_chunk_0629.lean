-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0629
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:49:04.782935+00:00
-- url     : https://prove2.me/submissions/c2818514-cc26-4652-9753-be1df60aab1c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 112949640 ≤ n < 113129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 112950890 1250 112949640 112949653
    0x50a0b060a082211040c0801120609031206060323010b0f07140a0c0303110705060702040b0103110d0c0801090e03070f0305040b03100e10030b011404090204021204050d031b0c05 78
    0x4001a40000030f1080d070150003610010314503603081c41705440000c05403c040141080041040d8000c0203180b80f0503d134010000305440903181812600c280344451491a000d1038481c001031802d42550182d001840c08044110084208810385503044400740300c1d5801e071903000c02000c2c1c02545824010045603105003cbd0030245070703169042500d411504082280c91603610760043c41810303040303021110100b003804008c00c4014103240c0480c51714041c1d5417000740100c4d100c403c0e15005078040c1e000008000004c1c01e080d030b129100820f40401600540d05081c011030200000412181010302840d001400c541c0300951030310416942e41104282120740544c00c000041c840420000b011100550280551662400416060410901a1800142114005040400c4200005018480001e04544440702c918088071a11008035002d04480359009510910000700c0a242a540d1540c55004900420844036800c0c0c100e0410f400300c1b4110380700ca02400c41000d45c409000c41c0704020141065202c0c0040c0c0d0030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 112952140 1250 112950890 112950931
    0x203030409090503031905010819030e0306070f0f0806090c09030a060c030903091215020c01020d090503040608011d01091d061302090a1505120c1e0103050a0b060a08 73
    0x2141d034034102c03c0321503410010a010200c1d01280d90305000142018003000254500750000fa5110380c6005060b1a08500450407400c2c1406010340c107001e550040c06580062400741c00040140c03a4140142012901c1d1408105071b1910886002c2d10542002e00340c4410340d150040c12035540d0300440001072b41441591800070000381203006c0c030318403a40c00351004035070705520740b03805401c21641d80c00960484410714034060200c0c06007040ca40140d03090250040e611501003403103030f0185c0300b50b00460b41c0c517a003000041c1041120000041c03088500c241c0d81c00c8221390700d071054a0344070483e80c902c5c0c44036a240003005000c851610351013282019078001a821544c0e60f816400c07408c101046520616904014003004190b08201610a61152000d0000c000d0b1115401c0d5005084010b4041c15004048480e01c0c41310100c800c0208001d0120000d081125494482d108450555a00d01d1175030700007810300d404a0a45410750140c64403902d0f000342424200950070701d08989000c401460003070800c108a0740c600307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 112953390 1250 112952140 112952159
    0xd080114030307120c05120c100f060b0a020703050d050310030b06030c1f02010b03191b0504090c080c190302060a0e060d0605030111031003080a05070501021206040b0312030c0702030304 82
    0x120000d1380358031094809406400c0403800d0030000154010288000c010407855820085215038010340c0b042c20015054959450201c0104a1900400028000040d03403014040d00080c1c0f4100b142d201d242210b80c801c4140c041203920b400192148541d504000c40c051000844a228155000f6009400c88546c98034110004115410070064024600903082d0750641055084c02010140d0ba4140c0081081e4095808065002b00b10303044041d010710610181d021a030807198184c03800800e0010410f002c01409801c0a00c0600b084e441042c0ba035124004281c800c40c03c04800c41e42d0300e49140180351603800c0c550780a100440d0f00c00d9101c00b04012042580304819520440a4406401e040100003441801e0000f81821140d0941c0041c46200040c800c100f14890030400078425640d001c1403150711403c040f5030945d2a4051040010310b554000311303190290b00c2440040c0e92103290215400e120301d00c12407041c90388982d40100991102c010810009040f1000d4400504416101800300ca1400c1d94661001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 112954640 1250 112953390 112953413
    0x111100504080903060901060308270303210f04030c2d060507090603090809042c0a15020712050f0408010609091a010b030415061e15020d080114030307 67
    0x84411800c00304440d03903c0e01341003040d1548803060b00001c020103400c640b00d40c201ca010310200f01c1d0404a40802041e44d180c0d000080d1030074078a015085940f00e0004500035010100000e940c40e400d4050724002811444c10070001602640c0c16072182800111140c545c015409084a80c40d080a010201d10100000b07443d0003843c5054040c0301c1c002030710305002d80d0003402c1c0d0362283d02150401d400d1180300400301c0c0004049410901007124000341020f910804003c03c05880b00c1c600120030300b15a80c0d8211f203400496160341035071142803c1c0c00219444404131049028814001e8440103440300d1214556000340000c0440c82800755225081980c1c5059071400e4075000e4000005894035119500708019202140074260030103e1a02c41d015030404c01d89070840e01006001405141c00040c0114003245507602510151040001a0348904010b0669440b490240d21403074020300e90900407030000350300c0031034068034141071070703445182d039910744283e0743c04003241001216070501040044074009050b0035010b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 112955890 1250 112954640 112954643
    0x20c150d150e221e030806030304050109171204080709050105040c020303062112091507020d03080c0d0603081216020c0f0411031609051005030a021b0f1b040b09060111100504 77
    0x440c2d0181c4d2480c0c010301e06003018140341d01a900512043c09960303000014001a11000802c4007284d10f2500615403900c001114410342089000501003029000440c0150541c0c0310306405004599848061000b02d4001180440050f0803c0c00455103624020007100e80e84207040c01030b040c05500c00c0305404c0c00c1250b044145200e8020016281c0340c2d509102107200e0702100d5604255040c003206401141a03422030a400400f000200c0001500001000d000c0d81c01c000012041001030584038a00b107600c551191801c00448900840041d003208801031a180c50035502c0d0740a005d6417004c04007840440122007245551164032885048007802d00300b80514881e0201425540d807244003458042c14aa4581d00450b01440038001180807564000c03045071b070800035144d00165580c12811000c3c03070034200307a8020030700ca003e0005220440ca4002a0900b02440030840b4586501d2603501000201c2d012070011540058030074001503000e41c05a03480c04080c0c116401130310a27081c00082414201e41c02140e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 112957140 1250 112955890 112955933
    0x120c0305071e12170f0402090412020f0111041d01031707020310020a02010615050a021f09051005070e04020c0d080718261902060901020c150d150e22 66
    0x1804c0311407461241280d002a140f05c3d80010b181800d0f004138045590061001d0400481c1f54000a40e9501c200150300134101c0e40002000a1542440190b04603480f9105180d4402c448000300103c10a0030b5110768120703a44003071501c0c01d1170440e03c0544002d42040c1e03020380c2d040c01040a0840108110f00081c04c000c000d603400041c5850a250152018195505c1e47d01c003001824050040e00a40016800c403003d548214528284487c0603006009071814410050a80c065212080c2d91031059800c003d024001c2510345001466101d03050004902890b580e0341e241c3c0d0311440262580600400c1d1980d04180750b840c0440c180006608141d00d0607109030700840c40c5050904081910300e9660403403400c1412071501030139104107003d0300d000d41402c0265010744100c0000513408241d80c02005088050b00028110365101414050f00e2030540d044100c0c4031810b2420080c0701561000103090540035280030041000b099150384201f0310500b50414024010b014241c141080481d1f922504440304440846 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 112958390 1250 112957140 112957157
    0x204030605010801020c0105070809072603070b06280329070806030105060612060f01120e0c03100605060a050313020a140f10050a08041a0c07120c0305071e12 70
    0x140c00341c0c02c6440007030027002008652070a20409000c0464000200c031001d00b01d00301d50510100c24103c07502030b0750788004a5840009503660400100002d03441c812002102c54a24070251040c1510800c3c03500c0240815184000000b0300000380c3c1c20008140c0840001c0d10814941d9400c0e1400305204030541c0c4610114401408004261409016a0b1307400071013911868240701b0110000041040c0213400140700301c00f071071640442d6034429040184a130801b4001070204100c184030403500e400403801e13010300134000e0b42c2d0359850400083c06081d00329a0080c0107036107446e04440702141e00c0d4002030301010000ca20f1a04039400741c1c0e20549640c01030049420030450807850a01000f1054010f840b015014100302c10454208a0b002016140b50320f00d10304103421039641d5850b080c00d0354180c24034440c0c155010101885a050130000c050200d0520500034000300702558402903414240c400e80043c0040c0c41007200c100024010481124200e0f0814440b05180156503070300402c0040c02c1c0d00290000b20081c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 112959640 1250 112958390 112958407
    0x8031204061512020d031202130509010e1b030705070602040b0406080a050c0409111e0406020f1609090f0c03080d0605012316080c0703032d0e0301020403060501080102 74
    0x18031456151210408041c03042c24035000f410865444110300203485034191024010915000b0302c10000007441c4900300315036403031213100d0060307140e4403500405000b04280c0740049440560030344458029500703e488a8040e020a2000d1841903100400340c00402105116400001c0c0550014002400544d6216612141015001071040b2001407460038400e00300320070f01c0201070551044070251211441c01207081400c010050010b0f110740c00943d0300e0038a0250b001800030710044090300584400e41d007520664200540d080d41e5810801d94a108120040f1008010400143e40512800752045420f45410401d640b100000800d4981c0705940a030070000d00140f0400452084002500c02428005804c2c0c41c08840c580701c82e10007400785110014002130842d00d00500359040310340b550703100203401d0b03803400a64980350301c2e08542c0c801240480c3c0e1160300e40b03544280f299509201e40ca0109009516180305031822503100410008040e0555400c002c0480450010700070180030740a0940050b950b001c61 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 112960890 1250 112959640 112959653
    0xb071209083703180507121406100e13060e0703020a09110906031806190c03061206050a0204080a05010b090106050310090c050d0c0804060b030309060a081008031204 73
    0x201901c5408160382031010300303500300c0c800c0b240c803011489181c000355074141903070316810501d24044050300c1845003d400007440c0d0b2481402140343ca00c20354000c140e12010760202d0341e80785010703540103014140c1d60394280820080d444505500c941c4907900340666030f02c252140d0b404c0b02d002c00910017154005203014020350410411400080090000400090b0000c600c041c0c954003d4035240c0c0c0c8a090004040385100002c401e4049038000c04006443d010300701b140c289601680310720403465000e803c100300d0344045030007032058908988031017200000c82c80c040e68540000707280003031205030f48603800d02c00401c812104000200c1ea1502c2400006180c43c1150100114143c0c1640304808005e02001002652780000c41e0002c21a0807a4030b001c41c104c10600d00c1a526802004260640c151812084201d03050313100304000d0240c1d0040740e040010a840c41c060645a11941440c1c03a000307481041944401482507099503403007000041c41c50201a281d620a5056900c41801052016440802e2009101c0c0c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 112962140 1250 112960890 112960927
    0x302030a2a08010504020a1509060318020603100905010b030c03060105090102010e12040501090e06010e060d0605091e090a0308060f2103310501050a05070b01030b090c01020a0506040b07120908 85
    0x400341c2c48c150104410007000c05019009540826845582000580002d0040e00100036801003a8035100d16003040303021010141881448656802c1200000d400c501510440380200c3d04955241e18541c1c4000041d942030b804914620304640da40c0d40c012408200074810a80103407285400c0598891034200010244e104070780007a60640031041c18089560380041c0c003003152440680342991200d503210b5100d4001e0150f40d00868101814200708001c003e541914808480c09445178039240e51a1b00d1000e654407440004001e022a5003040454031900d0318a0041c02c01c41c03801046c0349922958a10084070064207100f43d580d03c2d9201060341e0348001c1c030108402180800030010440d801c90705208403029034501c1d104440c140200020940c803414403403011078031841e412200c00c1000e542d4a03e0000003486007142e00c44071a0082d80c0030304150350b01c0421040b42c0c80c0c2c0c108000b04026243e51300d0701002c5e520302a0400c414410302100c04c02d406082c0740680d039100c50042c002c0584412008035010110381c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 112963390 1250 112962140 112962149
    0xc09010f02011b14040e0106020a060c110a2004020d090b1311061c1803082202062503020c15070222110f07050706090302030a2a08010504020a 63
    0x2410f10070184005000ca00c20052500705600c1d103841d0f0401c48550341e1205204581100c42240c04110000c1481500080c03111600d901c1148208a01210782101b00c1d5002d82a91419481e900300415003030108092036a00e000c05c070020354050641841c03840c0058101c0e07018200130203059403204c10000510901c480e96581c0009200080030b021122a80c0b9502e01138a45814a13102e20408074030358030100a4149918882140701c58100130754807007001200032001c0000411000078450300700080640c0b5004010500e410786d80441d00b034004005a080003003982240002d1070071400c0143c03030b03c1302511210000b10f1519001340c0107403002401e01e6080c86070a500c00014080054070422070400161200c01d1036101c800c9030843c0f5100c250040c01c0c2050090907441d004140c03544404201080300c20300000050803600e1154084804540e541d081c242e99807985407001075850b812601c081d02c007007050500d01902e40d02039500c00503c40600c0002881800c05160020788550b9590001c10007141044071000c4040d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 112964640 1250 112963390 112963393
    0x204110405010512070c06390c0303090609080a080405070909030503040b18030c0115090b031f022802010c03051911090904141e0601060c02060c01050c09010f02 71
    0xd41080c0000e0520302c180f082c1244070011240c00034003000d00ca10a8110000e81c03150080c07241592100024907120b020030400b0301c1c002c0001002e243c240c071588a00d1214640591690039002d101a1030550080010a9050f038030252110a4500056043c10080000c0c80c00b6444402c80307402c160800310f01d400d54541007501b0030345ca0319902001003500041942c2c3e216500804211a07903a5a0380036091008801d801c1c2c1c4500d1002007140c0d411440b064010341982c0c60760340354103042203070759030202410b442d51200f4264150300101e250702c542c4461104800484d80c4107038405440c11441100c00894503070100c003040441402d080410201d2682030080801590180c9010300890910341035400183c200340c41011a101e0307542c1d4000b10302d4910441611507040c8010b1107140d0368a006e00308102c22a4508a06011500624100f94061503852240e803080c180070300d00408440c1c0c02c26506484944c0150703020703640311078240500350348541c0c24080d5902c1178400544181c0c03205007440000d41030006448062055 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 112965890 1250 112964640 112964647
    0x12021c030b03100e0f01143315040b04030305070b010504050f0c030a06051302091c080406051b0d0e0f01030204080c040c030e0a060e0c010c0b0703050705090a0f03020411 75
    0x680c0c00040b01d88120f48a480002541c0d941941102d2030009824142c082e030f5401c0ca840600c1e42100c2c00020352159448000b03400307200044002c410340b03070044840ca6442c0c2c040e245841c403406082111805044450421000703103001e8031440c0800d0207420646c021000643d0001d00e0404000034114a075005040640c0c0074003d0741072180640014980051a170500740202100241014a01e504081e00400c0d0141000ca802c1d003004101300040e5109808440c09031070410340300071503085000ca00d070282640064030315050904200b8102c0d81c60380306041101c05031460549503400400140000d41040d050382c0c0343c2c0c04c81d0001603001d0000d5502d40d0350103541411f205000c200204070010500441241c000c0b5070000f8107c4185100354018540100d08260a00ca00038078501000900d501010000d14410211400342c20701c00011a0007581a1f80014940314001000c20001d601039007045c0c2d0402814140320f801d000f004800309005062540c401140c40300100d50800940c20644504040d40d140c1280f401e04e07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 112967140 1250 112965890 112965911
    0x30c030515090c130f020708070b01080a022101060e0903030403081005011b290403090504020306010903060b0d02031f0f060303020c010c03121a0108161b05030712021c03 75
    0x850380381c41a0003d000c1c40c01890f01e502000a160300001742c01c1120f0508640741c071803900746520660049070701120364111110000c940d074000014401d08256008200d40513400115410000c80c02c1189451180b940d00c0d404003040c03901e0502d494901c241da0100003540c42c1e01d0b050400070004040601540703c2c20203041814400f6980c0705a5010a00c0c42680d40081c3c07018040c549603081d001d49400400782000701140c0d603040d001490400c40d00450099545401d00c6417103004200c120b110658840d4081050000e0401c006281600002c4601400a1200c616000e40c6d0b00442d0400030102c540400d2441914550105a0350611070420f4030b90311a041000254219a406959800c201d103040b8107004d00c041319002054841c2c09482d002503400380d0300340441d40200355448034000700d090209000c2901640021b440560600c400c0302640c41540d02c411045c051200707819681c2441d150306444e0350000b0000800803035500381d05000b80c110107500402e154401d05040100066425840d03204050070108410b5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 112968390 1250 112967140 112967143
    0x31a060306060c03040e010b04030b01060302030c07020d050102070203100606030c02030306151b07091a0607050703030f0507060e06100509160509010908010903090501030f020f070b07030b0307030c03051509 91
    0xc1d805001070b504a41d40d003c4001005155002e181e000843c8080030800109207009024003030400c50f80b04002161050740c0b20710094080e07000807078240c003070401c00f07000e01c40c09490032200342c4034090b0003000014078000035600401d0514121a0b601801103499a908002d1b05a041c803c0c1045e840d540d201960841c105000051401201414205012100841e40b0700900c10807004403092000d2a0b01155241031342c070892003000d06400d40e00d0038400c80c202e8800301d40c1400c0c82400c5544040d80000501201801d541e000c2d6054241c50f180c7c10108003041c0900c00000d0b03d01c0c4690901c00e84070600078920741c903050900c00f5800d074464100034040c0071660240080625024820408901d0340d0501c07076100c00c51100125949281c0360b01c0180d0a608103002c0e0000e243c0c1021240040c0c40d03080c1d8090004102c80381020069115000b1001c0119108115441c0410050b01806400c1003607880c01007414294800000d02e030142d90741040d40c00082c2c1c46820000c000c404c1200101001120700d040b030480c60102d413007a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 112969640 1250 112968390 112968397
    0x10b0609040207170301080f010b0d030e01080c0d0603051b040e0307060e1204090e1204060e06070f080304081b0624130507111005010b1c0902040906020901031a06 72
    0x58003840e0082400001c00004c1250703120340f2500c40100c16105d6030341f110002d035658280c0d00004441d502c1d240c6808920701303015510100d000d801d5104d07090701e01c1c90f01c0700450300d5003402454040700c1710080c0302c514820007143c09100000c501460041c0a02400c1a041a04500740d94600601c581c1c542179039110750040200035102d1254214000050b100d40c030040c400d0900c41030816406050740000381c0414420a1030344044810503220301191010201081d6038546481039014a40115004414281041c0341c094014a4030511520204252030a01d540b00708098106440499540ca000b08040003840075014503111403c0081e002440305090240c68921140030b0800d0b620b00c85504549064595240c1c5211002486880e01c4200b20a19040d00c0c010501c8682c0500c090142c012a6512a00f94209003d118143c401040c9942c2c40c0140c3d101c40040c103400b0303044c1c034021301759180d941c80f0000d03a8607481061002c2c3e000300805031b916a1000c0005040301c808220300b00450b100340030045080c0e2030b4101034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 112970890 1250 112969640 112969657
    0x12090114070f0209070c060e0a0b0117030c0715080a060308040303120e1b012d080423010c030e0d0e13090c0f050103060602031204021908010c03061502010b06 70
    0x14039964030120704015204200c8424003070b400a113400144400242e009145820480c080c001c10441c940b03060400a071603111452000c2d01d0003030000f0042c00300d8a610060103006081c600100d034a8420040e14580c14800154803a0034400400301b48403030f80e550008002c23640b12900000c10442c20381180d8a61402d801a03003c0a03042183c0d6070925000d80e4580d9021690f501580c0e0708548500e070385a0891801c50081140182c0080e41e1913034040d8138040c20710078260b8440c2401515410f5114607a20840b14407000400035910390400007407091510310341c0d0004018621401001159150034284058180c40000c442e00034140d10903642c0040c05507020880d4200e40a00702c03803d0f030300c0304012030a83e0007800148001610140c07a43c2c400281c0710000402410071208280c03818000c4c560356501c1a030700c034003c2c402010146400c0c1c0b4009401450005110b442d040b000000d401130681d10f81c852182103600009810000c681c4d03402e01445001d844044c1e0124100a504c024050801081c0c045020390088824 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 112972140 1250 112970890 112970927
    0xa091401090b1317010228090e0106090806010b0f07030c0804170a06051008070b0a02120d02030411061804050a0906091a07020c0a050105030405010605120c03120901 73
    0x140020981c4200010401030540010480d1507440c14000241410000e100300361811101010010050701c041c002d45072140001018101040c40d100e009054050030b01d10304c2020081d00040200d00703a810a40400e01030314290344c810b6030340d43c20b01c94503914040e010317088045500780900c40c030003140034020111182c5642c14030b0600728140c82441d000c401401650405800c10038090710f60408140d0018005030403074060702c0305010a4481012484000768180204040340c0c004160920500d0301c400f0007081c611a10b44112480c889110308242c82a4004101c102c10b0b16400005000510040c480542c40e4200304503112403800d84501c100c40100086044c001d07010300d0710ba07400501081511350042103a41d40160080c4880c3c01145090380000c42c0510050101d060b80c54082064244002401206928042e00000c0450b082000641c0c0b00e030001082200d56640b5241c000c03a180c0c903203813020581f1212040040400072088810181022001900c2404015003800440c1e00c0381c1e8030100507060082c1011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 112973390 1250 112972140 112972169
    0x30b010308181c060f050903070b0c16030e10020706050315010903060f090b0112050c090402061303050303160806060a030903020a05060c03190b030a02010f09120503070501050105060a09 82
    0x32503000d040d441e0034011990026000c840d0395040400d07050f900d201c03d803241000b00000c85064460000703c643c00c0c1c1d01c910150303100b030002100003844900c019410582d20148107080030111604242c80d02e8a0502c102d00080342140d01c07012905043c0c03840c41c0580600d0015000c501d09102c40101240801400b10242d07524984028030164001c0640c07201641c2c00580c00e000300303941c2d0741c00c48e0060700c0c0d00c00341250f04400c0301000207804440710308000c084590040140c02c500d581c180c208a0400320290043e40d01c1402000300c0c0100f011401c240a000310b2103a00596103a01d0300461040304164007400301418001c003807003082001c0c0c0e622802c4070803400305800d0004201071141012880c01010ba940240305102e584140409a00800e003d140704411644202c4c81c0c0f400300224510a4640b07001e40240c040e803142e01c20500542c040c66980715250340a14000074000d64824011840003035012050b10300341c0001170b10406200083c01050301400d005d8a00c1c41c0f811000040003848500e803840b035071103a00b65030b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 112974640 1250 112973390 112973407
    0xe0d0f030e0a0509100e0106020f03030109110903030a09090c05210a0e070b041401030204080309012703030c060501142103190e01030506030c010e040504170a021b060301030b010308 80
    0x11090b040900340280c03070400c03140b61055941711000028043c10200300e42040000a01c140b00180030340e01d980c030840185040d0b9281924080203807a008406030020038090015000c03d4a0070805001401c0455482503d4640f80c07144010840d416880f502342000b0040000203110000d10125009404070010020300321f503203181c6020001c0c515210410268003603280d00040c809034540c098019962041e5130700c0c0900442c00019002c0784558429036040360414410640190301401500481d51f40f0a42d183e0042050a0303004418282907410403008148003640e058140080c510490f40507240c90852440035a150000003540d15184804a9a10b4000c419090854030030602c1506d603003d0040003107642c91600c0940180040e400444110300180c43c00c0005040b91400003910b1903d000103071111400d0303841d5841031001a00c03005105580444584140ca0401c0b4041e03001402d82412990140c072403050740c80749260001b4060f0351a503104450510040c030208000010150440c1d0b448004ca641d2000315 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 112975890 1250 112974640 112974649
    0x2041202120111030711061e0f041104020d02130b070b011203020f0a0b070816080703090c0807030f1401050c1b0a0506090319031104360b010e0d0f030e 67
    0x31901d480c6003c00003205011400381c2218054420000d0340d41134450981c3d075425040b031401041c4003006444131130100824010052400d0300b6030032500640d0b0510800b000c9038045003d0364005242c000000d80d00040c12260140e100411102401c1103540e41c07413500c3d45984903603030f110b01c042c000c01e504110114003080405000304042c88607000202d081ea1030980441c2082c1c260710100311120004030b801c1600088031500490384c1800144400e84440445031950281100205848801103d58148544010071324080810410004621030010014900042c0c50b00c010907140283d41c03030074160b05000500145c80403020968096909d03102c1080a107080038400c007440e1100170b40020b0010700030714dc18480000c01c0400140320758000c1c032001c404c0c04141e4071401c600f102c51487d1003841c4002c050101703001001545030f1990003040030800200450036400d0035404501d40206800a40f01c1c0e99011080c01540c02c0b40c0004000002194160500790198451403494462070714010b04001401c8100e0b28a50b94 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 112977140 1250 112975890 112975901
    0x607120908070905070f1106010303051605060c04140d0c03030c0f02040207140c0f060702040f060b03090106150c0b0613020c010c02070305070f0f14010905060f0d050a020412021201 80
    0x1921001c5800c10b07030b56800c0c0e0500a0030181c1c1c0c09000906601010441180030315210a841c10000c0002c000301e030302c2c5841c01c0b60305800030303500d500b070b4204030500210114404110340340c000c6817040c1c0050741d11864141414200328001103414003400301209001c0c082500a025181200e4042c1450b16094280d031801022070540010000e50151010620a062101c440c1010006a48050885200042c1d40d000c02503007180e400b000310340c4180e0810040380142015081040001d240d1113020402030340320008003046800845492140f69510002000303064201c12261020400c20b0070144146205512a8903c0003402000349001da204411050a00380c101d0381102c0708856840020001001c01e004000d442d0041840b0175101071040da0340104100080404510845401c04a401105458080020a81518524814103005101100090945455001300310310052010000d030303a001e40c002800119440a003203000300510500c400c1c0f1661882603000d914143e0115950214403403400c400901520 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 112978390 1250 112977140 112977149
    0x106050d03050a0801051207050d05010e010e0a170405150a11060109091106090306040b07030e06010f080d0c050309010c020a05120c0901080d020c100203070f1103070f0506071209 79
    0x48003040100281540900a0b0951600030399500100d44d81c1c81082000c0d5204108901c03610b60840c0404000514040343c00b200c17070921442c0045030110840d0b03881402c585044240203426002403103038404018070a81540107440c40b1365001c43c209030600000c14115030081108001400340000c0a031280c600900741c2c00c00d40051070781100c4d04d030b40c1c5640cac804018103c9010210740b1020410f419030b44625105056843d0070101900400f00c0d5540c60b20b80f0101c2d403802421031020f256070ba03880c018101000740200c60180c200c080820b1100c03403030315200d1480d1890307400a4100b004001c0708030b10f00052001c401c4908580d42480c1120460354940005030180ca00c41d400b00750301146c83c604034981118041f800c2d030b0b0700c00c90807180d1300b40580c0d84858103500e84845042d0400160000380d4000b0b0780e45000c00c2d10080540c91841107074104807460790340130419440204240c80154800c0d031011201e140c20003d4802910301030810701c0c0424a00004039140340180d07000180305d10481e5003503010a902ca00000c80040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 112979640 1250 112978390 112978399
    0x3050d06060f14030105100c020a08010504030c0c1409060402031005120a02011b1502030703020403141b0114031602010905121804020304020907030b120304081c0201141305010605 79
    0x503510a0701500c1c0c2c818801e0500b0100c1d01c415412442d83c81941e0076281290000fa0030020103422100c2c0440382e09503840402ca0740f28003503a20108242d0024410b05200e030707200752922801d40c0b21900389440f91445640c0607411580044040003003640341c01d045581c10a600351000b584035207d01508503200b07455508003a404c00e101040d0720300558030000c2d5051440d8000c1e03d46418810006e034866400c040b203142c000c1e02c80c8042e4941029403680070343c02154019207910303006003826102d0361121501c104080000384aa07010070080080c000c800c004110301c0701c0090800c6040541e82103600c9a083c00011701902c2000100105080f42500030341004084941c420203462882101e004c00c08802e80000d080410403070040b9810b42450300b020f208407801075800409041d802c2d942c05000324080c1003c40c50294020408004403030002c5d40c10000707480a400c14501510340510345100000c070940b10170032071808582c14282101300d406442007059400c9480400030503003400c070a040050242240c0d0384181d402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 112980890 1250 112979640 112979651
    0xf030f03070b150a140604090204090509010b03010c1b020a030b040c140103060612091a0903040501020c0316150c080403060e0606010e030c100903050307060605100809120703050d 79
    0x100640030004281c40c40c81228100580e44454402869080c10500c0c1641c000860500a01c0003d1901400c1004824010700c0e5526150729403500314180d800c65031160304001e8680041c0314a0440c00c5c0649269007100b60001c011002c6006001030a01341070201801101c5d08040001095480c2c0070300303035009540c00031150010340c03e00e841d00300d01302c0b0040e01c80c502c4500c800c0d03076500764550710a000d00012644144d462980e400b420310340301c800410b121042102e081000d028140d0381355415860180c81001540040d540752440c20300060700f010044403280344a60098240c268551610030180c0c000d681d1800c80a0752030740c0c00701d40141d800014580703025020610220f00041041016008001e5628400d070583e1581e407103041c01929500c0c11608001d80c107030880c480d10b004500307040350081c0e00580e5900d031071062665a51609429030b40702c0c80003a181d080c1c60380c41c140040d0800202e0940c007491145400343c0b191504a410580b960408100c0074080d1200184601c1891b20038001e4848484000c04100070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 112982140 1250 112980890 112980913
    0xc02030307090f03080d0c020c150408070f030807060b0114030a0207030e030f10050903040b0c07050102070b030405060103030e0612070305010f06020d0509090601020f07060903030305180a03030b0f03 88
    0x559400898058001a80111010400100d11000401141d034480c8101b420031a80b50314250150116119201c11841200c1403500d50340d0b264642c400302c03410305401c03180d40c440c10a001c00741483d20079000b0031400140e108081000401240c01c4605481c0c1103c40003804001da04012100c01c0d1480da83d42d84a04004800c1c00a641c00b2940200703605446070700e44080c3c1510403001c0c0354a40320180d81034a8540c0204122042c8468150071895101b680385080d24030b0325403110302149240d08000001813040c3d02550040c0f01d00d50701000110060b0040c40c10740c40c06c524190740c1e1107544600501004080103025440e407640d5440d01002e4500e00000d510402c0550300d04060020002e010910400040043c50000040c0c1c00d0f002056458100c0c00702d41d16070740f1700814007083c8840c030b480262046045201d4107500408140f414442c0b10098512a903a05119034a107040081c103a450107800f04410040c281d4514841400c0000c0d92010346a06080c0070a120b030002d0b000070048504c0188503130701800740c3d81c241a03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 112983390 1250 112982140 112982143
    0x20604060b0103020f360607060506010e0d0303050f13020d2004050103052a01021011070b0702030310061805090406060506131706010e181216110301140711100c02 72
    0x70117606c2500208070812105c1ca080d01d501606800680b60011010400100850165000325a00c00c6c0103042c009100051100031445441081c81c040d00000e0b070b142d0610031111264900b1540050b145035144580140ba60005031080d035007000300401550301501442400401c07068007400401000304200907541e0b4070304015032900c0340300080200c0c0149100d2850200703241c0300b1b1003000e60501a03000b411540303942ca6007a0010400c03244c46201c48801071001d60005a01c0c040c04900c07801695010759103c2c2003d200a0780780b81c00581100c010300c07000d6403281500540a2a503502166000c40308020b054846041200040909070010b607001040001d031111403409c510500030889090450310041006600740c59a1a44000e0044c850700315140d001068204c02030707141301c8592034050700c241c403180c01c00c0c0b4443c182c1c50303400300304000349a0403038503019414016400081030643e0010740c028403a850314500241402039000300100c081c0034140e07048200ca6242040a402d0ba0150107401300500110410080d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 112984640 1250 112983390 112983427
    0xf020304080c010e0d120903140705010c0825050a0507060c050306100c080702090702100e0607110303070206011802090616020910030804060825080403020f0d020604060b0103020f 79
    0x100385039804c2098145000388006240800c001c405d6550400c01d070300440d03256000d40395607102581040426903500b41d501950f03034000c10b4054454800000d003002c081d000035009150003040b2510f0480d10941e4a20fa55099648000c070800c51132918a40c0c8035000f0305c06460341d0003604801340000d071615003010a21900b110085020700011547c012a00b154010112001e103c80c40340200f50100a0100d0001401c011440540220036401510881003620300100104d034206401054035078001d1082c0f0420f20b800003148138031080e040000d0341c9145000040031f50354403010300c10354900d481c010005803904411503041d120301d050b000388031950760301c454500c0c8040804a02010313403186007010041345041c913500d0766100c00c403035203c030f00c450410345003080a845100e0000c09a04182258003850341e40c2401782c1c02c0b40f81d42448191103803070403420942002894108100c404840e5548003c20215070503400044d00313644190310220114008410b40c0049007c0e0182c28405d810303d40b07004c6040c0202c00b244907400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 112985890 1250 112984640 112984657
    0x50a0b090a020d1202071707030b0f0c03070c170a03020301150201060f030312060308030405010222121401020c0625030c0c02040905071a0714070f05060c010f02030408 74
    0x400925458105900e038880c449031000a510901e41d4080900113000d4084030307030b6442e207076005403180281c0ea203410014900e0705006421041d04800000d10421400403556500000710b0b056451041c644000c400c800f40c4070251090090200956072030003084406030042c024003441c3c04180351103ca0107600900030790403e0103402282d00c40141540c918030b105119840454a0120484900c28650384040e90300110444801c00c40f00d840740301c040045a0060700540c06148140c00043e0f513103400c585090701c1561a02d185403d005003002040114403161403a0360902034000c1c2e401c0001e01090500517009100b862030a480314011002080010685081c010b900e4015203049419000300880040f030455141d6034803440416025032484016040c04c0c2c0c000c4890501c10340c101c03003000342c48140d0322050003002020114078440c006001d00412001c101d01400b050b2016004100f11400c01d462103c03142c3d240d0168501074030020680400009094000e18655001c64104564a0906080804403944107210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 112987140 1250 112985890 112985903
    0x111070b01150203041a130b03010801050a0b0a0911190206060a0806070f0f181514031e0c04030c0b09040c300b030613170307020c01050703031107050a 67
    0xc0c2d845219181c0c034411509540c00395103000c0c108401040382c3c41c00c1d0740d002400f180c000e11110540c40703e40b40f00c150140c08245a401e80702d615000c181400d5920080c090003190303042800c94201503c480d52001d00b0360380420400b04078010051142e030018000d240c1c000300b00d01804842074280b15004500700f03000e50003d07100301d0080b070b485a6045503608000c2d11740c1000a400b480e4034100d150311130a50900080c440786026504c045035111022070074a80303500001c0c008440e8644400442d60050312103085240c074900500d003103151402401c04070b511f03d404038001c2142c0250000d0b10501500c0c0440300619072082141d020315455413220245a000b41582c070b0302540c5030648540417640203850300b5440c1001d03d0500002e80e03040e61180c1040c075410a110307001e2075403104090134941d1303001e000c40f610a440d464040780c0e22001900300001c0c05d200c000502440b0f060104188140e440d4080340380080b0721401c0c20425510185850708800401000801540c0303443c000c5140d9080001c0400c0d400013880c000c41 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 112988390 1250 112987140 112987163
    0x1c0b0a0b060a020d0c030909020705060708090a050601030602030c0915091921020121090501110703020d0c02060403020a06050702120111070303090c120c080d0302070804090f0e011107 81
    0x1407201500c100e01e202c0001da80241c9451400d0742c400d07400d003030940e0300c2860001c01041c1e13220041e409980103007400311a00e80002080105440d401050075a000700603c009081c07001442c0c0b030701c5868107010301004e0f06080d0000001080b00607100d04403080703110068004001080c900d50084007642241140b030344110a8040803c4071001c500940b08142c484840d065107a2118820326a03450b080c540000700d05001f08110310780e0b007000322205407030600c0180140100c0c0c85401494114219078200a00c08210a418042c4402107075002811081c2841c4034140b03900d1105580c000201e0328090760340007d60000d0301c18400700b40340e45e01402922074948240c035020b0050b102c4651940c00e0311072039021401407440c140b00304000b10744a40c1100b807a10340942d0145202e02d0720b440c0d004040490274036050383d900b21049403c0180502c2003001a445c00c0c4189400c60500d802c030f544801a500c16842129845a01c50101c41d041e15019030015102a220304e0003006107010415100c00c6642011304e090f5084150030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 112989640 1250 112988390 112988411
    0x807060309080d0b0f09090705010905030303010308161103101e05090c041a030d08040201080a06080307030518041508070f0515031b030406051021030e1c0b0a 70
    0x24001c00c0ca03915440a881c03410b00302465104001401135055540e4021070b14410440952070744400e060148100d4030180580e00d052070005013145040e548514002e41c0108010004206580c0542d8140021609040d0504010b814486402c3c030141c1d6080d41d250041c80500080c00c1440c2d88000c03042ca40400c2007002d03030f0074091849801c40300c0c1218018116009883c500040d413410780d20084003031040c00310407070034103640c000464601701e0030050400109042e2000c1c0025584c00c5140c19034095201441880f00c2420b0084864a9010700d0000909204010031301c2008031081e01210555240080c10030400c0d140f40c00e0000414180070300c6450340500501c43c010982c0011052158182e0b000648a05014410741c82d100480e5403000346480d1160504040f4501d0071200c1c200298000c50040d2004610380c104801100e002440700d60245610f00074680d121006240151041e081e480d0701420f0000100d0b586401294803590041120244014180d244500b0032182e411060300030000390208010075081d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 112990890 1250 112989640 112989647
    0xe070201140c09041404082503091802040914040215070305030103150617031207080421120f091e0305160309050d05100b0a0b12090307050f0601080706 67
    0x28039001c6404015400001141195240018000d4180c003910014118002e03855013500c0b40d00c2500c0841740300b00002041d5100e00840449400700c2800701d0540e100b024440c0c2c1d40600340e48868891a043c40003a050a05140e20007941a94010040d9040520407080d029081060300102220202c0c0720341c1c00700c441001c1c0391a5410903503002e1342e031544840e85164250348130100203101e0036410f01c0381305445900c042456104404001c00c0e0f2817000000790f0320385080e9000707220409002000b00d002c1201050812002c1021025580400403185c003500900007914882143e11811034280d0030001400c00510310341c00d4507168004103520b801054404a0001c40b140c447c2500c00c1031800190006805022510301c1c8414030071500101d07031090411050302da540b140030030035030740e02c2d010145c860380c012104501c217140290040710710414007110342080480c1016038810250040446201c4404021000220720980802c125011240c1210446101d82e0402c0b443c83d68401007400b4000c098000c815001804070700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 112992140 1250 112990890 112990901
    0x160503070e0f030109020a06050a110a021005030403020c03240f0f04081605060109060806060d0b0c180607060e0d0f1202090f090103060606030e0606030c04050c0409020408070e070201 81
    0x102540d0700c004050124003081480c4200c1440346925550b0313110082c005950724280c03680100a00d44440e900c41c000150094500f5184003040c1000303030080c100c01001695544518002104607050590712900d40f4241207150110380d0900b1a01171203400b001955080903014410440a00c10001842075562400101004202500c032410f4080c000008100012003600c00303000240012041c2c813003400403a407115490b010003a44002c049a917078040c18001104140030a0303600c4901a030b004d4056204543d03620508203c011b000c1103000c01d0100e0103000c0300540280203050b040000b400c040d02c407085c608000000f40b80400c0000450700c610301c09a04002e00450100044045948900300c086078441c810348082e42c8502501940185010011045603864401c514003941c003440c0d0006141d41040e10140880300141040011a4059020029540d4000071446545a802c1d02c000ca41030305c1c1c20589440a00543c0c00401d880c80c0049400300d191b12001840c8422200741816030881d40d100c10205900f00c50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 112993390 1250 112992140 112992151
    0x4052401170f0c12070503010504061401020c010822050d110f030406030f06051201060303021902060d09080f0a0c0c0e0c22051e030601060905060301060f0216030b160503 75
    0x911800602e4104128540d1507200d2010b00d0814588481120303104800320f4210380340b80c042400803005021905251160a0207841c1c1c1c41c8401c41580c03071101c0083e50726016406042d040000b408002414880c601c558103004403284d8015421034078035841d10540341c0c160300103c01c000031004001ca000c003d030001140807080074800d001d10301c1c090070312104801908200d2040700100d9283c0320006526200c01680c0215180079400025482d400e6280c001d0500344000b00200c0403481480b505d50160740d40e80115210305070b001100007003064003854900200d000d0005002108032011074000c2030203400040341d50300903100307482441000c0e44450344400c1500c01170b1101c0f04010402d108010800c0d140120341c0074154808412084a07941d24030015a5464980f81801c10780d48443c080c046c01402d00b001030501410326400d1084030503060901281d100d000520402c0100504900313041c19650003800040d8568822070b03009403510781c036400c10500940081c1c0340780040051220500c84040d00c164152409038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 112994640 1250 112993390 112993427
    0x625080114040204030c0e0906070906090b0c0a1b0e010609030b0703090614010b1309020928030803040b060907030e0705010e01140406081801060302011b030e04052401 74
    0x281d0a01070880c140c0c450016026410035400c0101102082040314040c0092040c0031003d1918030b00f1140050038860064001014008451001d01060350401c100c0401e0b220348100b070700c2d207643c0e44007000d91412500c0c21001e458211402c1924440b44107410783d520a03500244803025169030b03a5102241c90038000e20000d4005030702240400c2c1541c1c840d801490303107140135510200e250320280009215240013070b48006154a4002507860601200002100007450751000450500031204081004003100022018050681c8002000220b007030648000285030403041713641d128941407829040350030084d60a14407510000002031a02ca100e802212011139480c0080c00006d46841d00642d189410185002d060118811002804070100f502600040c0140d9503100014200b40040a407440800300149145904020040c80580d030449000c25400058180d01490924241011a140300100c03a0b000c0d0f0280c00c200501400206045881c15400040c035140b941a0103214010f559000d007168113158070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 112995890 1250 112994640 112994657
    0x1120303090203030c07140109090506090106050a0513090b04050f04020a091104090906230907060f2a1e0209010306020d0b060c01060e060a0e1302010509040e0625 72
    0xd2180e000252080c0c4081d003140c0c01c0060303070390405082110303980100d0307100342c200074095035150f038000003680060866800030021403c001d0301090619405000d514103202c00001c024918601c10001c0310720342c40050038000441070b210054a00901114032802d0f01c541d05000201d0003500b0810b114a018a0380140101212860404128007410684032030310f031044018440040e26210724000c002401d4411000040e250a82d02401141c050084020307484031030904c81042440200002c03800180e0305541041c10002044100466078080016250031743d20b08081e080401040046c682c8280702c500c11012000c5041c035148204010b011140c50295000305a04010808901e00c0d9000301148100c0714400f05040380e100c1c3c003088e0254800c00384c0c600350f0b80d9100010441c1d10048a01c031504070204485c55804549085200c450440d0082c0903400030204075440102107a0242c411560448000340050000d5400701c0c10440c0c039010101e40302084180503103c04400d507001d5002c04801c00c03500f510759030341 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 112997140 1250 112995890 112995893
    0x8030f0c091f09261b01050324061605010e1b010815040204150906020c01050a0f0903120201020a02060a02070f0b10080604080301090e0601030b15040f0c091d0112 72
    0x52202500500d010700001c518085003820090440b07101ca03080f900d43c0e69103650700e10703c413407490a4542618020303407881c0150145190b80e030200840e90401c28441c04a04d0700701c0c41410b54510b140e62601a19800031000444a1705a2680e5558500c42030040b0002c005030034900c0c40f0981c6491180c4283c02d01007210b401d04100360b40c0511450313504071982407a8081c0d41040c0c200410100c1e0701c5900040e0400801c0042d50708480da220310700c90043c03d168070203415240c00380b2002900e24065a2b03004414001400c41100c00d403803107400342100640d04901c14910400030150f01034001d510007883c1d00c0c014050307d4005111b08800b4000c40d40803a034001401c5400c4011784c2c0b900000c940029003103001e00e513103001c80060f4521081008500560040200b070b42d50354507040b040011501c02c404020290340040c0d0040000c140301e841150351000003c01945140b207440130007c2c2c000c1210400e036000d550300d022020b41c8607540c0300280c0390617105521010101801007007165114544244187c403080346011703403140b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 112998390 1250 112997140 112997179
    0x60402130504050406060e07024c02041e0503071e03050706021b010e090105120a020a1d10032022051b1e070201020a0f08030f0c09 58
    0x84a90801010821466140e00002d03068600c203540980e070135615550140007080725003071007a41004441c0020f010002c206000d864801c150360440c141008241c648140b032014610481100304a040035461056410303420300c450081d04103010714004180041d428041709548a2078040c16a9001801810018078141a9200c0110480342007a80f403048070100000295040010070302502103a0098003882040c80f5004207194404d1035845e0411819004412041e1a0781c01c100e030666000799242c82d0002e04044056203400e03003225009401c00d400103400140e4880e0490403017a4007400c0d018600d819140c0070282c1501c40c24901000c2c00301040460a0f11070134001c92952b041c401800344c92804c402090401d90103401c610030b024002803544031010800906d4080688110411454100a080044542c2a00707000c014822200707480000c005000d02c00d5a0081000e2405154000d44040c0c9140c4c551902d44004d800c240d0743c0540b0110150042800802e4100c00d5880c0032201030014466260300040f80ca = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 112999640 1250 112998390 112998397
    0x6060303091c0f0c031a06090106120e070b0409050108010e030913090f0818040e010216060902040b03010207050a1b030209070c210201020a14030103030c0209040804090911030d0206010608060402 86
    0x8850300030a03140e43c6400184402040720065014401c08070a44902925036003a170702c030003403d00c2d115105103401400844d4201d00461100b401e40400040c0c0040e4002402e40740c000c85d5046000d04100204000074095182c0e0021416a04204008c3c030280c2203000d0703010350701c0c040c094005500016070307100045142881c0d84040803080c0a40e4041d00950a584c40701410341d03004442e42c99003100c000001848600f814050800e94103c0300000b1460081c0b0101d9891066146103402001c440d1a050712500359a86c68102c2c2d0b2038500014002c6558400601e0b105540b01c1450340c04481c0c204507030207840c1030301220121010480f500031b0042c40070342d9241c000448640da81d5800488a41c11042d514034001000c5400484c031403030241c3c0006a8076103540c08050010b80d04034041000c0d440c0308100510000b0b6020001d42c64880e4141d0724602176459501d0b10a5150103503030440004a4a4240f040b0244400450f0100200c10286d0544202c04512030040f1b0f11070100740101e6020801d45008143c0b81d08169006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 113000890 1250 112999640 112999643
    0x3021815060a0c03030b0a0609090f02040906081f0b03030306010c061d0c1804050c0105070c08031c1b0c080a0c05070e0f160c151407080906060303091c 67
    0x1024040540d260025200d50401016400002c0d009803403442050341512681c035030369004607540e0014603d00b11000b00400030900922000e1621241c2c0000007504a405403405410f088009005a03510303642540c1d41c0707000c106203502d005c1414103000711240115200e200413076000503010b140345958140041d5034901a2480031103000350f843e840d040000c0b2003050380d0440100014043c00b103440d0024104820708014000f0f60140707282620921002a5001440c00c21611085c00c0054a8a00d036090040c48824113070b200ca07074180000907900d14003c00c0d49d0358000020f10810820880105d01d45204145282d44d200002d0101d2072000100000c50303220b201034805406145844220300500350784040c204032075984020b04940c00c60090080c000011b000580e0702182d0100c10303200038090b14400806540d801c1c00003600c450303c00c00e02d01e00d0a84590304042a00240018014024180b0120091007041c041303c613800503010b910b0119801b031130080b0407a44041d4005046420200014800403401c4040400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 113002140 1250 113000890 113000911
    0x30b0601210b04060527040302031306030203060907030207050a0b041515050405090a031d130c05070201020c0a0f050105030a14010e040506010f030305040905090c03030d06091401030218 82
    0x11901c00c9841035840c07115603900c030003012400000341d800344000c1c1c03441500641d100d240b42a14030b032603030241c0e0f21540380da501d00024160042d894074141603045109012081c0da48c000d070900d0124405400d03800440c002c850544500807141c1c0d481000700d0480c020307203100514a8200008940116460b60101038029002d60034000c2064022003006003218103043d40380142c0c4100820030009803502e8862300d5481503030440601021946a070b801090a004228500381b603d2200c20700613401d4950560468440300d41b19820862441c2402c405003642d000441c04034014400c011904249081a0060744101e0300305494060303075a0708042c0191071a400c02003c092100d581d4542c12005a40340c0000d0310300030010200c0c01c0c0501c3c1842d040160821074142c112404c9003651500400000b03a00400701c404441402e8070002d11505c07581c01860504008544c21941441b000c0742007074442100d5840041192a081401c04c6140861b40503560144424030020b50312003152054490200202410f043e8070406114 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 113003390 1250 113002140 113002157
    0x1011010f020a020d03050609100e0a1103100302120d090b090402120a0b0108090307020a090504081204030f110105010f060c02060c01141b180f030c0a03080a0314010b04030b0601 78
    0x12000c01242c01c226070711801070780a44c10484003280c0521400d80c20100030f403515509071600040e28410345569100701101c0131105800a0035216031584400031003240103031805d40d2810400115221001c0f107020983c440c1244040e20000e207040046c00d410a10004d45404050a00d00031a0840d990414a1200d422036020882038018100a81c0c00130300c070f44542200002d180d81c00b03a0004204410060040140340d20400150001d69158514601110214040800c8070b07951490b100f07656024104685000800072014042010b0704903000c9032620f2130664504180c1c1c544043d146082c1c0b0b82c280b295205002c180c070700030b2201a21404031000614006004189004000c28140e400c656020a10030030380c40340300c4117110000c03041038030350056081010300240c10b004507000d21200f82c280c23641d445032084a64524111098505101e81304c2030030801885509040c0e56400c100103150300544200e0002403a0810007400c5906202005058514a580b030070304050a55880e00d800c0140036010906000040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 113004640 1250 113003390 113003411
    0xe0a0b09010501170313050913020306040f060b010509010e0f0105070c120606050409110d061107030206190e0d050c1603061b020607141b010e0f07050d02101101 71
    0x54002500410600c0c0000407590302d44541136074035180110420700c0e240c008100d03056001507120114025180c00b155008119102e0460700040840210f10081d0940030380010002171000c012600849240249002e2060085c118011651885044a05400f041c4e05506209007401c0501c00007021280c1810000e25107071a9480b4076459030341c168002500420200708031010031880740248802080c090303900f40004081c03583c96005c0c9540491004c1d0180383d00b400003505000705600720b1900c1500403003915540780600d007030080d141c42045592225a851700b884552116909108005d40c081d14100a444400f401c840110303059400111458040c1c40388094646403502c030180100f004502c280340002c1c1944400c058010342c903440e50f24007415900100b04000000f43c003d801e0407080b4030b00c0f10307040c1e43c0c03003c44510803a207108551200494640c600060314046003400560221002c2801c4201e4a1980e030790020041441c01c401c2000350090341560288003d02e0240b020b42c030740c00c10114000b051002c0351 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 113005890 1250 113004640 113004653
    0x52b020603040b0405070909080306060319020f04060e0d11120304031a01030b07090e060105090607081206150f0d022a0106060f030908040e040c03080c01060914060d03030e0a 77
    0x2d0740c041e41d220300072800303100070030400b040440010400410107020f440d4a40c3c6540c0014000100f8203801008008001070062201d000e010301405900101151582850301c018038440c1c0003802820085071001405d13008500c1d026600d0280e41c0e034000060041050030806024440507a081c40c1c880510003448048001440556046441e4484010054546d891410140c0600401418034014021000c40c18080f107280700444660181003800c26039611203400303000c1401d0348a108000780001c03502103901e40400450f09021801600121900081c0b00300742c0384000c05600c1400c1c00004105070070090003c206020343c004d403e0f030070700c0707403010782c02d51b5075011096040080342550509190b5505c0c0801d10542c0e07088402004c40c40c01a150410684940d540d400a0300d101d1030183e44510b015200024040041c0d0518520203160300440003500e81100351022400382c103590160007002e40c105a81c041c0c0320300d24445a14414000103044c0368511886403410b5000301f4540501c0342441c0102440600407405 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 113007140 1250 113005890 113005897
    0x100e0a0b0c0d120219080601020a1505010501030e0f03030f2203020a060501060f050313061104120317270118110a050d03020307060b01020309040c1710052b0206 71
    0x10410103010b514262280003040785a100d0180512144180158680f030320f2403c42034030a002d4a81401c10031358a4140040c0d192070039800000703248001182c05c083d041021508400d0494100ba01d040c880752145031085520758400d02c1c61042c5130b52040c000106010401d90009403c03025a0012001070381030081800c0862400c0c8205402503400074142901300444c80c071413540144034601c2c20110200041340c00910303a10018068003c070194000b124414004980c1c0039542c403d07586100c55960302e55031660315182c03c80c032680640125080a0482652104a0000b80c3c41038015016038880050382281e07680ca03902045e5000c0010359070303840580d985042400c158031641800359001e0b5003200e0b0f03140c0811040d0700c041d4100c140211907010000300080d8000060302c186e01d034810404180354009000403451400303910700042c0d00c0350401c00c1c00d00f031080d005044600d10002012103a003441d51202c0b00c070b558288041c89103d4004600c80e4100c1d40360003080c2100341c2c41d142c880d0b02c0b4a003100c03010380004047e0381 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 113008390 1250 113007140 113007157
    0x903060f0b1e030c0105030a061e090c0302040b030c0a0905060a0e130204050906061b1905100608030d18061406180402010c11010e030a06060f1202100e0a0b 69
    0x55036910300100ea850304188015040001c1800025542d0415000c652142d8510200c82d040c4107010011440d04052a040100a020340613100e002241d40200810700349007139446048200c92401314810302c910300c80c0c02107409640c18186071a2554480c01107800d480d610800004c000c016a02e200840c81e9a0b500d0001c2018035560394500f4580c0c10000b0420410091401c490f551192042100f0005501c030302810603808042221010344460114203664011a43c80410070010300030002d8115100c60341e503901c400018005c1049800040610348040201c4449001d801900e034400d110762243c50b80c29402501c098890041492115091503032641c0070384902c802c0f107145e070108a0013005081c0c104030030039040e907a909100c03c44c0c01d030406400180c0170004944020380011035080da40d140d00e074040e0f2010030400c1c8011b800c03900804514209807006001a008521024013083e400080c4070b200070340056582c2d40c000f4014801401044401d442d000d0301c800300303d5000840b40000140b03040081001d00080ca = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 113009640 1250 113008390 113008421
    0xf060a020a09060e09070302090d06060e040303060503010507090312020c060c15070914060901260a110901020618011d06040605010f12060e121602031c080703020703090306 76
    0x410a081e005410019590071000804c80042a107041c1e40e5a0750070015000070301400d0040c0d9942148020070410000c11074090000340c200700c0e000030a2103a850340940b180e4000e5404015040d190300806003a200191444800540303555001d00111b82c0b02c0aa22108602c60700440302d0208007407001c604036801030000045581c21901c1c180d0101c9042568040d030048231854086407507410448112814040e0140c198020400800c8062040e4020746070b0b43c18815170007001441500903402916412181101c0b0100d00742d08000030345201d02580420b07520201e40503005025a56a19164421140d100900c1c8003183e64a840f440441290140031500c10015000064a410310700f50608000b035910683c0100f606074a0000c040146410b80c400300c02859500510208281d503101c02c0140c50101c84501400807500f0018078005820003602020480340c0c401c0d001e44d00820240030042c1c684000040140c00030900340b000080c2031502c290f00030b040603482401c08072141d5889895500803650f03e0b07600169007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 113010890 1250 113009640 113009647
    0x106020d110f070b12090102120a0905010204030b0c07111e01030f060b070b0907050d020d08130509010b04080106140a0611151501031b0e130603080a050304033c020f060a02 76
    0x6000b90f030001c04e03906c04104002545007510b1880d160400340c4004203403c840a0b5681c0c80d102c1007081c01c0d0125001560130403aa0000350410441c40c000b01da02a000494045401855140c2181064011082c8080c040d40100500307101c0140103601400d43e481d88114001e0b500d24022030000d501b030340a40301b01406810000464609020a14035209240c2c105034441c0742030508a100590300e000080d01c58940c40b02040ea00d6180d8604091340d103005030b400066010319901d00100b0b80c2000480a001140e19240080c41400e540d40301c0c1000071600c01c45000e130803081e650f100b4031542d4001c00001c0a07091a00e0100c0d113030540c02c40340301c500d8800705403241c0c41d4800c400e540c1d41145607418020080d129a40e401280e201008006001e4100d09212202d0340c01507244800a110f114070980c400300007190007000480c0d1f038180bc507400900c2e030b40c0b007241d044010516a0114194500c0e05d41c080805a8101248007840c00c100001c601043c0130b0307174014401c21031090807403000740d04100b8041c150140507200f40150b103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 113012140 1250 113010890 113010907
    0x905060d0f06120b0709050a0306020a0e03010606030f180b0103020f010504030f081e16230708030307140f0304020402180418050c030a030203090607170301030302030702180106020d110f070b 84
    0x100304c20042d105a040100c030110a1101d60b441c862800d040b00c0c4e21070001691441c500710305544900301c0820441c0c1c1540780050000d1142d070150030142d04d13504854010420748036800004140d946111002a2401c41c10500602c010f062040d9503c034121340504001d4102a500d9a9074118024085401c0742c1c80b46000c00c011503032040c03080310360101340510000036040401c00c45c08a54890700c3c00d4000341541c5501c0000350607208608805d00044614038081e5442c003500c43c4042c0743d50384d0064908200003080a01241642c594000640d031f030a00024009601c2c0d07844a80030400030f500205000716040d052900341002550300d9220b40c1c483c400c2c642148602da19031608241d418aa201d46080340a608091900350001c4c0d804800c80c1c0d903810089524603103070907142c00c02c80ea44445107401c02c0c1c100140000040705058000024145051080301c444480034901200d82001540a204046c0580d01c0060340d144c0150140c8128500c21451301c2c00c90310b10b03440141e4804d1414031280c0c42101c0841d40005c2c41e04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 113013390 1250 113012140 113012153
    0xb01030f06050f010b0a0e0a08030a050301080c010503011d0a0212040f20010512130807140c031207080a0c0204050c0403110f030705220c030c02010c0903030905060d0f0612 76
    0x107034000c00d040f052084562510140340300d203104d09446841003041c444000d07071841e81c1c0d018460001e030030443d049a442e0400014050200c2e03000b80030310520381c030480c81941075642c0302c1c03011213059030744000b854006010100d8214042c0d80740a4020943c0783d80a000800815800c2c400b000e00c51402429004c15507001c1c3e081110b17408420040c4e2010b0076904070410000740c0d82040c00c5130058011907500f002c4a039540d40260320b40c0d00081000800c403007000140740051000c0004640e6a4084420aa40c002c0404200f0103550341011681c2d0b4210388003c0c04000041020300c000703025152002e0074a0523140c50150f0018040314000c0310a0503c0b004089018030511154550ba80d0f8000003d035564411500c6034800240e9440151061500c211440180c801d400c1c18951880300e00a4080d0384188030720175115001034003401298030540c1c010740c40c003000c2c10601482080340e80200c94041d2103250440d4100024040c0c01d07480010700426103038540420b211a10707111711681c0c0c028005900c550544d01e005140a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 113014640 1250 113013390 113013401
    0xf091212030507090614090a0e040c05010f020a020d0809030c190f050109080c09090307060c0207031e0c17010902030307050703020a08031903020d09140a0c061125030b01030f06 78
    0x4004020213001c05000c0c4076045182160300c0c810006101c0d44404c07140c1c0000304c0d2101582c003ca282c04010a061100308940031030b05200340c40e02600da00d44102904103080741c0d41c1e503113080065400f090400c03031507000c20419001040300c8807014043daa171082d000340115a51404101e9515418002e42000700990780103c642d0034050a8246400c8102c07501d03240503d95540c095401c2d8a00c0b40790301d0307400700e078440c04100211842280e10480610140a0b0104080e446210343e210695401046da26034101048180001c45013865105a068892909150441c90990340c004003480d020f641ea0b00104015960030030160000622a40c0248a00b50441c4180221100c4d182c1c04000700c2d03442440766990304125a0209080c3e00b00a2500586510212400c0d5000e403038081c4010700f0307411813070183e0300d089200851080b80c4103001d50f4101c0c98241c0e90300001c952540c1d100700d0226840d042512020b90b07204207881c20a0008044c0000014502c0d240e40710f028022000303034030845800217110b01079010041e150041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 113015890 1250 113014640 113014651
    0x807080703030c02040c09030b010f0608010501030b0904031416060621020102031801030204180e060f070e0609040e07080604031103042106060b0c1b04060b0a0f0912120305 76
    0x40d010035072440c1d80241004214010082c402c91321403e21414041c400d08020008503000001c1c06000d5a68103050800d01040d4040c41e00055410000800e9550180c01141c9610602030240c0e1815a04ca8504076a804034144402c2d03c005010020b00303810048442c00b0460840c0145800a46589842c44408081800b5040039031808002402540980e8021056815100d4010075002c5110701e9000101c0c000d100300c0e00203000700c14401c850b0b000b110050368400480d900d0031400300d0700b040e03c9618041a03940781c115206000511080400d040d00d040240180140000182c00442d04c1510201c20702d06024054000218a07841502000180b55005000003621850500558500b134241700094500d1001e07000c8042c0002400c0c0c074044200700711640301000900710140125140e504070110141c0b07503005940340030040d41c200c005100c1e040c0380501c1060304075004001080d2030044224426079000351024030481c00d000c41041d000911000340301e024451244070788242c00201881e40b50107130490704040c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 113017140 1250 113015890 113015893
    0x30f0b1203040b0d02040302131406041b031d0102040303081e01081005150909062d010311010221070b0a02130603240e040506061203030a0f060b0c0601080708 70
    0x6040800100c100e400b035803c0d500110380d480042900c00c1000c2d20a5900c02034016215521004012165a00940054059448003d0513480d820200010388a0340a181440326545100681c404c50003030384280c81c8548090006071111f00c04c00112800ca030051791080d0081503143c000c002c83c42440c9960310503842a684403109903075050185055460b0f00305032f101031417540d81d007005c506034802042c00200400c0000300450b0032407900c0041d82c1e8071040143c3c1c002010242c121144100b484c05a0f000000d240350303603249403903240c2c40c645510152441c1415030906500a1008075901e405090140f9007440c030701d41d03405958844991801c4085070350014660f2186920500000351440601c044c2d50048076181d00e00410034140c01441070307010225070b6040116820381c00070009a04646569aa8403a40c007501c2a211555241820300a481c00359102d09880703600200300003031802a49a00c141a030b40e0000b500040c09a40380d8410020a0380401080030850348070b8001009a1682044404c020740305000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 113018390 1250 113017140 113017159
    0x9080414010f021209041107211b050316080f04090218010302040302030618030c1e070b09060715062309010501210504050114040f030206070212120a06050907030f0b 73
    0x14580102c0c044d52a4441c42147c552508401d03001080e0183c0303000503001480b505020030441c091009036004010700101040c0780e82503041c1b14400e01a00a82d10700e130041d02440ca000e00c24800350628801149044415039814002024401e200202800c041c00050704c006a071000401480f00d10b4010240c0b03014100b600400040c001600c010803400d07001058050000305498030103007800d0640c0141d003c030036190720901d1419203041c01c8805040800101d80d030140c5801341c0c1c42d121070340154400da08489030811410072030140002c2d038107018251440b0301c41e4030010b61103444500c101d280b03110f208802d001c00194458200028581680c010b0300414090030900da240c0607070341c222610004140751441006640b0700c0007409005081d041000011503c420400b442d10309854a6640e101c06041d09400611400000424250000681070a03030710307074542c80e28108900c82030160035890005121450158070740f0b80004090b16416035440c00b560080e20b0128001850032240c1013241c0001101034072603480c40c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 113019640 1250 113018390 113018413
    0xa030b03061317130e1b03160302180603100e0a020f19050f0a0825090b0901120c0207230d060e03070b04140f03070803060603100e16080a02031b030a09080414010f02 73
    0x10200c41425231202d0802588a030140074030801c82801620645402034400010400620340d8006030342c0a030f0f80743c0360005140d5190036564100f240101787c0141c03004c4c2d608004500c610503000c4850820000b161800520b00f4202402c00dc0c155017095001c000480c003844107001030401c5c1d00103810900c00031180108100300e000d41b80140140c3c6540305100e107002002400103210f9100307001427011410304e510b00340426420b2480c000c1d900d182520442c1d181d2500d0701241d0b0b0340000d150b500c05a20003801080080611a1600e50900501c210380841c0301c01c1c4020402c0400040c620610544207602420003025001103410080d801c04074074811401c42a0810050840051213140c1626003020055600315225610341031100c052807501e4022034154241c1030104680c0000c004c40c8010804001d56075848507445840d07030501a40800d65558141c131031a003403a40d06041c000310155500104601000c40d000000340c551700c01caa4082d03080140d0008980941e080e065801143d1101558010302c010004170606 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 113020890 1250 113019640 113019661
    0x509010807030b0402090604030c031e03020c011b050613020102010c0e01270b16020301060e07080402040c050f130f050303070b04060908070210050a030b03061317130e1b03 76
    0x10541e80c103042c0d55000c501d00d04d40781e55060341d001034809011030342e03155180d0030200c420308110b100455441c0e240410003070326400d107004502105070340768004003c10350f017050055426003205040d2012003240d41c0c02d40702c0899010842c082c054840702501c0041958607000090a4582031a00c0f5828030005030803a0b40980d030302103016094290110300b14001100342071040130568100381c0c8040d02c20230300464224581e420013610240d0643c404c800030015690b56403110000c2120403140c4c1c4011034a040005409403c1a410000c03c00d006d03403a02514280782c0420f0200c84d60000c0401e1451105072103800d0100401504519029050840055007005c4941c0ea405003480c0008000a20403616170f00468100150441691000780d402818682003420400004090380c100440040010341801e6605060b42404604c150040807a28070707030b00000102d5291034030707070b001c2c0c0120500780c1328001c01c07007160b690300e1868071a0080c0247e1050a074440c1420b081004100720b0002258407503460400502403041e64 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 113022140 1250 113020890 113020907
    0xf030515090a0207050106030320060c030708181204091a0603060d0f02030111070b0f011401180e090609070e0106090510120504080c010f11070201030b03100f0c080601050901 77
    0x1007100c1c0542140c0d6040219406809021001091982440070110800d90480b800c100b12a00011000820010101c000340d9940010782d122008240c041011a840340c0c0700d181002c1c3c1c02000d0a084140d1520b80281c581e140c003052000300302d0380410100e801d02902440e030041540c8810144018401c2c4502840024423034440035055500ca141340a4034101007104109020301402c0e00280208101c08130301488010a0380b10b07880031500ca44070000001c60b40244c0001c1c00d0f0681e40c10f200072000072111900192801d40e00d00c100d101d44c110030040300090f102090300c00948540c0d0040084e080f13604201990b40c1c9091195041000c540d0341d0180103111240e4881540c00c100d540c201da0b04d4440c04080d12003510749429003d0b10b0f2007207604000800043c413403180004c000007405440204602c4800107203010882d10b80507400c1541030b40422410001d584a074000204034035005013a00d451000203406881101c115110080d5029114039075816060340181c0d0451703002c0003c1c01d06510301744446000034259407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 113023390 1250 113022140 113022181
    0x30c02180a140420181005010e090403020a110d1401021216020303060603270c130c05040b0d061706040605010605070209041b090608070807140a030803060d0206190f0305 75
    0x3050304800c030b6003e507182e0b01704d8490b41d41343ca0841a010f0030300700e4038800c40e00070718007496010514000400c06503041103454184104d8141d40505070f0b0050590707a000070507502104455000b040510b081c00440c40341c03000c0403c00c0c0b030014001641ca90303070920700d07028010004180480164000105da11001d4011007165880201195202c0d07681d83c480e0410f00b601c07091108038054810f907271080f0001d070350303800600e650203144222080141d05803464260400d44401c020060002142400100041c2e1006c07800380c88003800c4141c010034800c1d29890f985152038043c1d12a14095400070052009001551207a6805000075290a51510a41c1d801281050350080c1c00100324400c2c1c2c00034038840980e1501c1e0314001d04103050041c0010382e80c0c0c0c0303500d55075214140100d0880d07000b41c00000440002045c0c40c6888410084d0924408602c1c5444400d001d41005140c150840d8000c00150016580c4c44028a64030194850907100d003c0c00300b10003007070680729400d88800e00d03182c40e0501500c64960401c104200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 113024640 1250 113023390 113023433
    0x30601030b0f040309090e102a050d0e150a06050103140c0714120721020c060a0e0d140105070c320601060906110102090901060c030c02180a1404 64
    0x6480f245401c88082c9004e1348503001c5d80e0700e4035000c038039400070205a03d41201d011217814802d1a01d0005091950140e41700d54141c0758001c00000d00d0b0050045029200700c03070000000148242c5012a034904084042d03d007100150110400c000282e409407103079502411080c6000c001c00883d0900d41d51980401a1142000344408140403040107079104521031074003000c500f40c07111600d1103041480b40303400c00c0b13104480d4800100451511403800204011104d00c0da94014000c11804809104560f03010050901c10445a400740030328985921204420840c825044216902142d0038031a003140c801801c554200981e10f9240345c00700b000030300020a0260b01c40c0030402d0621984070000300540003d07812078002d0080400000e07040d9042003c4404690031a2502002240d8060155080340704a0a00395405034120006104452003201c0705c010b558468202a2800c0300c0c19000204081c4445e030003161000c20f030100b040b6410141d4001c0c0c0a40d06059080b5540c50f0601d42d5580514030400720f01030519 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 113025890 1250 113024640 113024671
    0x70203030f150d140f01050606040909031413030c0e0601080f190905060702060705030103030507120e060c010b0a05060408100f0b120109030e0603070806010f0504051005030f06030601030b 83
    0x4080544442c90082c80014900d60408040380f5104000400c80b0842551a0142502d0b0324801384040c0105031095400800c51031405081c400010004d04008400382c0c200418203815011030404407005100207114450f03242c18685c030350300c0e02c480348074442e13000840700100c440c050100b1640c01051454000152004417401039442c1c0da1416602084103640d84941800d05109406101d00401c5071030040c2c14036406e40c0c080380d80f014010f4819110a00c4010009030b800c100c0500402c194052840040b096854110f10032035030340d4000b03041600f0085100106940d10054500680342c80f66680d0700078541070310a070b03083ca45440b4002e07032152400c020b0309c030181d5200c040e14051403202d6806003603030000c014a03003941d00c5200441140281039500c1c08a000c038403c48000e03211440c1005c1501e203c3d212550340d140080d82c90100440e018001c070000300040c86000d0101141c2c0c0d940d080c0c0100d20f56031340c0b980c0d00383c0c80c0d10f0f111210500300704019003500d0281d00502e0042c00070882620341c03140d0210646041c001d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 113027140 1250 113025890 113025901
    0x11d060109061a1812100b030d0302040b031303300b03011a01030e010b04061706010614040302010e0a0e0109021321021c0501110903060718150c060213150503070203030f 75
    0x820380c0170b40429030420301a190410380030070110340c4071600e5a48150111000c1c40401201036049100328050100361100900c000703040f4580d260400320241d07100b4901900e0309801d0086803070000c640d50720032030790084000105540707807191841101c4510004070700901c580039034010101c410708640e22a860406854648a100c0c01d2801d4102e00c01414028004000b500c0e5034039002c2c08d82e401d641c0720b143c01d40c0c00761800000d0658440c0c0410700f060006508070714941407641d401900c80030002c80055410003149280000c0303c03141c00d42c10354020002018096644c071480c5071440c02d00610f0317070015080c0044200d8200c100075025081c3d0b12890341d041d42d0192030030f21800042610114421801002036082c144091100040e080107002c20b48801d50071603d05481d600d02c141c48075030102c403890178082d400c02020042c800780c0020300d00c011100c45c2050002c1030143e45842060740e21401078483c900803001c0381081054034000611100042130302d44281075041040e8029141e21000d0301044180441201044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 113028390 1250 113027140 113027149
    0x30e10270314070804030b010603150905060d0609080d062c1b0a03060509060904020d03030203071206030b010501021606051602060408010c020a020127030f05011d060109061a18 78
    0xc120b401c400e00494848003180340c1a6541c0e4032074041221008100400002c0d400c2c081d00603410304419581d04e58815a0400c000c04c0024076000740310700d91104070040043c0c0413400911030b48000c60b0145048640d100007d0200c90103850070341e8002011008032080b0380d40d501050300507002041c410700d010541c840e1544410f000602c82480402d50b90442c0028640201903015805201140d400ba900c83e443c80c2d40d0700e003c10410250444000e0f40010a078144440000d2103980150303846415070600070401d81c84039040c54100d44a07908221440310341040103000c1581c04004000303c40341145040c0c545a41000d0005141c5e004000040100510210150381155994000e030b401900100008008100e00464000d5490840c040d059000c5110070919200d146009000a8071401826100c5040781349903a541c1061051640801d884a544c3e48044000e14800b0550b5820030101000c011b0400d541803607034040c2160f585900070301c41104028440b402c001240c0b0191030ba03c03030010090241980145001c00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 113029640 1250 113028390 113028407
    0x301b040b030f06010c12050409140601021b0406090204080606041d03070b0c0f0d021306020708070b1e03070c1a240a0305030408010207110315060d050f010c030e102703 74
    0x5001c4000c00d401b81401e182d20501800c1101c0d1411400d100144954183c0d400c2e4000a94049005820503c102d03115650503003408128400b01034400602d0b103588010302c404a812681201e01c0702d41188003400114581030061039181449422461082292440d003650780344130306030b4005d02d450340f004001842c06070584141ca5001c2c000c8034446954031001d0107410020b40c406142000c0e610414000401c400c1e200142040071b441000d001499010b003001c02d07090310343d0040b207410380d80c054040141d0001002003901031406200942c464500a0311245440100c420100c04041c481c546940100046185c0650340c500000e084928504101c002d000003050030108940c002602c3c2c0e100016000814241c158014400940203608800100c655901010385500d0542035203c8010140b6010800070b1501d0040460072034401c000b100c001403c4c06d4a0305d407d61300070041820120350b691400b101c5c0e0140c1404121070890103014100440581e00590a48550845040d1030020749080c82d420101405517641 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 113030890 1250 113029640 113029643
    0xa0e0406140f06011b02060a110a0203070602150a0510030b041a0103030806010f020703110103050903040e011805060609090a1d0105041b080f070506301b040b030f06010c 75
    0x4907060361074180d4416805240664003d0300240ca500907290340c0c8002c511100001c00e80c02041d05103407041c481402c8900c0180c80583d29071a010312a03c420059a04122040080c50103070040c1c0202c0c0072443c6d4850f040c0c00020800c0340c103541040104404601c201c8142d100b9203601ca1170700b4031503443d1810111608009490b15011071017603a800402410382211080348140802d076a007a24081c0c2755042240c03204a20310004007240409660311031698041c1d0055544000c000044908196560350b640705102c000703a1100240c60000c0400c52014002409007a501000c2907031300c0c1d03140c0800b040126030303d050000c140b03c008942d102d02820b681c480300b1003d00029850480240907504140c14041500400c030b040484065000e548006030030704000c110540d2120b15013000e02501e038505000e0000642c485400f2007148100c404c0c05c007040c035140c2800c040c000030500ca00c180c5c0da45403102480c0c64445080401108214050208000c06481901140d0f4026a900c0364071206441d5880141c8400501e1a0f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 113032140 1250 113030890 113030921
    0x51002070302010c0f141b0d03050702040c0507020d0b0619050d06090201090810061d070c03081e07020d1d100302090f03031b0d0e06040303081803031e0907050a0e0406 74
    0x21b441d0200d0200107a40c2030001c0703200342d0000c44518083c1c02c00c444d91410321401804a401800070030054a02548224045401c500304a8030705000c550000d031104404a0701169961000c03400c0c0015418600740c8014000800a01d90350740c0e81c00c04c00001c49110b6114401080180c5602c0b5210071a4450181000108940000c50b803540c0704a0031204083d00103030082c9050540d10340c0490800207c1c2c42581402080e594a034603080305840d807422030b1444401000c120700840e148058002d03040095070020f20410580e80a085103400c030b6240101065080403c1001607550310092441c42d0f59015842c4d09001000d0800503994184040410b0325a0003601c6210780c54040820745c0c220314411000c0360300000d070169090360350780311000e0015a518840308401d9904103805000500000b07004100003078014480003c0b5820004100c84814030390b0b4001c80380c0741321030810421039030007007040344204a8100780200040c286807802c02000c1101d2494a00c11081000d014201150600c04542c0c40152090460740 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 113033390 1250 113032140 113032163
    0x100308120a09080c01090b0f041e110901060e03060f0c0a0e040b040f091412030f0406090c030309090e1f150312050403020a0602010c0206060f04060803030907030b01051002070302010c0f 82
    0x1d4414001c00c1d070240142c400f081904009221000c00150461050f5880817a0551586600421030480c03422610708441e00c2c01ca220340d0bd00c25540316441c683c001d00c850340d15410b0052410b82410304016015103032103604d0051074284404400400c00b81c900601036481d050000c5c0402c3c10004001c0c02159520580040c07519038809200201c0b5006030748928080d00c000946489445440b80d650164269200001d04085c40858090f201c0c5400554019008a0002c20201321544500c0d07450b0020364811404075040240800038284140640c82484103000f015003030551011900c480261400d459031081107a54206803124403003940507100256405c20410140c0741c1d8220800380155109010507403013a0822040021b200e0301c14082c010b1494120b0b0301411407612908144445401c0c0761442036401621107001080c0d4500400181d4820815075004242c03052440c01c20b2010741c80c0c181c000501800b001c0e44161b5141e82c0004640e8112642132070165800d4000e81064500d201c0b2520000300031000b05c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 113034640 1250 113033390 113033407
    0x5040c09051206070318030c060c0c060c020a021504030201090b03130816050c0907020309040b12010f1d07050d030503150d1407210212100e03070308100308120a0908 73
    0x950188136143d551020400a00c078800d403a021459143e40c024002500f440d16a800100070360440c04031310344a801c04851102d01d6942e44001d4455241c000c00051740440e0f80c100641c134088050440b4107850400b240d15203404e58000802c070441c14040e403d0300c0e041c00030100d2400b080c1c2c800381022950f085912076880d10000780509800480c00301058445d4400c8080e80d138070b20301d00003800038052201500103500d0304000900380400392071807800c00c2d944940c4501c2e59500c113183c213005402c0c1c00c080540d4002a14071980c4042c4c00c2c050340b940c0c1562490751008606001544648840242c0507806080c1070b0b17100e0b580d40781214110004245102d401c410340d04401d400700f00307110300c06801301d000b410155148951102958541e01d1804440041243c000c604004094103103803500315a003a02c65002c0c3c42c0b4155120054405035076680c2c0403801d0342d6100040e401c1c01d0541c4a40815000b2182c120605031061443d1164509402013602e001c45c00d200d941b002c03c14503125a4045043d09174000000d944a8929 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 113035890 1250 113034640 113034643
    0x41e0b070801050102010204140f030a05070b070b0a0608070e180111030a140610050702120303040305070c080118060b0d120206010f060c080d18060501030606030c0501050c0705040c090512 83
    0x16a99980407030a000008601da6006000f9907041c0d441c10707455404078002c20010454012001041c0301d40600440c2d4240c40815000e01c00e007c0a402c84031115655955540340400d54410014917998046180030418001c00c00c1c04560034048680e4800d010440ea215800c800f4074442c0c0c0c8000c81d0740b1a43c07804a07010900603488002c0c5210b444008420424502c86103062035003d842211701c41e40c49440744503655000c078011400740602a001410005084205414062450340185c2d020b801107034001c580d640812001503901d1001c0e03c40c000003480242c5400789080c401c2d03c048000140083d45640c5450302c0c40d2a10180305d00c81c250000a10844001d060701c0c065180e08080c0107401c040f42414002050341c03806074021401d00d90340300880610b001c5d5850141c0d0018402c000216041c0d103808142d04022801c0c50003000d01a6000b0300001420340d10f10301c1c060b104140d00741e102c0341c144801442201001c82001c905801151415180407405d00b410110448502040d60050399118141032410740c4125030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 113037140 1250 113035890 113035913
    0x3030305040b09061017070b160210140406120902040207120306080f030f0c1c020f01060f0509060409030e18010f0609030c09020f041505090306060f060d05041e 71
    0x42d2903100425210320482c942c031180205c4412a02c102950010402155100b100304030b843d8004c0705880780c51b41c5031201c81044d40e0240c05a080d00e0720405803614150b1a00890441c0d2116140c01c040300034509007641803143e030155120382c030244585005001d0418a0f82d4000c45201640284115551a02890702c50f41600c0150301c0040041d1a2400c04526520001250f649580e4400011401d09400031031205c4035034861085600c00307020f51501240540003402c242511602c0c650054110003e0801846003107038107a0340410780c80059070a0801254598205240e0441c4042e9408610000103050035903008002000084d042581300d0305406103500c40e1820740341030b9455080100c45082e66200225000c210311b00000d0300d44070164000300a09620769000f0084941c0100045081c29a04d40d035800054040c41450000b140c0300051440381450140456940480102c8a81e10f2080717030007000c00d409000d00303041560305a69880100b000e210b0042916480301c2c5071b4584000e440302d0f82d80740c00d4041e0380c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 113038390 1250 113037140 113037143
    0x9010909060e100905010803090f0f0a03051e070608130201030b10090515031b0304030309020d08030a0b0301290135070201092f0904060204060e0301090b040215130303030504 77
    0x444201010404d20ba05006290403903c11100442c20840000104076440001040300c0f41d115a0b810040411610381b40c4400e0011801640607058488041c0500c1000d91007880c17003000150441c180900000c1d40010845030000c66211140c400044c940c030044c0e00800366004880e90011214035540e90055100b4046000c0d103205603440c408030344008045103101e002c141e80318415a640d030841900a80798401c06075610900915012a040c4195004900054101e034002d403003075440002040f0b0072180c18000e0400400066000302b29407008040401d4031170303002010400700f440030740c1e00c8007149a01c6154074410110441c42903400c0041c2d40c0802d11400300301020300c18003120180b0000f0301070a0041c420f41c250301e500b280300030785030034000e4002042c2610b0888448541d46d10412180c21a03403030301c1500d80e10403407203180d00696aa0511202a0030a0385034041c50340300b40c1c1801e600d00001103501d64900e4000d1b07416581d42203102c1d0043d002c07418900500071450287e0350007a00000c00d00d64190801170246 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 113039640 1250 113038390 113038411
    0x222020705121309020304080f1e03040501090c121203110c0303090307060606021b0d140d1211040f090b0307170106031112030a0804030201150311090603150c09010909060e 76
    0xf50396107104409901003118058030825040c01101b1286910b41c0050407442408444445103003141c1d40341300c5c0941c10540701525140c2d52811001d04200c1200c240501034000311000d9089a11540d0300e0210f0030030048408020103403666000b0501040807820349284054000c10b4030f4881ca0804401c1d9941d800444040e00d5980c01c00400007100ca0005c55180142c0c42e1107085251281d5851082c0301100004040450701281442c0341c0f6119014140b00c02842884160313610f040307207440f01f00f11a080d118900741c04007892204000030044008001200303801c03101c00b100c01007850420040083d0030090154402c2590440030101d03141c404806502410959204100510240e070505060229005d803030000d9a030343e90710030170205103244d009007002ca074032a10a100116280050703000080200e941940104c3d4101000b180903041d80c580342c40c038254407200645c001d0441444d00030003508101800f8050911840c8009505001c0e0792156000c100508500c10050180c21754500742c1c40b91040c000c880c0c802e0700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 113040890 1250 113039640 113039677
    0x50619020f0301090b0d0807030c0b10080a150b0d0803090106230d0606053607020a030818030403080306040f0b061c060f03060b030f030304022202070512 68
    0x2080128400e8a80e82006552168116070070101c40c0d6000307081c54180c19600010080b03160000038807600c010003d29209599440c4104100c0c41c01d0403030303000d015203000c0404a40314070611985d00009492641b4541107140d100034007444d0f000e4100140700c407035481d5070009403814441013070100d241c0c011030081101c14000c009290740c6084100c4006004c030380700810075140100c1c015051800c01007994801e4015140043c06580e1000011400d0705148c0c0c2000801e88a01c1034004094601f840c2610001041e8040c0c039070500d41414002d4648403082001401e00140e0300108800705074080200c02e030f40c01d01c041100d90700d076101c3c1459549a04110307806440f171400c3c01c0e8122004030240c010f80003070b9000500001e08081c0100c001040401d01c40c003406c954540d48840002e21104427111520042d03008100004075600502c0505051010344008036075641e000700240001078031014000004000c0c8109800f820b48007411101001e44a0303130300c01a00f284907130641400d1072204c01006002280a0765050501d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 113042140 1250 113040890 113040931
    0x180c090e07080f03070609140106063216031b0309050f0d050a03030203150a0b0a1b110f0d14301b07050904060204030204050a0504020609010e04180506 67
    0xa540c03c00b03045a04003500144030103400500301e5049003418070310640251001c800401010303401c641007940901c0000302e40c0e0500d01401010300c1072042542c40c1d14004051412400990918144034102ca0282c1010000102d10103041c8207071001402c40c3c01c4014103451100a60400170a601114028144036003102000e1001900c2d200e08a84e603034075401300140c01a00c0031618160029040182014000450714034903213280e68900759220007800645200b01c2d202e540d43d4030024103807542010901c08034145d0a0070745c2c0c08070383c1d510034202d007c000445111354280c02c8400850400c48801ca00108500450f00451035080008580d900a0800301c00420300d4040e95080300401d0303400340088a031120fa104104807040609440d40042d01c146420045540065680c008904a000100c0c1e041d42c180740d0100c0c05004502e4036004a40d005809040c040c0240d0500390002005c40c4110200a41404550803078034611740c540b60800d10100c80282115254a07200e414450389500046071020a40d1002000842 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 113043390 1250 113042140 113042143
    0xe091f05040605010219050f0a0b010e06240f04050402030f04030f050913090503220819020906100c050607030b090604021206010f120f09050c01020601050303030703180c090e0708 79
    0x4215141640105200380d02c1356030507038007040b0700720086e140b80c088c00c0b41080824500b00104980c0500c142c0701c0107004d40c540090b00c0909000944058801d100311042115140705111040c0c081c420850f40c200d80c0c80f2001c60500c0d01070302c43ca900a40d0041d001004100d5104903160340d1920407406a1500145003051041c100c9171886402c0c100ca030310070490641001d80e03055903409040c8851003102207a180002c1c69040f114960381041304061200c5c4e014a05120706c6909210810910b000e0082c10740c401c00803075000800c1c500c0c008219502500750030076043c5096104601100c205a0424151082c9041194005001d0304903443e940740212103180c0815500d0402d4800ca402c0c2c040c450390f2891081c3c581c1c0c401100d00f80d05250855003000840c641030480d990180c4144d440c00c400c03480000480e1304580c40c3c0b050070301c4000030071207040d034004100401c01510080222a404145031500050b200c039050780c4e0020b80300c800400034055143d0203c0108841c609170348a200d070300d1200d608031000242d4480445 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 113044640 1250 113043390 113043401
    0x90c070b1303080c092107030c0807060f051c0f0b031501050f0906010c06050f060f01050307020709110c07090609050f010f0b090a03200405010b131202010e091f0504 73
    0x5000a503c1d4002608101c0000050080104010b00d5054980c03020816403510321421380c5800a1500940703000c001f0040c0601d09480240759840c003800d1818a419009000b400841440d0014441c001072441e50f5444240d1010304040803010042240030160200384000b84004081d079806031040e6150100c241c0e46400b022412120001c000761a101c401c03905010301003030003628590521000d0145240081c189001d064850403030784544bc4800d141c06010400b00034148070529050003001c0003070220940d8046600c9040d03036034854000c00c8031448902e884419108265040405005205010801e01d1440e00818211184040f06004a482d603001c00d528003042803144030040403807518100f01c040200340c060500c403a401030407400065500c0d16025070101080d850580d086000c20864105894148100d501400030641c0c1107007031030410307001410303242c5650282034404100c3c0313000001168810303101c51104c4030000d040c5010134246217101c180501b00040d05211407238408080440d240c1407501c0342 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 113045890 1250 113044640 113044643
    0x90b10030b06030f030d0f020f07061b0516020d0c0504060b030f0a0c0c06050705090402030a0b040c09061b0203030d0e1b0d02010905040f090203010615020f0d0e09070905090c070b13 80
    0x5541b4180280b4403190040c01200c4007070040d02d400788485002098850f0151020a01801000c101c08422060520b2581948004a0144402408508010000c42208081095050f5510359120031141844400f401c1075074040c50740107081c1000440c0c4010724901840c041ca80d00742046145880d424010416034180c01c1080c0d00040000110b0340c007041d5103801c41508120b079420124a0891008003042c2070368412114075503039039200e415038401820b25110305501d045c6d0601d00039400d54108074004010200603008185004000400d01003599418800c4860030301040c0380402c10b200807551001d44640000e00302c481d20046401d81100310b410110401410194141c1d9200c4004d814081000010040465180c400640c4c482c10100181c400f4440d000280c001c40140051040140304000d1a01d407070507046000360b0f000603690152150f04503514004078001150954155603031100c00702e5a5072a00d03800241e01c01d401d0428804541c488400a08500d070003440ea010440c0c0d0f481c008080e242802480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 113047140 1250 113045890 113045893
    0x60d0203120a05091003060602150603030d020a020c03150f09030403031b050102070605010b03100f12030f2312071803060e031e042c0a0b0103090b10030b06030f 71
    0x4069030005003070303004000d03901050030301e9030074508540b021a46000c44039030b829000c04c5c3d6490317050000340d40400410000a14110174a041481e095002c240c4074000d04049001940e004108a144140240081c400105000c1c088900c00c0311012418100004203030b80320302000320a00041003030454080100c0d41603d0f015141d5100702c01c48800284550814030005450554dc03d100c800700188140c0030345802070000d03000300b03512400c00c1d03403a0b19035500680d400004030081c010f000b000800011818541119058203124950303044c58201074803c040540302c0102721000f00310310305003481c0019020f0300d4140b49100c000802596001000e0f10ba42c0340104401e0100b1612103c10400111075801803030000743c1d140140c03420503000515181c48071410107060a942c0101040c10b019041e214042241c25000881180c43e0f48401d440140c28440d40180c2400360582d1181005042070b40290455210240c4c0f00e08121040e01d0b10009110310b0f001c8a0004891030351141002c64942e2600080d4205142c40010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 113048390 1250 113047140 113047153
    0x501051503340815010503010f09050c040b06070b04030c060c05090906150415030203061206060d030309020d0807150b04051909050c15040611012702031e0c0405060d0203 75
    0x4100201d0210000712001c030b00740c41640b0126203580140b10341451000340681003001c41d414a4205402d5030100015101c0081c03400780c140300403d0000a08040c2c241055030002891540800490094810140003034540e1016030284030400d80d000b04001c04032409050100800705007610102c03000e2041c1501254000d0404010500c5850a2030120a89602004960b07241543d610804c18500160080e0640030990100c1007050604281010001c402c070000090880341c5440e00c001520002044405401c16540302021001c40d250700620428403904441d1660b103072040742c94414242c14081100400f42410b00504003454101070007843d02465070803030604c860ba908840d0b800d0084c640100c0a840b0781c81031301c41c05103090300c80050081c180c480324607445030b1f600e082103001b4242e44041c26103004c00e0b078541400d410503000807000c0c02d0070b445c61240e2110805903690002918209001d01202201800044507151041001880c0140c0206c1940c4c18056030b5200c90421005003007017103010f5010b0700b0a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 113049640 1250 113048390 113048443
    0x50703020310180906050a060611120f03040309030804030b07030b031204150e0a030308010302030f070f06030f02210a0b0d0b0601051e0316030b10090e0705040506070501051503 78
    0x2400140040c01001d50f0000b41100c41d81c8503c81502c03001d03207000c0c40b00e5640d00001d00426900203c1d1b1041d124000009007c02c151084401c00300380720b140c03103611840e0030120116040502c00c08a03000159040707a0001c1d02c0380c2d100d0600b0f40e4054016218076003ca45008012426824041005101e080c1c00c2081942003502d00100985c0449031041d11104004c02c01030394851030350759411004055030280d42c42c0400c40d0304610515240c8125941c0d1a80c4680c0700031401c2001c1d501d55503440042d12000c2c035011503402e8103510031901901a4a00e8030f646001c40c030054440503055040309230700c11182050140980d240e20420320004400b400d1000d400000c006c8000340207940a8002040d0b04820003800c0c800c00050481181d41a80050f1111150248203101711140c0580c9800384000e991401c403126a2200d030a14400341c0908440e00c2200e2107004c40750b002030071007401801a01c00402d8003804280c1d4858287c80d18500030182116020442c0d0b100c0245203000f401c00003244164809500c1030440c103003160 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 113050890 1250 113049640 113049659
    0x3080708070309020607080c0609072304020c0f1c030c1205130507080f07050f060307030504081b0a12020c01080a0b041b02060a0b0609030307060e0304030210050a03050703020310 79
    0x1040d501c24151a2500640162100340080032000e010300302a0351610480340106040c10300c003030941c2c08158010030040c860020b9414000c4102c03010403c1c1c01c80440d59231801f09001e402034450080303060280d03034064070071801e010588008a000c0c00700315100d0001720390030903411a03c03d03483c024005208402c5060746214280e2010b500304054400c3c54441c103076940c1d201d900d0140b85400020140d00444603808290008100080107807c0440b0724560480e001c40110790103000050500d010991560701142c2849028801c40e40020986000480b10780d00c07034400c0d035940e0008150b0445800e4020120064503a201281d08041024140e4a04120b030716160403400184c61702d415145d5115075604a2080518282d03054400124000e80103071050703242200a40e02210185000342d03004250400031440c0640d0b012080b5030302d42d640100c2c00501d2155052005241d0b000700c0c1c100941100c810040b000c401600702c8040c00d03c140702e5035014000d940e1204411400d0340819079a45824088001051140501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 113052140 1250 113050890 113050907
    0xc051914221e0218190305030a050d0e0102030408070b041506080d11030a0903020d0602090603131e081902070b0c06040b01090603030e040e1635071401090e090706030612030807 78
    0x170b0b0307003101800e50b207070344031142141e100c1002040403c00c0026421051062402009068480000210f00754982030311000b05910a207100100140c0b0b03000d00003400c00c01001e42c0344070000c4410404101554403082c1071503a400506440c1c0d400710304800c0d40030785c0082c40002140c040e00000d9450141e600d00e980c2c01d0041d424030707124044901a800703201114950b1902d801941c4a8803804881c2020f03330280d0b05140d440562102c60f80340c110080400c604e008540300ca8112081000d004a80c0c449074021000201c2c2451120b0300305491040c40012180c82d01800000c01c0c600a50141d51440300b940d0f07036100f03e0380481d800740c40014007051400107042c00f5454181e01c100f4034403265400f547d01906984c5031445d5080115045a0984110024024050600b8005500a4441c61409a002e81703005c11852952141c072032044035a9820300710041000742e40303d106180b000300240c4641403840d040c858040c42e2660003a024040000c1c1c50031100081102058050341052500361f25400300d80e0311102c204896218 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 113053390 1250 113052140 113052169
    0x712020919050a02040501090503030705150a0204030807110a06110d1202120405010903030e0102070314070201171303030c05033607030b040c051914221e0218 70
    0x1c1d6120441030100075401a18455440e803000182d5907401c1c5000034090b610315421440c0079620900c8004000340b0b00094040344415252101400c5a1764034008001912481c0c0004081d01c02c0812903c0400c40d0082d4890100f0308101c034290b4950b500d606080703d40c88009998014154410b140c0c4661050144040100c690900540503140c52001540307042e1501080e60b00b01c400b80c0d902d084003414142d15105012464515000035450700304a038400804129800000041e194030001d5a8821a8043c11f00c1c0d1a0180100b01d09001d2460300f243c2d2198413451610080d000f181c00e0205100560341b040c0212841840000c10b40001503162030008c88064480e801da00401400c0e046041600da8000c104040c01144101c1c10010585020702d4000c10784445607100e1409845826007211107040c2da070260900b03803841e800e0f20111040c1c1e02c00020b0207155007000102c0112221500641c02062140c003d501e62403014860161440a01d504007400c078421118010a440401c02c0f9407030300c61802045400c0d025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 113054640 1250 113053390 113053411
    0x112020406030609050303061806060702010518030d0c1101031413060603150c020f030301080712030e0604150e09190c09050306150a080a08040501030902010c0b07120e07120209 78
    0x40b6120780d0750100b15240000e0550311548048100501d03403a01d01c82a4050392680d0044080c1820290301007485802940e40083c103101e00400c0300d01d51080040d101c02c0c0e140f640141280d02c1c03016003207c00303044000c8060095400100724a0300712310550090090314840c0014244000261341c68603c80c140e030200c101e40c00c46e45076403a49030020105621064802d104407404a0000750b00d11000c3c000f82c98021310141c428030326041800100207c0d000810f03440201d03201200c10000808482c07400320342c1a4404000d01d43d000c2400305020486600900003840c081600c0d840d86164400507000f081203650044500c4054103030f254103000854a115002290842d841c1d00345800e146840d40002030400c00226011200340003030f4103204e001b9207805130b2140003c014486c007070122880191148800c1d441ba07802414141034981c81c1c00d000316403041040c28070407a084040d010007401c0180000740301c00d02c1c000030b4000003401c040b144d05086401250440840799440c0d1904411a031aa0038484820801060706891 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 113055890 1250 113054640 113054651
    0x70203010609020306030705030a1e03021c03020405010f02150a0b01050403020d06050703051308182101050603010c030209090103061107210206010f15030e070b0705011a04090203030301120204 85
    0x1610240540740240c0082c540160300c03071034a40d00b030500c0d0030550741c445c0b8441d82c4001c64030f0002c40c01400486c85541c480c00d60850600146c2d06003689000400c480821540402c0d401e9000e401c1c0e4594003910541324245d940351a02001d104d8200e9071081c016190070000a180710201c2c2150807658019214101c06050842c2450369940000f138a9141481090710038036224820071407010303854494a50301c001c1c4040070400d0030b60700751248034940c014980b6030039203c411501c3c5010242d9404a107510103281075415010801c1c45200c0040c00380100751070a0b4080d40c05c2039040d034150390180c0260388070031001400548080c0e02e96142c0801500d011500305811000822030f810102d04402d5a03500030b010b00146000051030907140003460550b059200c491001300b07000040c001d40b86c1d900104401e4100c1d80c038010405601c6513804d03d0030920f6a034446005072f2800202b005c1045419004040023455201130456141d100200384000c0c0c500d4403500135459042040140407940304000400391450010b42300003503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 113057140 1250 113055890 113055893
    0x303130c0503010606050309010b0303030403170a0908070f0b0906091005101e0e010b0909070e01170a0b010207050f09010b0a09050415050306060d20060d110a110601080709020304060207 82
    0x31180d13940c00040002e20000208039203420240950b00b021001500250725510300382e1002404070008041d480e2090100e4000716500303104a4000b01c3c62260408130003555130480d860502842c180502c0110340307900750003000925550000c14001c0c8910030480246c0000440390346040001c100c02890714000702d282680100e140c00042c485130f90a4249840d071031042034208001c54141a50503449a02d0f0040308105028141e202d0740782c200c1e0040d007a070405032507490802e40180c58100d0501704401105448400308401540d03641c000c0b0880312020380070340b100d054444082c4041d511b0501c4000c1d40280b140c10040104d8100035004202c2c60101e803801c0c0007100c2e00ca2002909031022007829041156400e0000c1c840da28081c006142c10203803ca07045200e06185a4803180c03034200340850380c02400449114244140c84100c22540269201e41040004842844c030008040d040403142400259043c0e42e40d6142d9440040c0a40c10f0300d61a000402c115131901c014600039600050080f508950240440d10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 113058390 1250 113057140 113057143
    0x10923030c0706020c09010b0301030f0b06041b0504090c17220f050a0b070503040f02151201030b01030c0f0b0f0a0e03011b0e15071103071e0302010807030e0303130c0503 75
    0xf43c00e0307503805880d841104c0d80c1000071000068000c0505840d042004100088103d450000c0c0b20740d12041000140e030b280c02c009402400d40003000351051000c0c0c601d204891740d00c000280184d50003640c00f04480681c03c5002c95440e16030707202e0740508100f10b8010402c079032022006040f041d8021200107200d10f40341d80da003122080030603100312113980c0094042e00c00c004591401542c0300c2c005103011400c40c90141c460409800107400080e00403883c60100003c2d01d400401100c024480030510141c55503501d01d00202044002d110030740d40040d900c0300218001c50504405003c0300c2040c03070b1041c1014403024004400340d01ca1a8600103110b103100591919440030700400040c002e1021500c4241159020080c0850020f048628410280c40c10012558414a01550400b64001c0c03030100380d268100300882d10b00701c401c2e00a01c80d07181c44440d021100201400c80942968070030703a03580c40e2035141d5403c15001e59000752102d00383c542040c0001920144500c1c40000498091800d0301d400542d07900110703 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 113059640 1250 113058390 113058403
    0x6060f091814010e2a0105090d261201090513080301140a05040f1a04110409241203020d02010515010c2a3215040306060b0a08060102010923030c 64
    0x350017807050340f91102e60701c1d031031013440c0e1001c0c030f50030700b081454100c5000c0002c1e281482c85100819003c907407040c200c5907d00303401d510018a4481000c499407040a1082c84017810801d105841c00113080074000303625401d0642e80469016400644c00341164203041081c0403603000310301c0e01500203182004c0001e81e40d0300c1d0700400264601d080800160518030000d41d0803d1501c1c92038081c001d0382894452070703042140904840031910706030b82c00a0401030b4541d81c40c0d985501600b41c2074050700c0207140402e1201c0c40921483e42c5501c070307400701d64038041410016402c1e2501181c007071180508204401d200795002d05104100e040c864401480620764400740405100c07489400818000d140c100c0900030006000e241202d045859514501400c1c1840324a0018905c1c0c007007030500500035610144c58480d40e060070780d80a198841300034084a07840b01d0755400f854210321004000101a10045032240d4010b01c1004c0c03c0d50b8000310205200c04c02c0102c1000709080044a44405210400204c00302520031300c1503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 113060890 1250 113059640 113059663
    0x1103030a090b06032a04020f0f031e01030f020405040201020a02100e0312030c0301170a050a0501020d1a030604031b0b040506040b2809020a0503030706060f091814010e 74
    0x45a40441c1095200b40c4001441240664008040203a2404003082000e500d1040f42c0310003001002084040307406801135424008624001044540320464004061881584503143c108222408040c000e8899102844098000c541800700719001d0308042d002141d200d0b0060045901420140e80800c0746804e0440100001404c03c01d4102d0162805008850a01c0c88402e0102c2c1107003020008480c440c131042c800c080d820070348926907a91a0a05020781c41d0103540140c1641c00d407008030301380f140c007035480008103000d01e030315200d114000c24440c410401544000a00103201c0c60b500e6907000d42c0d062100341900c40394003c140301c1510000d500341d43c0312403190b840752001c1d0800307080ca0300d44030051501c050214240105407032042c02c4811180c8294160b220007030b900229141c1010b0001c56107981081c0c11241d01400b0000f03044040c17042c9a00700340100c0b034260000d0807003103a6540c200b8048408181c291800140712154100104074018690605200c0840001400114a040561410071415030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 113062140 1250 113060890 113060911
    0x18050106080c0d020315090c0a030809040f060308030402040c03020405060a0e040e010608060f060103060e011401020d020d050702060306130204061e0815010c1b080a020a050303040b090907110303 86
    0x1000e004050702800b0350401010140d81c10140000d00d82e000a4a4100c01d1a01b0200c00900e030380010304440003000300790414080513100001072601da080c04003039075000c01e00590255003852507410b01c1145a02c186402c4236000020076080d5241d40d42080003401000fa4405c1c10543c0901022404c0d5544200604104a1945074540d010500c00148416508082102195645030190030460f1040100d2100c0c0c0c4041c2d61410365041e0b5176100c0068000f00b490790415090132401130b0010550749240d950035228078000740c0803203650405e800400c0380e58044400c21440001d506000c1c0c40c1c01030408802a5421500040c21000c101c0000403062003280c0050740501e00090213148407012128443c00402802469444c0030004e502d40f2089050401d200100000d040180c83c8034014180030007808807120034034150070058007050351075540795501c000c4410182c0c416406020000755901d0000701b05c404891a500d812070400314420100440c401e401000c803000c1c011030520845000f4414001140f14004611 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 113063390 1250 113062140 113062151
    0x6180503121c0b030703080705010e0d09030201020c030a050c0402070f0204090c03150606050301060c030203071a010503100614040e03191d04290f1518100c15180501 73
    0x205802c1c1d150351011010003000d80340c40000c04554401207001c1c410307260000000350b80c50006142c03840c010402c1c0002c0d100c213070140055408a0962020070181203d000b613007180c020314a14020141c890300001c00c028101d81c0042c41080180c18980c0290035160f006040b0b0308a501190b8011506840e00340c44125603510a0460520800c910f443c40c2c404132061280c020040756042200c09041031006006400c1031140c0c540c2c0c1002018400c204480301c04d0b90041581500650300c0d0f20030358042400703004581c828000c0b120340c000d8840b0288105412a01005020800696071206010092480700700c1e0040c240410403151150300e66030f04607100e00000070f54807081d4030408181c00a011020175400b5501c101c3c200441d200c071866000a280030030700c000075a681603d968520006190b658109c440f190440254150f42150803203d0020f0984411b60200301d921400201c02000050861106204040750440302c422010603000380c2e001600c0380101000003a80030b9940f40c041c030b0040d04124111004da4461 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 113064640 1250 113063390 113063407
    0xb0a030507020304080607051b010e060a0e010b0102120d060b03070206070e04090f0b250c110411040b0304080d0608030a0f0f0903060504021c031107050105070201090618050312 78
    0x61154079030101c02407010b90304240c1040081600c42d000a0b201c0f108202c40070484903540005003d58150902c0440001c207d05101426031544421040300c45030403d42c90180d202101403418004c0541981050340500f020308001e50740008980c01501c510b1951555400d0081424a00500298022000340d0002c01481ca084040244541c07010f0900f40d01841c10a01050009120084107403c480d500400c0703441c007a0380d0102e0700c00b510180d080d81110899000008983e8007904698940101c601a10485d526048460242300a5440031a04082ca6010401041011840381c0001d140c1041c440c0050501e0710800c08a0710080e03803e107070002d00c696000020886a0b05401c0103030b00201d2191030900c0d185500400d000a06034002074407028145a0711031002404544d105440011500c00d0b0107102c2104411072305008108081086108481e072040c0c060104e4298055021354038030a41c16541e0b50241810250112400328034400712080800181c00c0c040350341e6409000d11043d030021060402e4499182 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 113065890 1250 113064640 113064647
    0xf0204030c0e130c062007090207020a080c03030304020112020702031204090c0e09060609010203070c0303170108190f02040b030d050d060e10090507090905040f1104020a020705040c0c0501060b0a 86
    0x26191144100300d00f03640b007000543c2c800445003241c0d824201460000d0103455000488440b0024120703c0f4065400041050115030703001e059140d00960740d91100070b071942641c030790303580040c0302c07486e41035005100007001988908950300400d40d40340005420280f01e580440e282603408a400c6411303560100d01030100390078920404107088a14030b4031084401030000840c2205074040c0410b80501d42c005040803040c0d00800488140c030f54040102c250140e80c07410010b01041d290340030f44140b0306c1007400015180714000f40c541803a2110135544010040d103607035054011070b50030004a07000307074403030040d8a6141d50a1020f5144c003a0207031541665410180031410488040340c016005200407a418000340f128a11000d10a46807031420000b0305480e10101a82c0c0c6603801c0d030189044504190400003040046041000d566100c0c400c009071080c1880100020380c00740c042407400503405006d041180303150503046040842d0890400070400c080036100c07242900cbc40741d00b108c042140c00064070010242d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 113067140 1250 113065890 113065919
    0xf03060b090a0203070906050a0504030b0a090507080a030906080a0e0102160204150602070b070519031205010509040305120402060d090b06030601050603070221040906180b060306061c0f0204030c 86
    0x40c2542e0443c9946015003000d0401001c5002e454100400403603c0e0b50001d014408a03400346400c01c065000382e00c2c00d40000c201805500c4000c42e01c030f0181100001d0848000946683c2d0a40d241d142e00c2406414940c04540e21000108444401612840b8008010200b84000c14803800d51184013006011140140020307214020030300c00e0317101c5c481034040200e1035000c91003005540d42c040103541d50300a50b08080d4502244a40c4441c0508802c900e03260400d500f005c014104c40c5542c205c00e00481c3e903150100000300b0011036000c0c002c0f920800c05000302755002d09010303510038802000c603030510b00507076000740441d40c40500c200d0700e00302e07030070103000c15441c00300700301c600401040700c0300340c03840c5007148000b52603103540030506d103000003440f0740031100002200031f80d8003400050b14204901550742ea200c18080900c0794206440f6498107a054240c0d0404a048901c9040040c041030b14045290344103003500ca8450146440281d941c90a1991441761400104002e45c0941c610907440f50400070000c140e0b00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 113068390 1250 113067140 113067151
    0xa0821030c040504050a06080f0303070201110405220603080301140414060f10020705060a05031602060123030307080d06150302071a04150905030c070504060b0706150f03060b09 78
    0x1902841000400030340070085505039401950007084c2d45c4c8031441c0c40070161000ea080411103000f904c0042c421018000003842c4264030320b60080c002c1500d05403100d01c5500ca50b00400b178124030b40e000c2d000c0341030304034103540d034080c0a5800300060b070f140e92512040040d40003a0022100c1c1c0c0742c0010100761034982802030801c2102d100544400b81e00b08000060084001c121105014104000d48134140078001c1c40300c0401014040d0a150341d845840d03000030100e6200302c490300080000060b115007150b1000031098103a903031001481c400380c18070720301800300504c1403090a03034540b0080004200103006040900241c0150300d1010985608112603a0300352007c01110303004241c1b060210001280da858120006440080d401900644540c00d04101c102e509a00700e0108030308117a880010032500200800a8852000588260382c1e200c104010035a2913500c1455100d8034244511004901941e100006248600e40c1402000307036141e88002402e00c41d640700352500d640d80c001011543c04e140c6500c030703400b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 113069640 1250 113068390 113068453
    0x1020c010b011806031107080c060402010306080a020d02120709060909121d090a020403080c0703050d05280309051006060201051e04240609270b0a0504110a08 70
    0x4a210056a0240c02d44a10070007041548178107024020405c0c91303007104c47c11030f0001c1c002d950300c092000c0c1c03059840c031007502c0c01c0340000d141102c0040e01d44070200c0e000d100d40d64014071224000980e42c0800c5002c441d40d1901d8641c07405040d030001240380072485800020888000701042d48441805c21403403a010158213002801140c491081910001d02c000b05442c10040760344010f192202e40a01009000c0e503040200b002c8000175004502040000ea400304a0b48a030f01107070501c1450b82e50855081c0111a04101425021602c0308544801d491905d03000c5140d514001400718440e4480c0780c070b0301c00c0300300e0a40c030700b103a5840e8284100740c0d082c0609684004220455803042402c3c1c6240c0e0205000184050300c5074252031661610050031140401d060511640180240c54413190240020109640b108843c1c0c01c44c01060940021300148a0300d0443d045001071244c0e550b544048009850010402c5a8988045641802d03c0d0b881c60030140190031600001c0c0302d14903015a480c408400301d040d034450103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 113070890 1250 113069640 113069657
    0x5062107180c091206060e1f060201020f0a030e1912080603030a050901051305131d0d0906200610060e0d0209012105070308030712060609030326070201020c010b01 72
    0x22983c029415608580032040040141d11550411360024105500314001a80d060310910034a006200d030000c503142d076003017140e540361961208168200e102d00e110030f080b80b0109101900c0064020f86c000140511843c080d110b65400c1c071112000d00c060080380444401b40e03421091100640e1025201741d206005900651a0205850010b0101d000b1441070a042203000160f0300c450404131354036203008002c0a800324880e42c500541c400c02070f1400308a000300d000d842403d40541440005102c2d4003a910ba0344a60f043c8030700b800313001c490303440d14246000d445a4020124180040007004030620072507009010381c800a0a00302d0003071a02140400140c4510f200500c0a0003503502c1e4601e0504484501d480c141942c24040c3c110300c04510003c2001d0424002c01c0c0001003803001e40b50045214583d15519901a85480c501500480e41c0c0381c01904000303102c0f04002d100003405581019403800d1024540d802c5411000305074041c000703003180d01c000140d4001c41c0313442000e24240110b00d000700017401c2c00000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 113072140 1250 113070890 113070911
    0xf1009020a031212050c040810050609060d03051e0409050702031207230f030402010806060304080a140903030c0109050601051e040f0b03060406020a140705100506210718 75
    0x8a41090101620b02c042c8007030f6580400b07008a1012400d0741d52000180441e10b01401044000d0300702c0d100c0c45180f07000e03181100350705014030b115242c8280c500800d0000305407990300901c0381c8000f25036011018020200300e2400700b003094410701901a0303c4c4030f08141d070712410705003502d040d91009810001550300501022800740c00c216800b80e4044d1541c0b0f072110078007070f15a4414201c0000780402c6110b801c40062140004e00300e4600551195000384ca8000560300e4090a0000c1c13440f0483d0f010303016130014081c100e2001e1081c8d2290002650107002c90b41002010000241541d0110a14a0751031307544040b01820804140501070040400f2078510300002410210310783c0080352081d00e1481207070340c2c0803400a04085a0f0000c149498041c0840744149041c0c54060029409000c105000c01d4080040242d200300300f404940b03034140d10501800701c8040b4045804050a0302800b42948002821168184840303014005141e0810050040c003805242140c103441c0403101083c8038600c0d5040241401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 113073390 1250 113072140 113072149
    0x9020c190b0601180f03051c091208090307230a09020c03070b09030c03040312080a060308121b0d061a090306040b040302070e0a020307030c080f0c09030c030604050f100902 76
    0x290b208a081c2010f01118600c0d22804542ca1802c0e0011000c812001d400031052001c0020001c02c001042280c46142c4d001c840c005079000170051040b8003503001804a91400610600701034141032001408851201e40c99041212404851418490440d11900101d0003249080303413481c0010030100404500d4442d84240e2142c0707900c51030002608410500700483c07186e0508100304e550704450300d02aa52140e44030300e440c05603002ca5901e034000050000d404507140c6082441030004480d4400700741c910f02411003200200c840c0b030040140909e8040e0f0340304600344e03012080042040001d40300c00000c0403428a801012aa01e100518010341c0d2400e105030316042d140015015000390700501120a03641d00c80c501240ba029540c0c02c00c8a0003072403501444201e80c2c090300a940142d1880e00c00780b200d41c1820308110b5400802f11002e00c2c20895220204d841e091202005001f41c02020781501c07010650500400d15103282990304840e15031103c64076039028281400040e646992184042c0880c203007a40016 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 113074640 1250 113073390 113073413
    0x90302010b0f0616030c02030f03071a0609150d020d0308071b080f0937080d0e040b01021908030612070e0a020d14040f02030105100b030103080c011509020c19 70
    0x132829a1207400c030107020325000b02c4a10071229401001c994140b00311592040d180c0d00140000c48a0054141041200d1040e00300303020720598015000510503560200038217002020342d584a87c000d20410088005a126464200c1c44507000351141c030460b04080000400e0181c11400c10f903442c01003040c000001030140c204031001e020740d0100003510b4001c013400081411314004491160f03801668944103044000b5241d040d8100c0e1002d40703c00750389a680f440c0540b2840f4041c40d5070006000c031141c5034003130310301365020004103403041c4100d0b1006d288508080c0010b40a00f103042e20380202c0441046410300e8000c0e03403a01641204c00c094000245407003c43c843e41000a03000c800e046401165403904021507921892244407449218111401d240c24520440000c0700d00c160700075400e2200184030190450300c80d00c00c0305e42c090f000b20b1039a0b186440381c0d4125004100664115503c07070860030304001c2a001400060203012100503904c5404c0e19407286004d0020b5661400000c601004001140646040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 113075890 1250 113074640 113074657
    0x20a02060304060b0d05060601021504110919020409150501030e030301060305041509030507170301260f01060807090e06070c06021e030a090b0a05060603131104020d090302010b0f06 80
    0x103060300d075151481c00e0700c0507019010703086030000310480d1813409001c0c0002d0140d000d01000c0c0c09840c0340084400400040752003c0314051b0030940320010148040c2000c41c4c406a204d00340c1e01540d0090402903045c0e40a0b03901c11781c000c403241038071480c241ca0303c0040c510000b401440d09080c100400c92207002000c1d2203010510a01c02030650320390014090003120030700220101c0d01c454003044030001600e00038196070030040b030580e418901e05550103495844e02046905036401d03844000420200001145140d0341c20302c5800c0a00c3c02900112803024809004082c0035250000107051036038200000402140c00000707085c241640400103101011760045074008040d078100001581c0c0c0c0301f5950180d4a002110701c200e00554030b0020820a40c3c0300281c6c0580307000703032089006100d030351280401002900d85c00c2d20b91a03404501080410f0544610130b0213541030920030540101104804800036049030030800c01d842c107aa860f84c0d0140c0400d6828402c40200080454154406428070b10100d02180141c040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 113077140 1250 113075890 113075899
    0x10c180e010e0a0f021303050c01080103110618030d09240503060405090309190f0503070302030c010305070c0506151219030e040908031311010503240a120b0702060705070201020a02 80
    0x1040004403079030006000e150100e0313002e41d559140d12030b0719a90305d02244019100350085003280c40135503114895044c12070b41c015900c184400c00c26400c0005a900011440d03c2c141c10300300103240d40351010f00c40128022140d85a10030410b140100001804540c5031800c0c4402c0200010f003084280c0103003e0b070f40c1000091350300050781d65a0140fa240707144540302166610103148800500c188002e1443d050540701401d00202d00203650f0814140c1d10300c1103000007541504000c00c5011154840c0d4001c80c2e001441c1e10b44401d0207800c3d9203d00b0b00b410415140c1103204440d00402d000d0601305081858a8104100d0003000d00d409004141d80b500c5045c8100181008000c071040d84c1c00d0343d145d40001d010305400807281540d032b00f49821031001003080b60a044606808468808100d076001300240ca124812840441c0c0282c0b80088100d10800800c003030b2943d10001c401404128074800c0800c2c01150b5201d04c200b00d5242c28002c4000c1e18040004000d1130070030500700440f00050740d000c01c035005007584c1030b0f5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 113078390 1250 113077140 113077169
    0x1407021203040f080d0504060b0f01050705070515041505070b070915080405010e25090b1302070807080703030c11121b010617030d0c0c0b04150b04020c010c180e01 72
    0x2604c044180710b0034400c85044c5003030006010a0014a5210801c0340340f00321545508242400019a00ca0247c40c00241190700400010045420b0103600301034600981000e807450545c440182c00014682c80c60758900160b408103801c000c01241c034115640055813801c008c00a1894603550300500c0302041d113400708000400010504014003508100d03010340ca2030003a102c061088200038603071601110424080d401c0b0083c000104000144101c03020503001600c000328050248508201130351003a101103030601800c00c80100860b2950b405088000e210380d4010507000d1032164020242d51402441440c240c10411004880421802c12038803410b00009400300070240694000340185480e9010800185d10105000a07000001c00240301764001e07580100100c0c20300901c01c07221a0744000d0b0003800440114081808200d000d207540c08044103100012a8114903003000c28180d0300882c2c41c1c00e10710b80d151504442540d801c4040c0100080d18004084207407458041e102108510600c80c020a100b0b011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 113079640 1250 113078390 113078393
    0x7020a050f131a01021e030328020304060203060111011104050409060609050103030e0114090a0b0f0c01091113110706020c1603080d0c0302090a1a07060f1407021203040f 75
    0x10201c1e88a0a100100c0400000030500f80e800c1e2100a4040380324014094040020302c010105510070706101e044900441c01c0d5619501c502550081107100f40921144080380e8142007035050005520403031240b40c0150310390034002c0004d0f1502e8142c0e1103056080c1d0400600d07242c02c41403001581e044450880d00850210020b060810040c40c064004a500314146030001c403e0680141300d4070680c0c0703001c2c1c0c1d03614501301400018285c00e00503d0400c030f6201c8011341040106411800183c005a94a4520300e072401c006c61901908640682d4000c0b1910316402c03010801c2031038400c48950a071030010b0814003454106151081b828410301d00300400302ca6022444900010b002c00402c96044059864481c481c1d449042950787c81d00000f42c0b04480034180442c0e1234109109009580316000090a0340a00742c1c1402d0400035140e00c01c50071000313520020701002c804210140103070350340d40e980c03542c1c00a00c40791000030032092075400400c0306041d0741c00301407641c507610a5001200c1d03110390048003c00d00e54040307 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 113080890 1250 113079640 113079649
    0x720060d050115020606180106050d1e0603030201060503031c240b0c01230414010f02071104050105040207021503060607080f0307021b01050f03060d080a090f0b07020a050f 76
    0x150340d44021064580000458880110070341282c0c10303070081e02140c0e0b1641e220004c111200440c8150103080c00c50080c01004054060400340c00b0104202001041100ea41d180c0c92549010b5402908075043d211481002855020710640c006464150080c5191200e100c030301900c43c1340249041d4034240c0d964541c0409051046544030011801d501c20200019a2502900320340d80098002865035403a19004e46012a03440440001c001e88107558400c41e0755550700c1d1172658541c0414951083d54903850114640c071580c0c0f0040c241940b1a001410044401c0b000348070481e6016040580540d104001c001c0145e519250100300035100900856966558900443c10502541038014840311001c5505c0031442d150744042c0d07200e02e400750308440c0403003011480c0381100030686151034007041d030400c02c8918050391031008641c8544d01500d80000283c2c2643c80003c5544020781440001d032250406110440350718000000030a410900a41000c1c115000603032240c0c0c052003004d20440d15500c400034640c0b80c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 113082140 1250 113080890 113080897
    0x9080102270d020a0f0306050901060e01030b04032d090806060603040807140a03030209090a050c0d090f05030d0c1b03120b0d0c090f06170714010215090c0a0506072006 74
    0xf40070b40340c0245a991041c4c0340b00c00f00fa4034001101c1040c1002e0001d003518905108040494030000c0c1200d03416445c640310164040b902500c00c0d020490102d1450346410600500071615440c402c224a0003221080c20081400817070381c1000c403070390300081b0038494155180000c0d07a42181d003000255540e0426403802c80e80d440c01280e5401464094a18064241a0564050300c0c0e072500540e484c40c856500ca0504104a45d0211620700719410140409840d043c015449002d4071031042c25032000d42000d6440e0140f030b6804c0f41d581c0114940c2c8500c4c1484c0f070380e03610100c00c018042e5040350702c408400030b580e0060b2040c144d46203141405541d445803445c503070382d0f002480b02c079803504015803101c280c0e101c0c6404000740503020b00c50041241080000540409011540d456006404000e080f4860401000c0341884442d041c1c46411440313858020517003807001040c02405900094001c2c522403d1807002d020707111003140e000f24800c460901a4402040850f0f003070400800703400d10881c01441c1130303400080c658003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 113083390 1250 113082140 113082143
    0x31202030408070906090b0d0507271d190308062202070609060509030915030a02120c03091e0d080c130e060307090209060a0c0f0b0a05060109080102270d 68
    0xc80c1802c00aa040130761742c000e40a0720205602440703a41078507024420784458000005041c0c0d400380d0f8003000030f4101c24680300000d04040004105c11009171160310300351200c2602a040c201450341180c00d25101c2041000d44138000ca800008191165440142c4200d0004101501407001c0d40702c104400ca00c0380b0107656020b20031400c1192250040d0610034010b1119000c101c03031061030400810000b040010594400c148000c0042c503004d104070390340c41d442d40c2000d0094403510b6028800070381c9281700242d9051007551194511922450b1414100e403500c900c103455514124014440355440b80404130307110071307000e0150070904446c3e00c5000035100e0511a14000003020f4185140c046100c0841c2c400882c0120002c401300e6a42da51070741200d0741207108800f00554410b0b002c01502e4040f070b015010304160381340100c0c511101000b6039141d070f11500230100c580403070483d44c505c1000260f6801c00503080203019410021800d00700701c5c2e01c2021080a80c1031040d0003a060700300e108086c0c0d40c0d80024192949 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 113084640 1250 113083390 113083393
    0xf030b150f010c120318050a2d170d0c050d0b220c0c02030f0a0614090c01080915040b01091b05030114030a0206040b1b030a0e0f0d050d0815030610031202030408 71
    0x943c0d0b0347c2480c40e202e0640039002c55584800b44110100d001d41e1100c000180804000480180c800a907550108020b510512185c010741c24070480703005001512071080380321810703181d050755000c41e00d18420031a02d074103200074411280d440600e440d00c0c1c00c4581201c464026500005800c00c0c40300025174100503880350007903141c46550344100c1814800300f07541e000944150790a100200d078600c0203400e00300003242c0c1702841d6130084c540f14510b58071400320a80c1018100040c2c03204a004166400b00a2100f20f800b500c2c01280d00004014041942c07252651144850809040c0c800d2403070801083d520040c40307900c90442c001170b030a5030769a50a100c001d00c00703030707000b45019960340d55031801413180d81090100c01a800900076081e00c40300c0c0c0110480f00982000d41c0c6545a80d18800e08014580c1a40071207103400c000c0c203100e030b440001c0d810490b400d1440180e4989004611f000fa020541c00c0100032103d40c025000f140c140821a202d850540090765480b1001911904c0f0480040346075004075806407040303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 113085890 1250 113084640 113084681
    0x5060a1a1e010f030509030306190b0a031b08270f010f0902030c01080103150c09090906090203100212130204020c030a08060f09190b0102070f030b150f010c1203 71
    0x1441c10203040d6210351500b030b260740c0c00c4031003a42010340480e070302294040340a400400c00101e2070b140400e240d00c08421803042c21a111a281e541c60b484a410101502c03000c40c4d0380d40b0070880806002003218800c20707141c0c9044581d6107480d42d5007580148416012180340700703000d02d03454070000d010b11800d43c4000100c8002c010310716019440c1005402141d02c26402409201c0e800c1a40754030a26007103060740c2d0081e074050600c0c6d940300f607201c0092000c031803100d04204001c400030030914030501403292a1805100e003c40c0d543c00c9401014109000c40c0c0104c401244104540071120840c82c4405900864009049040d0712103800440c000e032080042d00001404000b625100f055003140c0d045020729030965881440e146424107004d01d1080c16181111050b40b408841140c0342d9140d00018520300c010303c107032095243e680c1034000e843c94450308201c5055a1400401c624002414030083d0900d204584003220191882c0010344040442c400140c4080407151090003c0c5010b83c20010000d280304041c0034a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 113087140 1250 113085890 113085919
    0x20a02040b2403250807050d110408010e06070504051003050a0b1203030a0509010b010503060d1a01090b130b0109120c0305060709080d02060103030f0c0c03051e070f0305060a1a 78
    0x40c680d03c11604a40c4860304004a46542c0208115600c080452a1140c1e0400c3d100d195003a100f580080d45460156521062106402d06425028000030302c64a8000b0580f81c0414140300e041400042c50743c8200801440100102e0703587c050407020085007404d00089070f071500079190003d004044a8a0b401c101c0012115440420000085100741481d007000c010544440b0ba038207003a2215500c80700e000690910120302507140003400b0380c521034403d01c0301000040d519044084c610800740d100c10110355030703400000c4413400e241403003220385202a0b0081005241140c00604000e03114050004425981d000410821840c0d1600300c01441d0410210341941c074180f6001444043c1902030328640740102d0f01081400d80c00010b650381600d1f8540c680e061400c070718034030445010700d64200c00d6480b0b8140480010104500340109000c9100c2d180904e1000110080010300d481d1441c2c0c090042276041c1030b4100080380b404910282c2290404201140100358881c099049002001c4175680c230160b640d0036541d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 113088390 1250 113087140 113087209
    0x11030c070b04060908030405060405091801050408040f06090503070603021c02040311040b06031009020d092a0807030b010608060d02040f090215090114030603070e0c0405031606020a02040b 83
    0x41203d405540d2034010780e403120358642d281e004a108080c0c01c42024130041c0810b280c800c6860382d128018901b5500c2d051003001c041402d4800c1900c00707aa01c260002818801810581000d102901c110304141541d10b02e881d001c01d64903c02403144008050b40810124000c171300c90602101070301c0d030b400c2c029511181c4900300200350030f14240c03480784502d282000300e0815041c80001c4d00d11440d140810032480781e02d8004d980740a54440892242d800340e682c041000010130b04208040c0d410300110309040106898030840c40101c02c0c50b0002d00d0b1a500503503041001400540c8018103585080c9000c01083c2c0300c19012450352500100c0c0254018245680300300446030a078006039446008880c0784901c1c1c10b002c9000502c43c03180320462070000b0320400c02c510482d0f42c032400443d0414000381c1200c0304cc554038501c0403010401030301c100d1111040040d042001d441c0400a5591203a00c060311f40e481d142c5042d0010f5034400130440000d003d982c4034102210a60740d254113484010103a01d1062180a48000000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 113089640 1250 113088390 113088397
    0x30807050d021005040f0f0302030d0e0309040b0301090b0a0c090f0e07020601050604080a0f0c0302040e0303010e07020102160213112d0405030d0804060905030403060e0d020f060711030c070b 84
    0x41c001803044620701c0c1a191028051385020300d401203a803d02841c61038440c0061022810802e409600c010000b80ea00700d00c651280c400e40895a0020315210600c26040205481036084e14a210742c0c1820301110200b40d01071116038100904c000d00007650b00310342e00300780c2d03c4405944c000110b81140040000710000760000451194000364243d504a07070301c600401c080345c01240512081d0350700c420f401d40c0000b9100244840c3d03080c01171081d41109a583c0d80090160b840c0b054040075103402c0400100700d0815907a52844d04460107000075800c0c038000c102010f42e0f9401e0840060f00c03420000440780030049007039002c00061214481d005a864030100007043c0064580320030810b5480b499007808081000071015642904c8004001d4200306c42144011141c15402a0040c0e5051f90b48200020001e201080100011446400041103124180c80b0850500a6400200055412000309a2549500400c820764080a00c3c03d140c420340e103440041034554090704040b042140304142001c00e9203004007014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 113090890 1250 113089640 113089663
    0x9080309010e0703200310060807030209070914090604150806160323180609060709080606010206040b090114130204051006050328090b04060b030714130603080705 72
    0x28002ea44550507803035542c0b08140303c081e2000da059640013940c180700710080181410028100d0703000b58101440d4004031807599024808035032000c5401c0013107051151030107512540c0307030411040c0c8a14101c548510192070740425485103814000040c1c0c146c0d00c9034403100c012504401601c0c4804c0d110110281d0b1600e041da03024000c941308090000145129005403040c44075010180006044218a0796501010240c030103590440e0081840c0c80040040000b144548040c0d00103103402d0074103050261000700c8542001c100703500b122003040402d0b6000128150425480884070100e0303030319004a51b004254202011038140d04800600c001c0003101204510018000c070703010820b41d2192140078810100604c207031400b1400900c0000c503151524210003090401c403500c0050b541001840c24412038040c0201200d641c001c400601040c040188503104000f041940188411401c0c01c4a00321001c840c0380405209003403130810b903800c0042d40d40000b00115032112501d0380b030f165a4a09203460701e03440e910 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 113092140 1250 113090890 113090893
    0x80406090b090a150209060909070c12080604050a0b0102190201120207061a010c02090c0f1e0d06080105010513090213060b070b1003030f0f112d0c010503061e0409080309 75
    0x610a1380410b00b0310856124040c01403280780390581c0c41c014011310007001041d06003844142e03003d0301d021a41402030380010040341da5521000e4076101d0200000c88101914900480d0b1415002c8015640c002920707102a0503915110085444144012a1b10b50004101554064004600441000000c0c1c000e18545950a208500122940001121445040480658040045008a1150f0303485000030310840c40e582c00e0861820b510300719445540c4c4015001210f03181000501080d86991074400c03040030701501c00090000e5450f00d0005501d0301044000c140714141c0d01d442c070000315951051380c0d0180c66200726083c0000340c2d03607580400882d00990400d440c100403400004410444407503000d01038a81c50703181c2cbc1180c0382035a00b003210b0010a5408050a00030740c0c0b800720100d001c0821448102004460841504070a844151903aa00001c04d1402e119881000d940390326a03044000ea980c001c0050780e00440c1e681c5d014441d101103c1452070465006403400800005205220004510940c041c90 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 113093390 1250 113092140 113092163
    0xb190f0f0905091c050d15030209100312110a141f0e030403080903160f0602010f02031302010f1209150501080a0210080601020c030f0f01110c070303080406090b090a 73
    0x950007019682c1c11a044000c0d50008448841c00f080075a600d10400300041c0b50242c11b00e0000402d61080318083da4090303100780c950b54403c00c2103142ca041103542c0808004400249c07140b460790b0780207813000101c9849060221011114611600402c01c0b03044e9075400501071204090710654592710340c604448100480c0c040726540720510b007600c4c09a26894041400150b141520303549824401e5000420002da0501840d002000c1c07240a50b5050030282c9140d00460107201e1900501a084a590b802981e404500510422002c0210300c44d402c02059028201a21050307422002200c3c0b8003109042c0d541d88600d4001c5182c1401880500704800c40440d5030208001c1e40c9407052a0350320092450020342c000c43c410440b2108078415110305801420600403181f100800d000041c0c200300850100c030403a80d2200080c00c881d10424003c51000c515000000c9141c6680000301c162a403041d404050300340050f000116040281591000740b6441e00a0020318460410000c0c2e180c40d4003100b04243c3d00d024811 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 113094640 1250 113093390 113093399
    0x190602040e0c0a23040504050406050601020606100c020f041104080a051005040203031804110a0201090c09050402010507121404090b0a0e06010903021c0f050303180304180b190f0f 79
    0xc02180e000401c00c1e142c242c0c002e40591801c81009165403100001c4c054203000000c2c094455002d42401944503940106161404c20002032030550010900c03031143c200203116000301c0b504010001d0300e05070180e03800c401f107041e808041000380080d07800062450071700145c000b82c2080301040070000180300d00e0640300302c07040c0c02003d101a503205940103580364000300f0a030155541400c5440340b241c00701400c0400c1c03000d00c1c0c550000307094102101c0c24000d80d442d4040c00c020856288180d0000e0b00381307804104800d007030540000b0710724018008c2c0140090100c4801c6a10180600c519440d0320194a203196529501d80c00d442010700302c144000750160420340da0102c2d44021b400c69034740c415801a5694101c0a155400b00140074441d0079054400e141400d02c0711000c100c0c9020700f0402d10f4016001075a8a04100030a40701242d414070945025420900080c01942c844907040100500001000b003202ca90b5040042c0041180c0b00b020441a4544040094080301d00700f000c1049800350001ea40c1031560302c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 113095890 1250 113094640 113094661
    0x4050a11030111190309081306030609090b0105060a051303080903010c1e050f0409020414090c1207030902010215070207080709110717040f0902030f010b07051509190602040e 77
    0x400e10700c01d80c3c503038041c00851074040c0c00c000b25101620085c9030100d214000c0d46c03549050b650041000034a80c16440c04180a41505401403038001d00140c001000104548e8a908100c80e1040c010548524400a06040300c64411805d41d40c0a24101c06d800d5622562813070104901e5020120041c00f0b5408c00c1c0d1500b2a0501460200c20791200a00881003903030004c1e070044076568003176500c2048090b0b040c000404d02d20080e01c00f03040545103c407000030784200316204000c000311000b09546042142084a500c14841d0819002d8000300076040220b00711800384010703403c0c8110fa24500c00e007802240e04101c00d150b40054581e0807505648256641552505004001e90313030044481d10304440c0c100214000203801075452401c406c0c0019000b4240390f12000d1801c45100240c0c40001c0049d004400c3c03011440b1141c0b001401003a0380030b20a464007103581d84650700e800d641c0c0b054816030420f8200040c4404410701c5076031a0358032000f8035105d40d80880e16201000b9009401a2030000d4031881c0000d400d00307803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 113097140 1250 113095890 113095901
    0x6020319020604050a0b06190f0915061205100e04030206060108060102010605061204051e0d030c0503010501210209030d200606030303010306050901090f150b0f06040506030406110304050a110301 86
    0x130450042c09400729251079440c0c1c805005004d443e048002da614038418040d00200d1680507180c1c510404c0010340c5800704050940341c60703483c0850200e589980400c0010381000e4010490301f58002c000c00c079540d4a0b000c416240d039a980c00701802001520030081010342c04036270144210f500742c0b03c0300602c1d101c410049003210b01d24051281c02c10070400a420f4000c8400c0c41c06039002d0b2161080781ca0a0104844521801e801190120002d6000c3c5d04480003954160180525500e0240b920904646c9404002050a00e0705030141360008601c26a51b41c00c65040c0c0c04031500c0240c06800ca0307444440904008100e81c40e400f0710003080307218030a40c01002d0100842c609014501c024000c2d41141d08540342e00d401840040c1103004c0c55903a90005400050881c29030090803401514803e041000815200c401d9035002c0511620550544440c0407681c0c1e196000d0f2016039000707661640d00c99590345014001069117071600f00e5030b64404800c000402000052010031144210840185079040c042414240c42 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 113098390 1250 113097140 113097143
    0xa0204061e0f0b0d0203090703050d091d0609010303030e0c09010618050402040e0f25051801020a0510020d06030f050703050d03050402060d0b010509040540020919050106020319020604 81
    0x80811900d1520004d0750080e68008600da001c2c5c0d51300d15030300e5403118508200000d2010108001c45001c00c1025841d0301c48400f1201980c0754152a0302d002c2d4000b5155100c14000203084c9076560030480b000d0101004060002c40010304102429611031a0181540402051803003180103040c03408aa18240340c020f850840e007102d19120f00c2500c6004d4000701d41140107060404560200d113803110040400c0e10a00e000d80c0c516252513070740c0e45680349003046410325441514195409450713401c0000e0300000e01800c0c403a0305240c006803904124000e56000e0030165101805403514191544240075020a6240407640310320121880d081b5402002e606882d0200c801952010040c00100714010443d0400c01c00c2941c140b5080b49408130541c001401c0300c0c0103032007070a00e00f0000c2d20141d4a00b01c0c4400025007542c0b10344010741c000c2c610b4240c4066002c4d00041c00038055664140492405514000010b00d500c1100300140419038407031900940d250400041c15104581d20668580b00c5400855500d0180303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 113099640 1250 113098390 113098409
    0x9030a020405090a0c060c0c06030c0c120e0a0f08060f0c030103020d0201030e1006060f110a06150503071518080a0609022b170f04170a0204061e0f 65
    0x800640d000c1200070400201100000d000b10001e180020741c111300108081c0c2003540324075004010368142a602c0340c0301504040b050600d01515008190381260403006c09551003140e0801c4410480c0040700c0c4101c0301c0701500d4100541c0007000c0351070b280c100d65000503036002a08950b01c40d80d4024424846641c00c0d40c00540c2500200018805820001143d00d4218018107022442680e03000100e072a010000c19410303803035551023000f031180e25400b00d150b042900091030304054074114280e059407030b611100740040003150b40d0ba102d80b00c2c124000125400500005065440c2c1c0e07507591505076600e1211010f400b00007903039550020320441441e4014001c1e1088040205410b0103103584100080c42d0540050781d0085c0003450860352601510b1120a01d4080950303500c5541e03e8030300d401c800b10800342c04a4000614188080000f00d129002590203c50428040d1070511000e0700d4501e05090b1030141c065007090510754041500040c23001019502d03400c0140d03000d111030741e800500300010301c9406980c111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 113100890 1250 113099640 113099653
    0x7020303011a090a0e1509070809100f11070b040c05030604030905010c0f02060f070302010f05060f0918031201151706011404090615020f01020c060f090109140709110903 75
    0x1007400030b00a0245004080c0000e0000c6880c1c2004c44440007080300d0414950302d4981003508070f07051044250350000340710705121484e41806550345440d01000c0c000e41e0440303507540e0340070f0b03100e150241c002003104c458580019584000c107040117000000f04450503100120040e200023014180029020310440e016680c0550040c10300c0c0c01103c1213200c0c40381c15502540c46a41c141c0143e51040010107a00108102140e500d480d50315000e82550340d8002c2c02c0030b4103440d000c20410342c2c0d10355210121a01c5011216814203a80c1c0c1413000c074480822008c200010f11012980c0b8201e110b0207403140f4140c901705440b28000040c0c1d40c50844010310380340c50044090405074040b8840c0c0d4000d0f41c1e504001151000c401c0d05054482d804801241c0c01d5030f0000c030032020912002081d5540510412745100d06000c001e500d0b0002800c0301c144d982202400076041c00500780300047c8030303540c01e40c4041007155216098010240401c0d0010365683d040340a00344186252200c1c0000c040c92090403039000f000050050080c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 113102140 1250 113100890 113100929
    0x5062b060f0b100302180a030804050d0201050d0903080a0506030d141617040e0717011511061003030207050a180207030201140702010203010f0902030108150c1303030806090702030301 81
    0x940204000c601a181d101c22803048140e8602c0f02010490072640c0d001a12094031801c10a49004d0848105015050f4081c041c000f041848045130107980090710030280d540c400e4401290144101881da5080d40c0ca02504002010b602101c01405912012070910060f20f851040644922400c2007031004200e842094040c04040c1c20068031481804450b4040c89440c0da464000d007200a030000c07d2160800020148080c090251104e41c0020311803420386000070407800128082e207018060400041e2034000d2448501340700c0c100701103850b0400c03010340303c5a04115407011100b0f031641c001107015000e40d41c4041070605108021a08445404003120401d101c80c2e003841c8021361158806408554a580700c24544004100d920307401450180c1c0016607941c54140302d9969180150810180d1500400c0108201c0100054084401d04070280c5058507882e10034003100580304004102c286c010b200140001816007180c00c840c440c42041d01d08244039641d0a1040f81c072071000340a44291009071aa50720f5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 113103390 1250 113102140 113102153
    0x507060c06051005030312100b0d0504150504051e030d020d0b10050c150c0c0a05060703050702030901090302011d040f020901020c060406090b070302100f02030412080423120301030605062b 83
    0xa8000a0204d01c1c1d1681503203920b01d2030410303404160501c2b01c40e41c81e0414001004403084c2c0320001540c02800412083c02e1035962245c503100d0001e514105142084055880c1c04410f108075280d0350001001155944081d5420030040c1c510b040d603440c401c80c0301c914401d400c00e004004950008010301d020789066002d1014801c4100f40c040c080480f600c0091010401c1c4040030003101c5c0c0c800780120014101071505100040903a48002c1c02c0c00219081030000c1f8049036003000c04101501d50900701032034150090040d5001c8941c0344106154480e0404400c02d901582c80d5004054400080c1d09950080801900f4402503118030720400c80001d91800d820842501d1100c060f194042c480d20540e8400d24181014800396850414050700242c1d000081c4020400d02c03420108111400d81054038039031409031200d100d030f1800e201000354960030100144242c1c420920078408825201130503103449503143e0424000a2500300c0304940940c1d4408503602c1c1c802c0c0d440d010480310500782420400560200c2e510070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 113104640 1250 113103390 113103427
    0x50415030e0a06020c060106050406050301140102010e0109030816080c07020f1c0b0118050f1605040902180429061602220501060f090302040c09030507060c060510050303 75
    0x102016907030128a19911001d02c040c65605005403030160703c0b0f002e05030426042c00b6040c0c0c00b01c0e050110400041020340c3e0460240c82c1115564280050036403800300c0185d01404034004150300d01c0d480d0641c01030806800c146154002e4034003401c101c1c900f1b031801c502620381040a0300e00c031017008003c0c0000001450410043c03506040f000d003e1007a034000644001c0c0301090b031484122a450407490050003242c1030070803a56032010720520184a542404e1500a03c02e060140ca034000030100d0924540c000d030f020302c003164000d1800030342c11985e5511443c03031200315103045c08030644120b09080024100f5120246042c00f521849107408440e02201010800341340d0050001542014000c2105d0025980d03000000d01c80c030802c0e245204204c100709034080e0440380160840d00030710402108001120b58400e0280341920740c1a280060508a1010300341e80e8500d0591000389540320700d420104015a001190703900783d0f4466401884a5120710344045d101c2d400d01e02425815601c01d04c040402c1501e8090035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 113105890 1250 113104640 113104679
    0x30c12020102150a02031506070201050304060e21130611070905060f040c08070305220201120f0507050a090506040303050901080a060f0b07020a05030a030507030819020406030b03100c0504 83
    0x101c0f80070144086800104a404030340032a0550b5000c0100702642030f002c00c0542c0e209404a4006103400161b034000390050002401c080c20259881c42031000b2240104000c2191050804a08680c0a8109100101540b0801003001002020b03203002584030b006001c2c00c00c58411803405040c0c001d04121029008040081109521088101004d503250300c4900c900f045001c400d541da000b562800980250590304080c02d06000d0b8041c4212000c1e004121225850605a091802c110448000c00da0040a428000700c10200e1a14080034403642035088030041000d040c0c0f41c0c451043c019591410462940100e10001c0c0210314200003140b4558801c41c10b5580c4450003c40019103183c03109218008140e10380c00060b510b01d000a080340551030310f91254801010100c1c01000e44001649c0c000341280a8280c004086c03100c80310104500d104403107810305409004071011912260340c0d0300010041c000f09a80750303003e07018030203038192441c50b58000c55410f4181c90303c4043c40c00b80340101549648411080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 113107140 1250 113105890 113105893
    0x71a040504020406031b080408090f060c010c0207051c120806040e0703060c111c0503040302030408190b070201050601090311040209060f0702030705031f0504060b060a030e0c0109030c12020102 85
    0x80361a581e14809400640880d5800088034207480321951a01e401c001048800c0c04102800c200002c2d40a01c1245c4c0342d01c40c151054084420344c2c6000c10414080e0303905280b0254200b00211301074960025400302260821201d02d001812a41d103038480807104040f024254003100c3d070801100f14000c40c80316820500241000030000e3f0968696820180315400c200da549031100e00030031700150302010401946068102420250b000f07841c1c0d4a08007003030300b0044018828040005414140244140c078010004030007a503107190030211054840381203076101220240f901001140c6481c1c41441082c0c811034040c2c54a140203802d5482d81c80744043d041e48200c4d88a60200030241c06900c4901c0079110403404601a107032103454620415003032115a030086402239119231800071b051b2040b0b020f1a001100b4402e40020b035171f11142811000350441044580d009900040c10038074542d410352110b00424403020507600c08040100044030700580e1840060881b5898080034081c40c1d030850848402c4620500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 113108390 1250 113107140 113107147
    0xb010507080a03051902040803040e06120a050304060f050315090402190608090d0828150620061519050904080a08010f03020d1b05060309030403060b1002071a 70
    0x641d0128554480c041d0b1000003610359091002054549003030044030a0800f109500340390400001944e40c1c000e503c00e414031075410f040458510307168500320302c000c0d4500f9003d849c0c440c012801d107a59a680940300708000214000c0b091340d4014460300a4034010316080d25a8040044210200030446070041e1090781c3c40100c040b40320604d00c4400d52100010655606c0f404110700d080000b607400c120301142d1150900450070100120540c080c1d00c0100c20320388445135110b81d8241008100001c0c0481c80581500c20224000400c8603600403a400c1c1044118510140510b19111566512420182c884141021f4800110740c85840d1580596041ca4200c000f20045588c2c2d85c800200b91b66001c0c0c80a607426100014211082d41d800f501e05c41c007424041c236000ea003261450340816a0646002800b620341701460f84081041804041303007100902c0018021512070400b07511a940302d41c403500c0201c41603480c00e4030a00c610301740300b4495034420b0481d401805000b03141042031039601c500d5080b5158048000c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 113109640 1250 113108390 113108393
    0x2060d0e0f0f0d08010b070c17030915070605090d08070f0507020a030b060a0603020f04030237081501050f062808070e030f0c04020d090b04050105041112100b010507 73
    0x80051141010701a8010000c001c0008001380180006800c4400c031054204003140200307040c04e032694116441120411100030100700da4070300754052a4500c650203050790880055082c500400380000da406080c00300083c0d21601d1110381e983c107012030700784089100c01d0006a0407601603100494484141d00300540f5183e03080e030005002d00215041107440e4500b0310103102c481c0c02e00020300b0000c0c040c1818110715069008061003458019444021321031019110000074600c1c071040562250b440044195400c1101043c0c5580421904d0191819038421901401c0b80400d0046000381210001740c100e07150002c0000078820710f5030001c0f8601180215425000c8603c404424104048136101d5990090381d041010300240300002c00c0e0340c1c07207209a0000d01c6401182d500800c407100502000c940050390390107ca80c0301d601420210380d000d00107050710300c200000d014064120078402e40c80b0302944080b03007500404015800400d00320404c8070340d20010710891248610f9004040d22507050404c103003400040e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 113110890 1250 113109640 113109643
    0x50a05070e0f090a1203090506191505010831080c010b0108010312030e0f070f03051c2001060b0a021608030c03120a02070206040e0709090902060d0e0f 67
    0x111412181940300660420041c058100788a07000074550840d10300504050f40c00d16922803046401800802078820030404260007540315583c141d0744441624482c3c0f030040d0140d2280e0803415001e8484608009016a14210242401054800503100c4600b15100c5880e00100745a003000c1e010100d041a006402549000c4113000401d14890b005165076030011380304170342c2543e00c800c1280781407009150043c0002642c600000d04400d0716440d0000d03805010019031403800050700c0010300c2c00c1c040c80074040348036101c062203e8113581c000d00c1100c5251a101e0b19400623107214100b813000041400f0103414410140402c80d001c010301400c000f20740715854807000840b60344840e03c42405a80010b5803010052400f0b5800401400060302850510980c11309498807442800d56800700c4519403c00600c00108560503140c6c00e82c2c000d0030841c1c5039503c606035203080c100141c6824010a0a02c130000070303a0b64250085840103079025180354140b9281420384400341c460713841a00903074041d0055a9056010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 113112140 1250 113110890 113110903
    0x50610022a450705040504091a0c0702090f070203091c0606060522140f04060b12040506091614010509090c040501031103090303011a130b0a031b020a020f060705 71
    0x118403024070b060600340c1559101d52100c041820081e40c030030040da480d040401e9034100c400c1602c0220710148549081ea9840d558002c940d209031105009002201c0070f1500a03000d064805c1d10502083c0c0c441c609003440003d42200c4050050303004200303500050900310110076003409007a40c0c1030740124440d620300042e200150410000160045100d03507100c400081e02840070000e61145c6545203007402482111190348000042c000d9130f9208100555032656806440105a8040a20380360401016071006d031000580d800d54040c8a50781c081a0b0070070300450906980c4c48000d0b50809150700d80441c02d50320b40b071042202410702000740140c0c9026250548440d00c600034003410346907910705060014045404070051140140014010401c2c104030003c00c49041d01c911207031494030980082900059032003612104447e481d0346060010b0b9120500d40079110321581c44d00c0c24003480714001c0700300402e80488661000140e010b44007074005410103041002e210400038081d20300d402c890792a140d24005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 113113390 1250 113112140 113112199
    0xa0501020301062105070e1216030b04020111150f0c0c03030403200c0d060e0c0303070b01030b250e0310060e041707020303030109050a0f060603050610022a 69
    0x10307403408495100d05811390400050301d441034010032030350078800c50041c40321a501c2030041c003640c07400b04d100c020f08000304000600d000d4030f500703030020382a107a1801c4c00e07520310192000c82c01315540c107601460121001c2805109003050348100f409030303603460091582a0700b015210060418041128000101c0d061000394410345c06a01e804514a8130b550380722000c2d14403814200c2c59504071a00c4000709589940c0440605a0010303008121103200300309080c00c050b03600300c07100c0d854800000c2a004002d01003041c1c0c4c1c1200e0245040c110307144d5a0050301c0d040c0c820700e50305820750303000d690f0b002012450040564210301d6401a044401040d0400c0e20350048503d160811020100c4100030441045844006030b45903e810100003420b040c03055022a80c2ca00060013122403003500c0f10005001d8440d0303944801c09440c00c0001c2030280aa60390302c00313001000c2c01d40d00c55003d602c0394440c1c910594000212280c5054943c2c55904a0741a41084074404c4601e40720183d030b03c10821601150b030000c1d210200333403290 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 113114640 1250 113113390 113113397
    0x605040501030f0c240509040605031f050105090105060306060c160b04030c080a02101202091c020103050a0b0a0501030c0507020907020319030b0102070612091b140904020d0210020a050102030106 86
    0xf00603424240c49580301d551080c010418040ca048081e81e043c1c501d035400e403289a040c040d840d1510040003c01610300364000f07581500c59a00082050300319109400c4c460703191741ca010402030b6220018484492024003c4517008081040400c00074100500204507c2c40743c88150b52540803040290640303d499070b80300e505c20801c0450280240302010803408028600b42d80201a1701c1843e0f030102d82c0707000341c0c0c600c01e405100303080e000140490031940483e0801c40004004200c511880200c02409040d048000c0e40068600800950301c41c40c40c0c4540e40c40c010340109601c161914000046001e0100e000a07101004014092400162585240540216125000b03107440e0503d88500304039980782584841c003094284049545140d0b004513110068816518003000c403000b804204202074128020010280481001540d0003407210000c0700041d00d01115916000001400801508820075107020b03521814070082c0200502e007120b800c0c000c0c01c420740181c40c80b9003115290300c0d00b260401d90044010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 113115890 1250 113114640 113114663
    0x90a060908030a0c02070509010e0720150106031e05100801090605010e1b03010e060604050d0b0601120b030c1002010e030c0a02030706050a0e040b011e0c140a080f0d060504050103 79
    0x560814000c1c15100300b007601c014901145821f0018610003410300c209042c1060714000306070000d00c1800040915025090030381d038404000e0201c0c136a2000316000000e8892071880010460340e00c2401062441c40d00809030b5111600d545003428004c25001d080138051035042500000c800201380250081e150007100c00280c00c0d8900443d00c4012180206080050001e03100301c1031610140405803810340f9005070403a08a5690640461017620840e00070603480b0f426101e8081c10061107001251240000380e0303d0007280000c0c01d030381e034058604c0d038081b1940c150003101d0205e1240c140480300322a0060644000b04092080070001783c15684861500c400540090420b02c0070b506017048424000c0907245001c0d881d10402070002080506c090001c94400c607100e02407001030f070788100e400c81d4885051007403046040c2d039a464040c110031010741e01181e046050103402842c03424003081034034803650000700e400c0c942429100e41ca007240e448040c00701d079031656a21020031a612584580f9001c2c0d440381c25910384 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 113117140 1250 113115890 113115901
    0xe10450e0405010c032d06030b012601020901020304060e131b0e061201031e020301020a03021e0708160318030b071707020c0105090d1407030201140f12090a06090803 73
    0x2034071254021344003490305006942408426045403aa080780d2180d4201801495243d030401c0900303001d03440600b01c0d54000b0004a101a0005030748100c100002005161074100061824240e000b803841042c00760300300b4032041100700c0c024200c400c0120001042c8451a9040c0c08628040701c1e01c000e545044140d4814035103a04582010304031140400445030942800040501100403050500000302841011005c4d07650095007040208141540140259104c0318180c00080081d000141d03115965140c3c0240088892810800c84212a8108880516003200080ba43d00c044200440403804c000d8009a0311404030080c0720058041c600c2440c442c1c405080612000f4041d50b4501a180f111500d10f10074806181c0d000207917655148400e00300551199121400105440d14850028002010600390070422203030100c1c24105481c402d0f00d4101c13030404204081d000c58054210002d00291040050b5014020400340d1244d00101d024101c1c0c00715015a5500c105403810701108075651407020040c400c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 113118390 1250 113117140 113117143
    0x110c07080c0310200f09030a1202070506040806181011090108221101050c01060801140702030304030203030a151d070801080a02060306040207020303190e10450e0405 73
    0x50024440024401413500000400441c458545142c002000004095401144840c280c0c0c403010001401d480340070600b0f00b041910030f540e500400c2d005005940000c07642c0e02d402c20030740e41a90218401041556603810390f02040242c02c41880165120708850316040e420305000740b45810800f070700c84a445c1e0b0780341000500004405000800001680f040f07a80f640302c4208040c0c0f1190740c001c2d44c83c2e0900800c00005036224880d904681499501b001c0b0046203801c0150001c0b04107a9010b05004055681c1183c200d071280019030b001001600700300041103640c003494000c69600d103020418103030110350300c8107811024401c4040c5100d81482c0c49042141341d58011000e03500600385400070340500701c3c1c0b039070000700b10744002480144500c0c2d010903510255102041641c0c8c03004075440c41c503d041000f5200c05040c07400d280625074440c0048400410400d4464904c080341884403541c1d185c818030000c4504111205807170f944001000601d80407241072021645140700a040314200025a81494103019 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 113119640 1250 113118390 113118403
    0x8071b03150b010309050a0308060a09060b070507060e0604030311070902030702060711010606020a03031a060c03040e1501080f1810061a090901030311010b03060c0d15030503030604110c07080c03 86
    0x1411300d0700c1c0003150008180080b40d4044281d030b2514001c411541e40714002001d01c042ca030406000180381c04d002140d01140c840c010310b0314501540841c0c500643d40d0808460902e001e2190300c0d001348080c44100002030280d071001c188501101c1c141c589032a00d8403800c3c41243c004541400040c1d0090302030040c010742012f0016128012100203014042c10203502075591f07a0790090050406958804998900c158180031000d500c90041c8a00e030b85031407081141e9500d070040d010340f480300c1200e580440c119046800c1c2c0c4446040040c5c44500f41980c940b80d0022440300000d00c140408242c80011211001041c00003202d014402c107070014840d81040065410f0f601e540c0710341b10540a00300099800d66480c20b011070304480d803510b0480c00d03411841078428003520713004503d9034041c41804244108452080041d14141a0000c0100403d6101c41000c94103041c0324400076107190400c03c00300d40303582855000502c101003440301c16403900e030300c00380403074907014459100a2468008007490101458144881c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 113120890 1250 113119640 113119661
    0x10030b0603060709151e020c0108130c03151806051b0309030d020903030f0f030612030a080c03070c0f0c0504050115080c070c090c0903020f1c08071b0315 68
    0x1d014034501200060440080f138001c40f24154245c40509076030724070410111844d85032040030030010b0340c1030607400b940d50350841c0492400304a036a0300080c85410150741c01c030055600000000030191039500c40c5000c1d03615050841c041d19880b02ca0000b80e4103a02d64041b004148a04000116403400c0152441144004481400101010014423118200c00001d0b03e0501594020040c0d0303500441c3c00003032551052502c032140410010034200e0504003940042d6220b0501030702c141c641c510b54080070f00e0302ca11584200101003111080402c2158442da006158014100d00707080700e03200756589a25402d19000d02040320300700d030760030b07800e01090030030f0700440d0300605011320200d1070008003035405000e62800514421120304003086c843c05001c50920084000c01103400700300710050354004d000b00041d0440c08141e01400345030280c40000e041c8001c4208407900355801300c4901075240d45c1c8031781160b400341105851402d880031880350340ca03828401141c021031007070b41d503400702094900701d181c1900c00300c1c1c91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 113122140 1250 113120890 113120893
    0x310032901140303040e1f08010b03210a081b0c0a1205190f0302070812060f03030c0307061a041409010c08010605160302070b0a02010212090118020919020310030b0603 74
    0x10b841103440010503503050b0741e1044d000070340076592082d0b0102803004500e07004c013620320321100004800074190710a038a440419401e5451b2079060a03100e00c20042c2c010451008114200070126100340705804c09900103158040da43c00c1880002401c0c0703a60f4103c1054100941c10189413441006012891308140c441c950802a00f0030f10404000304045011050220500c450011300c1e85e4414030a50440359004d600c40e81d40b42d256500346650b04483c201c200c1e502805403802d060140420319000060740c02c5c00c00280011032508405903103850240c00e0b00100a00b8401510520702419070750f501400380d482c00b006a07042c0f2180703440b40c00c007400c0d1502201c020003842403a5006009940c0d1180444581030341c80d00e802c2c440c1d0384151804910b8045994001c0b01240004140303007089031740c107400802407001004c08002d02c07070711800c1059080340d8600305c1c002402001c00b1954401420300d800d60036400129405448504032b90b02017200c0c243d074030403500c2424890681c0ba0904c104800c01d010150414420760 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 113123390 1250 113122140 113122169
    0xb01020c0a080715050c0d0908060a0608121809010b071502070201050d020306120106060e0109170309040b01020304030506040f0c1203020c060c01060314010c0206130305070201050310032901 84
    0x99400340c440305940200032601c104481c04d8641c1c103028404554100c6500c000712291000914002850310705e0601031581d003402088e012410500c0c0320b000703000a4800100241070300182c001c828000c2a403008403140f0b48481e0145052505a1350b1101c070038024480c4101c10b9a50302d2491600512111581c0506841e940c8107210490150341d00c507043d40c0c4a0740c2c1c6c1890059032383c2c4506c4000741940c40300c460130550720340c2002004182d441c0d10800c01c1c2d2500d4001c0c0c84103140b4030b03101c028070181c501d18a49010076a60040c840082a0f00e410f801c107072495001070050f0380c50b0a48940b03031a418075038111401d55603045035204035020002d00007034003002841048004201d5100c00e9070020b450b0300078254018031880700455a00191a400c0d84200c1c01940d224000c2544000101c140d90301030031032900664058010200040e01c590038800805d6103003070781070350354600c1c0041d41d0340151080c2c0c101405011080c80070440c04400507040c2c440441242101e004404c02c0c0d0741e0303000c11005503ca016080f103c040319a00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 113124640 1250 113123390 113123399
    0x102060c040803090f01030609050406060801050601020708060f06060f16050c0111060a09020301061211040506091009020c1002040803090306093d0c0f0207080303040f14010912030b01020c0a 84
    0x4401c1e0b50005800711181782400c1c040c2c030300481c041c0409400940440b03241105100c01c011995004c4421144030000a20507940c42c0c40069840f0840c078401c1129641008000550500f000d418056002000406050411900d850072801540260047c40c0c41e1640800c004010b002c1c04103c01ca56281d403d00e020310452a85908181c0c894138045d164211303864882c1000310442d43c081d0480005049e00602145035000142022114042c032000643d0080d4504030224200d800c0100b4070500c1020181c1e4a000182e180c210003800070342c058002c222060184003070303100300e00300e9a00041004280b500700458071424454105801c164015080c84881c1d48401d944039450030301558805500c20203491034201800b031440b08034003825008601a500580740403d1869016045021075500c02119401c8034501da0729101d03150b549110544004d44078035141c043c408001004844a001840425400032030813844a50301c0f40c00f00d04102c800b400c00300b500caa1024009507410000d624007282c0440f40c0d0980c00380742 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 113125890 1250 113124640 113124643
    0x80d151d1006080603010f05070203130905040201020705060f040e040c031401050108070603180c060503010e0708280b0d0c061103070f020f061c051008062e0b030a0501050102060c0408 81
    0x1c0744614000d20095400203200c0b41d07400c1d03004000c0c0321400c4106218500e0301110003901d90348456841404501142c20114aa0605106d0705101d00d6060700108421414074082000f03e0300480c2c21408007403010400031450040d00d1800c00c0c01184910b079400300190071840c00d010f420742040b42515050b850503004010305003002071203c045030003d00340000d60480d8003501c00c00701850b416000c0d14035910742d01c0018460b90b200000314100c401c040c00d100c1d010f894501c4220342c54407090fa20307904521116034161810513032981d2000940c2c10804800180e0240800c00300d140c10740640012b840192540d20100021600700300f40806100210f800f035072402c2e0310b81d41c40790201903150384003074002d440c079814809064848504440040d00f808000c1e81c04600c4004400018103c216070b140070040d40c4080004942a000440c036010382d8001030030070b82c00241e4000e48500c10302181802294441d103080c1c0010147d41e21401980103000e481c0307003c1015030414002924105001c0c0a407820290104020002c0000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 113127140 1250 113125890 113125921
    0x21305060a0201021b031908090a0b15120a03020f0114010b07050102040e0108030a0306050a0b0318030d0c050c0d0e0a06032406020318040b03030a0309080d151d 71
    0xc6611507111032041ea0304a00a01800c1d050a481d4001c00c08043c600307440010141441c030040e14510390508182000484000c1d0b003d40c0d203145268442a40f103800180007a0003103501c0030754060700450b0340b140304001801a44800004003030070b0708441a070708181a0b041c40810391301c46000b8001d000341c56800c3c0171441d810a0500c180101c0366004a1071004120081d01250000c1000c0e5610313007521f50311a0181500c80d4854412100440e150070360024080c240054003d0845103045122421940d8001109400c078170041043d0310750340010050000c2410151080c081e0a00c1c4c20741c1d4007521681c140000360300c0e00d140402c0d42da0500c9020000384400d5912112144107440c0103280c04036000d812681018030795586401c41d4000000c0d07081001c1fa55550020140518078249a0442041401c200030300048444000c13604c4d425800400410718418040e0b0072105034944105501450b0003500144002200c0c2c01c1c40350390100b040052420050400400002d4450301e80032609079429041c894003440f030758034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 113128390 1250 113127140 113127149
    0x9090a0504030905091012020a0509090609010606180b070c090c0c0c050f03060c0c010e06040f03030b0f03031e070609060203070207060503090a0b04080910030509010c02031c180f05010605040f0213 87
    0x8a001f81080c00c41d120b0741108002040c001c1c003101c0c190b041103180d0603140c07402111018200d620b801400180c651046003500178613031416451242907400c01070851621f910800040d10302420030b040000e81400e040c0300f03c001c4107100e035465150000c100d1402c0044a0315a0340070a00c41e0603000304160299a022800d99004604804410750398109030130401c5c054801c50019810324001c4c0c0e4104001e01260300d04000c8802e200e035408000448854040207125801e50b80c0700740c0c05a0040c0411400003000506403408200e1440c45541080c904d9a01d5405030344290301c0c100c034425004002d0000560f010401c940285c211420b00905610305002d51640d21100e4210182c00520900e0101c0c8c1480181c8080380c903400b202404009101002e4480680a818280d450142c150305e4001a003840910220682c1c9201501d0f01540c0c1000035050109806400d60343c081d6000c0911060403600051080c00b01080d030b280c0300d4400403607980d1405081008070b50560031500502d034010040320029018801c00d92042c4c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 113129496 1106 113128390 113128409
    0x602090901211506050301110a030c0903030804060906090803090601060207170616020321160809030a120b032d0d050406031109090a05040309050910 66
    0x8142545030740d42d055500c03605080000b1040d452000c103040d00380e20b000c0740b9562104006802c4420001c01a40070440c0011142503050f018000c01400601d5401e201d82803d10395200038003c071400038401042c089d40c031098a01000202c0e409142c0d1a90029159074403450300c048110340d136210038000e00c009846020700010744800b100f0078603d442c00d01103000c1c011f9902c07034846031141070043e10700400c1980410f000c00b02140c400c424400030842402d96010075181040e14101c601d00c0385001d001002c218240040040301031001003107a188421034544034802107900c2000e00010210407111a906001c0c24040707100154074900741040d2181c03070205c1e2565148000c2026036580300030711030351004a03900788000c11145000c2e500c404401c00b41030000364500302c01c8100180b83c1c0d02040780c032003c20540e200c00340418940c5c001c41000243c0000e0300c5d2410b40d41009d0040c480884480c5c8240c4280 = true := by decide +kernel

theorem cover : BRFrame.Cov 112949640 113129496 := by
  have h0 := BRFrame.cov_init 112949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 112949640 ≤ n) (h2 : n < 113129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
