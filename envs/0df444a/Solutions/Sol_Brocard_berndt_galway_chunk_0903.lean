-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0903
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:37:49.902904+00:00
-- url     : https://prove2.me/submissions/2313fb2f-ea08-451a-b7c3-0954085b0192

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 162230215 ≤ n < 162410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 162231465 1250 162230215 162230251
    0x328030b0a0501030e0f10021c1b0c050f061501020c04020f09040b220204060e060903060a11090621130f0b070302120406050f0a06030503251703010608 67
    0x40e82100720340141810983c0e203c5c019071382001e080020000b000341400c150b50103409540801c201075801454000d0940076203032041c8907141c8003449500c000c1d6902590509442c5680d801c112500003412005494501c03074001c0e1901900c2c3d082c030009000b01030700100c0d030413a240240c00281c2030290702e03510680310710310602528804440150448051a104690014002803000d000801484010740404904651030900078600f01d62580140195510307a140d4005202880c02002160b12940b4080c2e905501f001000c20320403846a000007540440408445050000d400c01294140d0091050202044082c0325140000d80448602d0b41c2c110207000b4071418800e0750354807612034180f0400402000d000412001608142c401d80c1035402c0c50501b06000c4009042a040c1140a420162081c100c40b115240100d010b1404520a08080360fa102016500385410304407103220340c1058132a96904003a00c244840c0008213101c0741c009003060f64640b050340760b50520900a110540041a0344603914141e180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 162232715 1250 162231465 162231469
    0x13230403090b091509010c050d080901060b1903050405010b03161502030c1515090a140c031005011103040b0f0c010b0103020906070204180c09060501080907030f080c0307050328030b 80
    0x5512140c003000c0748050381e030a01000121405840d8204c090234501580c1c2e00c0c01c1d030082d40310f0101030107009818000d12105403274840d030359000c5c402d80c048013813440500301e044801075000c3d80000b41d0013402003000041c050001c80c0881e040405400700f10000c01d00c0c400042c45034008101400c1c00c0c0701c000344000c500709108500c0031039840188403031800c0500070b09000602a00201080d5000318040a0301100650070800d0000b006040004e420001d0741c8940e400154102c03a260040c1c2e8800c0944a820703414283c80c00c1c1c0103413103198400718030300500c0c00200004161100118002c100e2510781500340c954078258090031900311024412543d04240c01000161190703031340c0308241c0b680d031901220000f940754441d44600b6100c2c05804401043c020380d845000074440341541c40b94003216020b0b295100203607501da581c10303101d0008d40070080c0700048404103c804075000c00041c100c0410320408403480c1c064562205403944d004103002e1141c20b00c049014101611024814440141c0c5904041c4003040c40000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 162233965 1250 162232715 162232729
    0xb120703050a030c050c061b1515040c091e0e0906010b1c0b040609022a0319050c101508010203070e0402030a0b0d060203010608010506070503070213230403090b09 72
    0x2002034104040300584c2014020b05002e00000d00c800204001d40d1500c1003100350100b48142000e035102c6004000059040c80481006144a1001d40d03000071000e05030b900400c001040c6c0805c081e070820008101c082860708211100e02da1100e4007002101405103441901c10050600074503941076600020010064150381134240c88501c100b61080d80d0b41a030070000000c3c0103007440c042d0705610500302030300090001803d500801c80303014040c0164000ca0300c01d04000e141001c070701080c00d025074020010041065000074201c40483c1461404c0f81c50030210b101094036045100083c95207569a810381142e450403018103800003070003120000c1d42149042c841c0940540d0042090350300568001001688087d425844510603c9004201c050104191308041c00290000d0180718080b80507080085600e20740031007511a150340c01001940b80c90300680c241311003c000d110f10184c01648030702c0b00c1045513040e03200a907580389000101c1c41c454a45400e00809135201c640c084440281e04000e0318104c1d4403518 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 162235215 1250 162233965 162233983
    0xe0f011212080a0b0613030b01090204030503070f06060b030c0904061a070b0403020f0307050102030f060409081e13080606100e0f060f0d0c0c0312060b0d05040c05060d0b12070305 79
    0xc140319440d0b80d00c3d5031400002d4110000d0441d8400800207103c000d044001c8142d2055034081c01d04540582e03240c6140300c0c01c03840790f0700000c0c05940c01880700000107175003180902c105610802c0049000d60703403420280181d030000d4600e1691540003040321440c1c0d052034418a00142080c005030030503540000340c1004c50703103e00a0f010341104a041c0005050500130000c903554003807620116039880216003840b6000b0340058800f514410052004199949401c0c060014250782021009140c0b103050b481e041c40b601d0481159184000c002d000b945003100c8010700c0c80c0000c0114070b014054619202e42044850f02c015400e500c20710600348002030507611a10700e0340440300400d45c0c040b60746050041400d4054051044825501e600740100c9080d0b0726444403240c42d04622944540c1a001040e1401100796000b6001714540450306120181c01041140c01282e0414000c01040401d50b407101d0108446501004441c110310b82c80d17981c0d50707041e0304050b00c200e02e002e02404054102e00e41140e0380e4a031910b5503c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 162236465 1250 162235215 162235217
    0xa09140108010302010c0b07020705330a02120315040204060504060305130818150d0902010206070c050c01030c05090d081e07020d03051c05040b0a0501090b0306010512030d060e0f011212 82
    0x5e0004230418003c01128000d050300030120b036145d08458254500c15464580c2d08440d10200543c40e080d44410041a0740c03883c04c00750043d121910100c4150062034000411000030340e244081ea10303a0540315440203201034045652104e9a03282080f0018003a100040c04e07595000e90728100303000c0420081d201b03079040b072000c40c29001d00810071074002640c19554042503801f044c50025409504e6401c2e940040074151007a0261045581c0e01d090584c2c5480f03004402600e250481c103910100c40d8406ea1100e403c101c00c90600074108200c10380401c4000c1002c4c402112002000980c056400c4490880d90741d8842c02e07120b20901c0c101640d80810503a000b0f2050080521001003841515280f021a0310400340ba00c0141c2001146400d0034415018401940d4918007945014004180c910281c05031070000b0202a008040c03a92801090298001100d00f4006081c08284145119403c0900400340146181d5650f03403c02c0c02c00c0020035048070b0041e8064882c150b072281d428000100480000c01e032020503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 162237715 1250 162236465 162236483
    0x608060912090102010902120d0e030d02100b060403080d06080106050609010e0906180a050411060424140c0708150603060109020d180b0405010c0201050c07020d170a09140108010302010c 82
    0x2500113038054071200e940294041d620b4004034901c04000a00014070300e00070368440300c4003001c00c400d0584440c0705100a00051700403056903003041c01990015a0fa481c40034010518056407034480b0442d90b000450030101d1591030b28400c10401d042400b41d00302600040b02c140d480e00700c4040000e850b50015828050003880082d0004250f50f4501e204801200c040203402ca0541c54080760b420700400080310101d40102c020128002a030030100207560a450403e0b03030008103030700c0d1031406184407002d041000042101c80181f0f11103078040440035240000b80302004115241c10282c0140c00c1080c0e0450021541c0321240c02c00c446654000b40710782c1191240d8400581d5080445030520286c075541e03001080d0302602c035481b04104206204030342e206d1405400204061440004100e0a0b18426074880d102038000740155000b6147c8071a032240c41e0341c0303e41801d20385035111300e040e80d2198200c13828600128045580c200800c07801e40c06403100040c0240381c440c5041d0b045a0020301207018041001c0c0c24244 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 162238965 1250 162237715 162237727
    0x90d090b1219090305040f12120305090c040623100503070c060605030d0f170103050309300f0609010507050304120309020d0b010807050d081207020a0c0305060a0608060912 76
    0xc0030342d101c440b038251070000d200c0d82540d810302800c29445481142d607002034200307000030705c069415502c040c4564020044002403020f05001c0703010b8130014141141c0d601a0f00c00400302d0b55280e2103124000d202c03083c1d040281403c1e50b103000450290700648180a455085a00c0e030324298018100c90f0300404c1820900c8040b2a40e0400c000102450b8006541512038485101c0380300d508141048042e0410382d9a00031100b0082c40703c04012075084c41300510030303441031002c0310351840d2000b00c2c80320316194100c0c224111819228003170307086020b5001c0940c00360405000300004440600280c1d9010700340e200240820f08108000500c1440700401c0905402c58400c9200042c4d4032903000704180980040200300941c4040c10100c0030b0718003e11804005115940d00011f890030151560440f01c1d400c140028103000002c4030346540d200c030051800c002c50048000080004062610b442c0186020360001d00d010300c0c100440400310360741d90300000150752201041007055100018115091081c00c040c0b943c40f80 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 162240215 1250 162238965 162238981
    0x302130e191104120507030f0c05090603030a020706230310030203120a090509040303020f0c011508150a050402030309031b09010609031e1104090f05010f0603020108150f04090b090d090b12 83
    0x500d1501300030300c80711038a80007006104001c027050f010358104039505445902c422080650b240b1640041e500582c00c0a9000c003c054003404152007520440b030707606078000c400342003607010036032080341c1d080102c200e52035050041d03041c10040c11540003100940145800c0501001802c118018440c00f0300c41d00c0c1581c0000d04040c0300c3d8040d205c0701c201030540141c64010442501e4060004042150101e010355140020415030001d81d802d0403003095404801d0549078040034001601e0010016601484104080340350b0751010000c0c910f1070b18244076210410b00300b01c0d0810801d810181e11031003c001c81c2c41c80610214a83c04942850f06080864180a602e610301d850421428966140f45d409460205210305004010980300c5800317103e080204800e002031a188011646c282c0000382c0014040b0303000403420b441103006140800d40091200b00040080000202916650542221810824424000600800c020b018100c08290811809150038600c1c101d48501491000b2401c00e1050000310340c43d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 162241465 1250 162240215 162240223
    0xa150c170702181302120a0b0603061501260118060807060e01110a050d0903060518191a040c0518010308220f031b0e0907090203070302130e1911041205 67
    0x13660280002e00f42e4241d40c1c0725140c03202a420815a045411030b400200c5034540440c0d000c0c480e17610b10480c0b1302070382c41c0040112040b0000f0414450b10400e44611003c8103201c440429000f032107071200382c0e01c032410a00c56100a44185500c220b100d9408800c0900145400000e4030ba41c0c00d00030310700301c404180040348052600c1c0b5040000303022401481d1141c040142d02410300401c0d02d000306028042c40c0c5541f111030902c58901c0c1c02c41c3d05e640c0c00000550014082d005402c94800d801012020101001c564542142070f406440840c0c481d5030b030311400c00041c01e0004074180030540b488a616220340c51274860348920320851603030741b41480c1c0e091403026010006d0b250388405003c15038980401151285040a00562030403141c0c50079440d810030001c0e108607514109803186440e0000f8103a4107283c61001e00c0a50806071010041c1502840394886c5038240092001c01401143c100c1d95060900c840b0b166081c4100e110341150050400d40c613104580c010b41c003114103c88600318034016004040c03c000e407c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 162242715 1250 162241465 162241501
    0x1b0d120e0c0f1c11011d101407080c01061401020604050a060216061d0106050907021005070306091506030c0201021204020d060e030a050d050c030112060b0a150c17070218 75
    0xf07204082d840c1c8505000c1582112a0450400e0b2070b20070078240c40c201103005901c102c6c1d100740e074007001c0d401c81102041c0c0310382c00135007144620003c01030502d40241c1e14145a5008120110b200d6991800c2c108080440202440d150001c28005042141065152641c40700d42114002c1d080382e0b00000c000d02c0598a642044900a4200d08208081800c43c00c21441409400001503144e42c01c1040c0402c5078603080c0d4040e401560140c00500018016042e0394000e014000c01400c10b0650302c50000030101c034140510040e10180c0c020030340880781032100140403070704003082c41c1085a10500482141019900302c0c3c41d00240c04035644403540b44a49410b82c003922401c1c12140f070600021070400d032181d81000140106001c80001070225a444d0401c071541400709100703140c1041400303a01280450700700c2d07200c901d4000020b03181001700c5072290025117910140540310000200061548010301c0080d40001c1111a11418403614024242d0005903601e84007801401203c0450f00100710083c0028a480304 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 162243965 1250 162242715 162242749
    0x180c1b1f0b09060306070909050712060611061006050403080702040b0a030c080d17071b0209070f0201050a060308071b090f06030b06030105160e061b0d120e0c0f 71
    0xc40c0486520203014000408545018464200c00b00c1c80900d0081600342c401c04190380c3d4011594a400800340240401a110300b0134040c2e18001d00e81c10002a00504c009001c458072458059040d11903454580b500040900642100764039041c00100e910200304c0d0202d030341140c083d50300c6850301c0c0005401801c0703452045a0000040d40004200000e541d28074048543c2c01301070741c088a074804000e4800040b050180c003000c44000c0c1c0001c0ca900c0c080c01300001050503c1c0c1840a0391403407580407801e550b0080e5942c502090510116580031582401180d5120240500a0244615690750510640101040202104030301c0f11203002d88040f11715004000d0501480901a2004540c0010b000b806a404260b6915000c000012654101401018002e044080e040451416115000c80d440400901510341c00f000c10000088005012102580305003042c002400d003180d10160302500ca9a0780000400c001404c00e4400720342e030440403403407658448044e07030400408a50b4500003203d0a2000008030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 162245215 1250 162243965 162244003
    0x2062203180f032102030405090a0e010e1f0615110f25050907081609080f010e07150f030c0e03150103030e0111031801020a0b090c180c1b 61
    0x141c0e094290701c00030201c901944580713043c0c80030140d2141501000424010150340704110030045d03030401a0089501c818008000074a0000044d1151309541c0e5901c00c1c2c271500d9010002080240142c03403e03161440076020b9003089a1442c203178011110926240000381802040034072083c0088042c80020b48005000d0140e80c4648207100801e050517151907030030102e810000801040d2070601304862805002a501c3c0c000081c0d903805501c0048111010000080082220b400114450204000c00103507007014000b0440b9030280c4401841d000070fa80c001c40384044407454402d05076401110400d0b10712120320707021401140034072060300da0040000c581340e05842204481440350480510440c103aa11943c0c1784152501c070382c0b00440702000910356841c510703081000b94980102098106211128041c0169172116046440350101981e0854052040742c10810000c030645c5056005040c40042000c0202c045051501a01c0081d014421044052004041134003608103001c001d40f44180324241a00707 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 162246465 1250 162245215 162245219
    0xf020d0c0f0f080d11060a090203120406050301051905130203070c14010c080709060212030901090206121905100603150e09070e0c121303180617070206220318 70
    0x550b007a0149100c0c4440314000c951182039450320500b02140501041d000804098540c40841c0e401052402400ca074144a2401d0b500c0c100005c0901400081c0001e449040c0c80c3d6242605010240d0a4030002c02941c8006050600240d40c0e0440d820b010004c1103003005032030b83e445420541d1040031110000d00b0700e007400d0800b070007000c00542101c43c403442250348240d810f480d4074100b079920801c18066100541c024200300010350f40120040e40c2c2c006c2c00780002140301d82242c2c004c6401a80421f0044003104000000c01500000c42811112088918001081280b42c0075850b04403200480c0200b400b01a19036000300f184084a904001c05840f544c11401e80c039041c4007540e241da850740361085a6180d150080002e10349000042902c50721480700d6107200c4540c2d5200c1c90084c010070390070412130500c0303421420710358030214417052040a425162150702080a820109804440c002000c10046600c40b004021a01e030281c3e140e02e0010074030310500074540c111440d0a40742e5420b44019001204100400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 162247715 1250 162246465 162246479
    0x35030c0705010c0306060f0f03150f1a13050f0607121206050a03020d060b01090b0c0703020a0b0306030c010e120a051b06030106050301060827011d0a0f020d0c0f 71
    0x106800d5115a000300b2205034141e00503000e840840c421040803400e210b003044041d07806101000070080035807900168030818904100340400b502d17009842410f0400006014244001240241c49070b0641e098505140e0102203054031001107028503801001c284220200381e4482c5001e0f982c0300c2e940038009000607804880024007503002462942c0079103040c60f900142c0e40c10f15520180030380e80c002d0071031917000c04030b5203c003400761800310030a0381044028030700048d03e42e01c40c502401e00c605120010b444400d10b14010400758095940143c42c0001e000c10500030b003507400154001c0c0c900800c0c2401c0e032404c03007030800084a1806041c02c150b068011002004108030002c292812400104035004801d004000c06014080c0400d01404000c03560800061144034092882583d001d00d641c2030305d0390001c0d004401c6130b000e110303920303142c800b41d030b44800d080030749403611910601a0b8191600104440801500c03000311900d140500680524001442d050070b006041407004060a03412028002c0e16a40d00e00e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 162248965 1250 162247715 162247717
    0x3010b250b0f0601050a050d09020a080f070311010f1205090124050a090b090708130c090506040b01050c070909111009030b130f032006090d020c030a35030c 69
    0x112491550440800030b81c0319170040042d180c152400703075034440c10612800c04410007804018001c0e40c0c0611480c0c00081c29040401904107407450140142c1941c07480d40c9040902c6080c461402414403003400e51659030141c0c80003140700400346485000c20303a0f8071001407560040036590b0481443c0604024411001c0004800d0001103900130784050302890783d58400d00c01111440b00d0341c11340c003400210104072558412441c05d50400c0c0380c600c04280e80301c0d50381d5842040d03100741da01401c05562100f040002a10340f501c2040501c060a003000c503d4000c1e40080542c4414540c042c10341324541c3c3d13051040500580741181180f0345009411080c031346030564006402d85402e03101c01c40d103c40c000800142c207408000c14907107540d5070080032801800d0382c07940c090310011065410100c00d80d00440e40384500c010100f240d20301030400e12019020b00f000e0360000905204050031007a00a5000d0301038200040c2a181d0140c42d002d01040701c02c00c54240c80c5160070b22056146044421944011050060810480c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 162250215 1250 162248965 162248971
    0xf0605030c030a08030402090c0d0f0506010206060306090601170705040c05090a0f14040c110a200909030f07080c0102031905360102040f0b0405030d110303010b250b 73
    0x80c00c841c03050300050101603039142c5608000b000200c0038000700b00103007003240000d508200500c00c0c140c2450b460325175180460f440300341c03035500c1c8035115800d100322943c042c08403540114050340600030b0fa2402c144280d503270b16030611850054444214401c507a0220911100014203402031060280350b142101c01085900a21038442c800d080c2070100141966140250508a13000c400002c190075401c403041000420142d00ca490a0001c04064094600428898030000c06d01c5001030344a9106416408034403480e0f5a00c80d1800780c1e08c0711040c40381031a000802d45008111000074159643c00618002004d409580550f9013558004000c2c0320b401e020901c91902c0d0a030003810204502c0e6034041103200c03600d00d40c200a00581c1000352140e041c0300040d5600c10b4000880c0d6001614280d501d07848480c0f0160517034040300350230f00086010320440c5402d0090000b030309210320740941c1100302c003a045a00c81c40306104507140e4600000345460550350b40c289501c2031000c04c40c0840140c07201800d118030710b40811 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 162251465 1250 162250215 162250219
    0x6221505010203071502090a05090a09060c030b0a091508070e241309021207140306060a1508070224070306050a12030507061104031a060a0b030403080403120f0605 72
    0x81800305580d44004159441c040d005400030701c0701910700801c0c400a51043c005503421651101001c203145e152841901d0003440700f414000b40503206070414000f1500c02c0c9262108060400c0912405135486c407001505907400c082001810045850880d811010254403902e607a000b00c000004034410580d0a17113204840c12030390701421004502114101d0140000042c0c0c0c00100c4010342d030402c0500398801c01302c651007d414020a0348074081e4407460110540c0c800340d0201540c140007012410300340200c68101c90b007902d0040c1d129040080c0708c83c1d040141403103101000311180000e040280700b08640090b003035060001c0d500c3c880082c007179141100000c442c24004281016400121424014101c50440f02c441000f080d40100c00d80c0c0454041e448400c098410540714a1100d1490fa0408000d10043d4810441e54000085800310214a4900140134510518209a04011441c0c4c9a4112903101d6458a00040307165501e00c2c09980c01028684055802d514140751311200ba40594000400d441007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 162252715 1250 162251465 162251501
    0x6060427110a0c1202010608030409020d0b061602060d02070206071211070608070309050c15041d040b0a0b030f010504110a21080a0908160f0801050402010f080622 72
    0x107404440c403502d10442e10a580002da16a00d5400032444003408060b44082510020468640d100076a501e5a042034001c2d01c8025400105002000d46900c600ca260320002c0e10ba45040040b8266103007000241e040c2d001e0b01681c3d00094000e6103610030341c101c0300950b50051a80342c460a550501031411031000c08814003003600010140c160043c00520310084900d01e94881d000e070b6448003403c40142410900850f000d1003900742c003102581ea107a8445107011510b900107900c03135241203456891412203c5800054101d03120600c8041f9884040c0d40350b010400c40c03400300d1101d00940c0820b2405c01075840019455182c401440b0800102e10718103110554200e54a5141c603440781008c005402c84122108500c030341d071050030360000b480f81b0084c07c00503102d42001030946544509490403c0d4001725244c2a040e1141404c0c01000e000400100c00f400c1110000c01040c038040c0d0000c0c20321044100c28105111030580010100d42c0c81e9090910704291009140392140c1002842401030603001da00b003515414 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 162253965 1250 162252715 162252731
    0xd0e19030503041716051002030409140a15030f12050702030d0801081b011d03120a02060a1802010806040b03030f0409150e0702151e041b050103020319020306060427 73
    0x241c1d58010200d002d4040745e0320b840c19007001a80c540e21b0a80a0a40c00305100000b0a062a8412380c155034640040c40301092904403200421030b07c0c40886942c1c40001f1100034000318510901000107150b01000c1100d40d4035800d81e058956008560380254148181030b00c185a10754462a5541294007001c107d0704100c001d5079003800d040c44e0240138607000590b02c0880b42000400201d4010f88088041c0a9880880b8480c0303c4210750340c40460800c0140c1d200400b404883c000d60322542585805038030062041c00030650008144140240142f0b200717940fa0680703414165001d20454100e007a108030640e503a5546c8814902c050000081c0c10070440f8071098000408240040070188070f00d0703140d805490111180910b8a41417a009032014801f268a15008a00c24074240e180602442c06405c5101540000d22061154592150089410107005205001c203d207014be0141161840ea0351025880f07986220110703009004036800055072003401c1d40018841d524091946035036920300581401044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 162255215 1250 162253965 162254009
    0x11401050105090f01031107050a0b0702060901050408090d170c0a060509010e07061421061f02030301050d140604030309020310020c0309040b0f090106020607020118050d0e1903050304 81
    0x3c040d00c2512608080f0248481a4641c030940c400810000c40003c428203000494403018074190340388404841500d4400103124950b41c0401100360b1001c1250020b01c5140760690300c61889000d0034405602a450403800740040100e0901707060000e80c0f92039641522825a40d90b000c0d0340d5001c034001540c03d24a40004030351014018001d00210140031401060420318050046401140d0000c03c85c4803500c00707004060b080380d000c0000e1181c0c9200c10369400200c1c20404108090502a9581d42c4411440e003040701c915a0340100139039044031000c4801c0c442d0122581850075907003003450320302007060107224100000c140c2c041c0d02c1150400c0c001d80850b0009981020380314103d100d2001000c0d44c55006010341180c51400b60000d54401c040513002e81045442c100101e01410404c0e0020809030700021b0803c92015824402c446c030140d1001000022030190791030301d545401410005901300000c803040300f10603440303141007054200c06400c0300a400030f64901b4000d8590700240a107a1803101e010441303040b10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 162256465 1250 162255215 162255217
    0x20d05070f060309050c01050717041409070206040f1209030b0901092d060b1507061b0f05090904140601060f03060b041d190213030606080d12020a0201020d0e011401050105 76
    0xc203505c80000c0c0498400d040042d610f60f0004801107549440d03807000001ca2060038405400180098807002152842040402c607020b4801002ea108640c801010400810300f00118240025001016800310001c8824211280202500050900e1a0090910045030415800159154000c110244001e400c00c83c1d011401c954000418100b5880075115038081070580d400591070b404024030051200c0381414941506810108059601c20707554022403182403030324050f0380e00c07505103071400c04104440749001504900a50300c1c084d00660a4074000b0b0100600005e0000140646404407600c560351010000e051120a502090020341040800244400c1e0340041d40c040e00c400007020900c004640c616508180d100410210500c0b14400c1100c9030440e452004000303007801c0c10101d440107411401c1840039940294042d00d02075111407030080010b58009a440c0303100850708000f41c3d03900c012000490180c0103d544e8280054a0700c3d0012102d1001540310b4104202504104920350f070380c0320015111 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 162257715 1250 162256465 162256481
    0x150c170c07050d030b0616030e090a02040b0d020304080706060e0702011b091224090203010b060a05032d16080a11041404060e0408030103050717030d0c020a020d05070f0603 76
    0x2a4402030310780043d54002e03003019a02c00c0b0090010707810200d180c1840c91104000000075000304581c1c8000e10350b282408a031a940c0301541540c15841d161070221258500e01c2a54003807049558003101290030003501008039049207801103c00d002c282d8903603010a012080a58020b00558a03254840d080142d6a01c1d00000340007490b01c800c48a60314010a08010088201c002c0315804411084401000d00032501411401c0038044001030482582c814182180c0c10b00350b41b644102414450a46e50f5035010b030071a0740c82102010000030070001d50300500320400c03c041502c1349440d405010020f80c1341202c2e810204082482c1c0d82d541c00d83d103600a00c11f003129006c201e1a040818200f20030721050001210404055030040d0000540580c1d42c032007461a000107507001c40f008040000100240902000848043c000c2c08000520f402e000040207a036a2007003003401000d254403021b04161490003803100411040d00903001c000050a9442d0294448956000d416240c41e110000030811910030300c10400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 162258965 1250 162257715 162257723
    0x105120a02090403050c01020d0609150e0903090d0206191205060d020d021e030304120b1f0e04030c021e030105070c05100209060f0a080901140903090d150c170c07 72
    0x10b0b1600c0c0d5450444e0154040440e0515940d020803a50400759a244180001001c44c0b9400150031000b511103580240d2140c3d00070300c03060707007400c0501c401c5c03200100494400102c115003c4c002804584045219402401250441311140e6000381c00c2c595001510006047d03d45501004269a14000c01003503061005029402800c1c0700c900f500103084c12003907496500c4104080046102c0700c000001c1c42c1d94000e130804a002200b00f400d00e001c000d40245015046038511004d44c2402410580e1903072030118602c160785289818002003018140100030603d6415009040100c13603500705200040120340140d0340600070341c40c7c43c0019000381d10658a02c1111036000004d03119032079030000e40502070340064000da40d00900030482040c1005040d0300404501d405a29203000514050700310908440c416a103406103441d50764100845400040211825031b401200d882e46445010b09000e000c000c4010425083c441c0f070512045002500001d007000c0501140b024426942c4c0d03517410000c664011044001c2c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 162260215 1250 162258965 162258979
    0x610031415181311030c040c12050c03060d11040609091a07080606070201230408060702011a010c2006030a02041802190f020a020a03080d0510150c080409140105120a02 74
    0x43c00140c40d110312040d204000408840059000c240040c04a230400e501d00030210305451006000d0300600c0c0149a4080d9961690320300703615024000c10360750703c40a0401030000300c0d03c2c0c140c080142c3c0c0d20340c08140580401141006525102d03c2c0c01036422043c84525103407402c1d0354000441451141200d94410440588504e00f008015030041d038061010129005000520750051000f0312074002c0500014520480209640d0604010280c01c4034005808120081009018007129981250303510418a80c030007454a0380d01751540e0000b07181d1f103128040c1c507403050001050040201d8941c014005440502040c40029080088444100d04c50760089a181c0e0206048010500d40034000c8120207881c1801543d01042d04c1d80d001920202554000311081c01d004100303100b2100691185991241184541403409800c0038400b48038100e242d1a004200844030064404105441c1c0079a00141404c00d03041c4000d003030703002d480c2908260034007516001c0c1045800c03001c007103c000503080446a4001c1e0241c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 162261465 1250 162260215 162260251
    0x3060b030705061e0d0c0503040b0f060904152d0b030102030112140f010f050f160909020a180e0403080601140d050c0918010509090304030308061003141518 69
    0x5603100780c013546038041111014000a0710401003030058a8406809580b025513070702d841c0c0340500b0302440250844400c03080703800c10407045482e10700d501074016400400d40b415a0800300f042c20043d00c031014081c040c030404120301144a090703d40c1c4251405c49155000e01207090b4070b0003458201d0200340b190f480c2001254488201052040c00e860001c1c054900540e400c03018220489425280c403140740107040c0342c0d51410000842c0d80300a0030fa130024a00794009000d040b00e40402013070003200d80100008141e00050040c0c940740aa1100c0b8940d0030f0318040c240c0341564801c91608030310011101900800c040c480001c0307444d0300c039000c4400d91081c8a040e40d42001c8814007010000c0c00001c0c5038003500740040080340450369510321401c8202c020f40311011525130508003030280f603007000b8101500580c002d003c10b00c002608a21385551200c2c0550700c1c0c02402303500c00400c6000d400020715901d2500d208c0d505114910012000002c07103900c065500d01a03840100c1d501034002541192003e050f64214600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 162262715 1250 162261465 162261487
    0x219050307062d03091a10050103050103030806102001020d05060303160b09010618020d2007200423011d0408180310140c030702071a041e03060b03070506 68
    0x103100d00481e400d2500017880100c40c3e40b03400d0003004070541d12840030060010041036210302a01d000141c1002c0c030703040c840d070351569502034000c1c000505041e00c1000c038a00510b0310b85224a2010031540782c402000b00796400c00d841140c1c000d51001c1c0204c903000e13091400240c2182000400c40d5600440c801c50107240140c42e894480c02981b0251001d000755480c0d40000900c160b03140c034400d1401200b07940c0141d6449080520784119044074281e004501c03a522000d105084030101519217858024030180c03941c12929101c13083d4201501501e40d40316261103e485149003c2602685010044d071840d100c140e40c803a11201902042d00825014006041000800080b045409494241000249504065a00d0000074144180a1540e0802c1580c030880511080c2c50600705c0b035040028030000b01d14604003072b14000d440350381034000e0001d00948103003402c00e001c06040460300141141500400c24080c500202800401d0f144401d84206040040116040c6008181c0ea402c0303a40c02040180f0348820071003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 162263965 1250 162262715 162262787
    0x8070e0601050a050f0423010e01140f070b090c030d0c0f060b04090f110a170606100c05071203090e330a030809120303040305160f021905030706 64
    0x303903c04002c404d10220010444001c0a8805449216030110441e13002e40750032168144140e107110f04102d1819039800705a600805154945640300c034402e941e40c11070010107489445081d60007881c405580c4204241801c021901c074004140450903114406540c003401c032400c821410014000d1203400c414480018100d500c0895517240103040403401845580300c040c1341807000321080e00e41212404034914a440d1600c01c0e01c1c09001c0c001d13945410348420041c480c1c0c0d07502c0002d041a01510b0042881790f081c42c042d0814154140e8010100d40c00241c4904a1401e4004483c104a0100300460f9000c2840100700150500c9800420755440d41031940c682a10748411080400300e44056400410b460740385c0700c03401c80d403001d58086d000305551342003500e080c8400d0405610407002149c20900922000a17070100c1180c0b04040010140c065040d001e080c502030969100600a500251a240c55200052640740c0c01c011104114107407040c3c10380d04c0c64165a01084002d2126860407040901d04510318a46 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 162265215 1250 162263965 162263977
    0x3071203050a0624020d02030412060c14070f02030706050703080402150d090516050d02060301090506130e0f0f030c0d110708150a1506080c090d06050c070204050108070e060105 78
    0x16502181d040d40c1c5920030801c0410551910001c10702650070710891540401c24401000803620086151612b8079602058407034406170020016600c58041040d0540709003004c201c52072000102d9942c49080385444a081c22400d90124003d0003801000144580a0010f0350320341e91305900c1e1080c440e6103a07800c002c6000341c003c100080c6c1000074410030403080a2440f034400001d200d0f90080c07284003d0b07140c1540403005943d101e1842030409110b804016280e00060f64112100b074407004c1b0761034a401c00020070000700036007840c82c0b0310300e00090045041c100081ca01c10760340307800301500e0310032038909922a1a4840c0701242e01d030a52044920901e294400c2120000500141c010780342420b4070b03400c40741d0414000341e8000c07106038000c4040c0078004503944a01c5501c3d492a03c05908a9860301c1c2000e0000c040040c2115060040400d4035100342d00e62042c29200d40354006c0c8100130798a06045c0b840d10300c0e0044a0180e020318600720011a09200004256007525015001500c050303a446004450543c800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 162266465 1250 162265215 162265231
    0x80708130501110c0c030c0603061f020c1801050f0108010311010c030c0c1514040f050907020c13021308010608070509130c14011101141603140a09050f0307120305 72
    0x14110b52460302d49883c1c0900000e00682c009026607024500801d444c0414280e20a0b11680081050203042d541d48040c1e40c5010006022004010150b0f02c0180d0505000a0006070009003000c0076800c404c41c85000319040c0c0d1130407a042c1c66079640d00e400440d003000007404000c00d203441003960b2440c95809100302c1ca441d20701c20b20380544038108903070702c034003002c440c81e44403850084800c00850360803600720b000c804003010143c1900b4101890614840041d036424071a6500821004000c14149842800303007480c048405029490340400b84051400254231003060345004654181000c500c141042c040c103401c942030000180f820a04040030810400000b400540c5807140102d802400034100440a400405640e0599a000b01c51180090700c0740b508000c0030180d80e454141d01c1e04000c4e5402d6001c980001c14030030048003400b040c5900f6001030400030020300d2880f130740c0020000465903079045010142c0c401e0050f500310400b0007070071355903038054020000c0140341d100f844034039164420340c0490381c05050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 162267715 1250 162266465 162266471
    0x20f04090204030f0203071502070e06011115010501080105040e1c11061816031a0c0c07090203011e06141e07050a060c0e0a1211040204060906030c080708130501 71
    0x19480c0003608a034003951003154020760000758407096103003d11411004154039100c00310741244060b03000791100c40e02d0240600c5c000101c808550641d201d03404900e0401c8040048904070f007280019804400000d06c035290024032039070008640e50034240a54182d40100c1e03402041aa1071104000b89180152000385080000d240e848120440d010040180565040c242a2960241d070f140718900780305072102d08103220300700880108001400d22403042101c50151030340c8105920740f01c143e2140d51140307064242c0240700314080030400351040c1d030045048a107100030000c0d01220344220701035040c45c3c42c429080407400b100d0707450741000c1540004080d105521480c80e0003802d503902e1540d416401520050310705501034007851082100074442c0e00307082c21071810000d8a0703002c1c0c040051581c400700c0c0a030ba4410b608901e20f010411410713080d28503074011300500549d11a51150b40003080c041c030130b100f20000281040c1d089000d441c080c140c080e026407006d0742d55100300e9542d178881440c074221146040380c166603 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 162268965 1250 162267715 162267719
    0x190b15030a03080103110103150302130e010515131a13060510030204052d0402070312050106170a0c0c080702061c02090f30150901091a04050709020f04 67
    0x15041c40a01030a034401d403a070103225411428028000d004184450b818180381001013020401f1000c02e44003100c1d4112010b1060100144601c8080e01d41040c1c0c50920351300300703000d11041c07500c54910503071010710540340c20505042440b9100256010b480041014081c503143c407641c1820b10384001c0340c030301e95100c1c1c011501c6541c680c040b0f00e420a07003200d1240020350114051011b0b18100a64644401503030a1a000c904c3c6a40d01c01c00181b0100c4030031501c0f07039070700082002c00c00d0300071031b403060003114105001c01c195a03542d00040c060320000040034900f2030500c80041d50f1000c840c880c0c1082c1d5180f40e0348030040f2300660350314400c2070f50250340283e85c41001406442c460300c1ea404a00c1f21030400088015032108984400e102c800c2c0ca030b28600750b11404440c05544441c6103200041000054070016010b02d02c40d80c2131940d818914481030141a03096030004010350190150800c404882c8982c1120b40a04400d0030b891400e1141a01d000780710381c101503810816804260082c002c003002110f40d0501d016 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 162270215 1250 162268965 162268969
    0x110d03050408101d0a0b0a180804080703110109080c01050702010c06020c0c130b220212010602010e100603050606040911040c020f0c0a030209010b0c01020702060703030209040608190b15 82
    0x80a08407440c030f0410340340e0803000b1144402d00d4900104a41d000020509041d00d5074440710f03028030082c003449501d076503000403107035000300d80550748100c68101c11406d60719602d0304621600e50304039000640b4050f14030b50184200307500c181e0300e40c41100c4200000c0d0180d10f2034840110703030035400940141d041005003541e500200c1c0d880d10080070300d10102e20040c02c0d03102152060003129203115404683e164a0130032040e50075220f202501072100000c1302d50369401180700060400a00903046295120300b00b40f00040780140d01503010403a440c030000e044071003c070181d041103415611030f40001003c5401202c0400c003a8282a003181030103500c2415007030b0002d01c03440301040458584008400040c0c0c0000d5000c5402c800500c20013910705010742e0309008040c1140c010815016040c4541d000e107000000c4c103611201c60a40c15118030b29801008103039500001c0c20010046d420030440d041c41a854244009100440040c0c00c40f4540a0400031021105d42d5485450040400400c0320240b079000d2040705d0800e13 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 162271465 1250 162270215 162270223
    0x50c030a03020703052709090f03090103090f0611130f0b070b0604270b1f18020408030f04031b180b0103090807050123040305190c020904080a110a110d03050408 71
    0x2e20038041040810f114600d01f0041406400340c00081076800907072424800d500048101c0c0e070000c0081c01c01194903000c80c074000e203200344d04140142010703207807540c0740120b691008000d03c031b40b4103030380d901c24034035510b40c4408000d00c0d101c0c2c440d004800c082003000303000140740609000d40c0228010400158100081c80d801d40c06d1004500342207200c40e14000c04000c0101280500350005401c440d2540744680c4c006000c0103890b01402180402c0398460054407000040e1b030102c801030602c2d1410f80ea201c840041010303001f50801e02080351160440014090b052940c91001c0e0111100c604e00c0b2080d15030608000c0340240324010711070b41055101d0b202e000110303007420300070b089a512030000040c1c071199a401050b50078081c644003900c411000d0051001113a40042601c48400c600d084150400c0d03403e80701900c0b00310498000039001040d11041000b442105000781101d40d90f0783e16030b910141641000d090b115502d01c1d00007402119110503641a1703041c4040847e8081c3c0c42410003514042d1100b100602d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 162272715 1250 162271465 162271507
    0x8030708070e0f1c06061502240c0304241a01050705060a110c06040819020f0d030c0e19090615120c020c0d050a0302011803210b06071a07050c030a0302070305 70
    0x28847c010000c1010941d0400c60b4404202c07000c1b0001c005030720a5203041620540103081e00407001c50110105003400a0075184034401d4240c5019a88001880030088c405032041c420703503210040c02079a6036900c41d4064401c1350311881d030020190400e0b9450b00b02041c02042d8070108a60903080511402140b44010003030140254011072206d9114a03c4080d07007080404242034420464210700c0f0000e0f1861000540c000e01c00c1c00a04012a0415508c0303401c0b11011745482d51b40c0c0d030014001011071007240e481081d0304e041c0d9050010a000e001e48480503c440702455100c4100020a05241305404082c0c940c0906c00220844c81500c111403101d0001540c210350000741a43c0c00c1e048400c40c003007016024032481600b180810788903c441b02103600e000d00a080708040807503482020b45400c25803e030030f56011100908005114a4a035801814686410030f0564500d059145021740030501443c000d00541d401c0c0c43c0043c0095291140310301040b0702075000464210f0600c40c0610500590300038a002c100c0d2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 162273965 1250 162272715 162272729
    0x3060b070b0609010f0617040f0c0321080106020c1c06020a120e0706080c07050106080f01060e09120405130605040501231207060e030c060708030708070e0f1c0606 72
    0x201c68100402004158001a44000c0300060f0081c0104000c54110381e0001015100d603841445640c1c6500b000e41100080070001080720348014000700801003c2c0312000c01600a081185001c0656840700b600c886a080c0030f48400340c0c0c00007500d170703000b8582425250040180d180202c4211059030b43c4007000c0c2d0b0001c0d05140081080c42601c914003401c54400c4620b88420000104a5980707408405868241c0151444400103400034a590602c0b10940202d001401981d040b40c1d540124040b00a00030b051a001c0e90b82c540407800b0102b060064005038500c80c4140c641c00552425160204100c10701e40213904510002e03031240f000044c15901e81c80781e03034001c2240c0380c517a0703080c0b036541064103030382e01110440d09200368400101810500c000042400640d15982840548404804000b80c0b03402e0a05088a5021500049203002c1154a202541c015115500d1380d041b551900710302520700c00300003151140c101058090500880c541903802401160242c0e0f450740d0340071030b6a05e0307041c2070310421b420040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 162275215 1250 162273965 162273983
    0x11a0d0e06070f14121503060703020a12050402090711100204150807021911060715061d0c070b0a02040b180307090207080301090c18170616020303130303060b07 71
    0x607020b0f8000e465020007108a14216030f00c92095509060386000b00c880021031691704000080380306070002000321030510001c044078003500c0c0c040b0004019500140c0300000141d114090020007501502695015640c010903400c030380e5542d01e004841020480000c50074030b10426210428a03821440148040d00000f60300c03034203d494a90014080d60400b078494002c560040062101070002003203015030017640014408011039401000890502803014044c148184042d94007080c40459801a0100c8030350903501001c0403003c0302207040c034160859581546000801c0700400059000301c02c00d07031140c51000014149030721213804550f40d4200143c0b844500341c1c0900704a0031f92808210b03241c01441c59080640c90211184e40c0c0803818001031003913801c80c42e244d00101008034092540c1240c444940c17558540d6450390b4001c42558540c00c0c048111150080b81c01150702c0308150381500d0340b44412a00110b1464440d03080d1001030000621041d02099034492021401d0903000d0010700010340182c0b102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 162276465 1250 162275215 162275221
    0x6090f030e0306010b0c1e03040819020a09020a02060403050915120708010806060d020d02031005100611010c0c020d02130e0106091b09030807060b03030301090203150d0b011a0d0e06 80
    0x3140c58100185c000040d130100c14000421007810000c7d0038114140b03000d810000200307102034110302d58007a80c0c1024660340a4101c1411402103080c002108560007201d80d010066a1050580d08038400d2030360002c0141c001c5000240400d000e20020519244043d1220507842d610880305800c030f8000340c840c113403420305603003c0c4200e8590262784180984501c0025040034189400080c04404040a0003401040540d06000565406101c0700c02c4207a5101001c1c4039915000e080144a05009e00655020800c0034a0018408905210380721203401c0549400010103016020407003002d4101d0422640280d124540f107403010040c0c00b844420540c11000814800c2c282443c0790103807047d851055010003411204820800d81c0419144200e03600040031603641c2405050600140441900341c94141c8000000011841e0f140d60045106181680388440e51040d00010040f000c403504002401141c40d440050100c00d102e58a9040c00307021000103e0320301070004a00d00c0948041112144a0350804020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 162277715 1250 162276465 162276469
    0x50114270306151012060e01060e0102120304030801211502041a030606030c0a0909020c030306040c03140606032707050910030321090501141909080d0906090f030e 72
    0x1c1e16800504155640099800b16000b04144d018800e01d0801004507070a0f640c501135840d644030b05c001e42100059a00590384810010742281c0a00321b604d0300600c02d02c4140901038540340141c1c0c0c002c690641c1c1e40c0304e440c0d1800c0541c0d10f051443d20140100440c01d5034107400007070020f490100800c41c41200168603a0720304961a81b00c6103240101002c03142d401c00c01c000c0c5c50b54814048035441142840c000e40c883c0030500c0210780c10b0400c3c1c0c0081030118400100c540c615180040950301c2800103d0f03041c07003141c42c01c40c1d044098841c500f9050b6a0400302c40701050443c50320b003014591001600c00030200142d1a0805c2e424140480f08104895400c030b801c007400141130034558151b00031010003410031410f01e10f0b5402003452031000d08042c03015210304403084c0360b0801608100005904080240003c005082100091007801d0700c402c0c1b10101510083c2540c0300d0036020740780c801508054000e09101c10108014040c00ca120411900d069980c000c40c0d000614a14580160b540a42c0c0c503011a000b103c01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 162278965 1250 162277715 162277723
    0x60a0603140703170313050a0609111002100c020c0a090603020907030903081807030807051b040b0a05060f07050d05030403080a0605090402100309150f20040501142703 74
    0x20301554001940c284041040e09070589840300c40c507004c1c030765079a42d09000f507031400c0701016000307011380584c41c0c0480c18030825030880c807503030742c0103400440010b2200000c010503021a00b03510005a005400428604012940404007400c06070040d6080040050001011041c17030390410765260390b54240c01d0055082001080f5880031242c03c2c200710b4002c880c0c6014000a0f8000c05150350741000425121582a00303001c0340000310350200c21203032944454a062270f2070310140c02500e20302ca64012102c2d00700d4039190150118805c1d020f0301a90106050000380003c0c0d80c0240018089010104865400907408208920200c0955900c41e51603080c64607000b0f0207644080d2200740b245060080600207552811440c40c2c00030b070304958140c0144202841034011304000c1070060300450080029003190011500010031030000740390200460007a28a00c0c550b004050098401400000e0005100c154018006042440d4107000e2950900200040816400782c4c51081d000d10003c00c166010704e2414100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 162280215 1250 162278965 162278993
    0xf110f10090c0b1317070e0a02030403180e01300c060801090b0603010b0a170403030c020f03030c0313020a030606030c090b04020a1706010e030601140109060f0804080d0b03060a0603 80
    0x2101440c0442e003024070080101c01d4026501c46035603403651700301309610400080b0300801c64181c640e440e41c80e181d03120300c0c029041140d050703011444001168040c004003000c0201904d08000e2500516400e0803000402880400c4104541c0e0002c8141700da003003100802e281c02c2061150b021150403c0c24484010070410040c2c1c01815020300303003048040656520019039054644400e032003a180c0500740d20840f5081850001440406491001e100a042d815040b2105207000c3d5000c80d2010400c01a289039240b008a807a10005802800441d14000c551680b41c101d0300c3c0003c000c0c00f103490f16903c0744000c0300c101d80d00444011400050030008400300340038000c07a00d9001c440441c14101d0300300380901000040d10f0076072050f80842e8001026030f030080d220103000e000082c0440310310b0341e1030303084880d8914003044d02070b030114984035000200144a61000102d2003003a43e1441203944075075038ac0d100e00d500111206200313a0b846031404074039034034208005481200000c02c04a1750b54998240100ca1031101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 162281465 1250 162280215 162280229
    0x4150b0607120807091e0f060c03050403020909070e09030319020901050702040b0406080a150b060705120d1b0e04060609050f090c1608030a050108010504030f110f10090c 75
    0x40c0512404100942d090618400190410082640d90180100d45a406a4000300c2e49034031490b180c1030355090444d01d040141c0700380d80724511496480707031815524240d4444000300024000c010500c0141082001c1d2038008082004070b030515501c032042c06428520450325001d1540c070210400040c901502c000c40e006003055182107180c40d0001d00000c02910540001a01450700d40840c1040c68965512120042050f0070a540d01c0450500e07001400c1c0001d1071281590a0a043c1e141c01540351000c126420b856200c0000d0603c40c86028401956400814075242219514002d07a07400b40d000b4010a86100c01c0e591f1050700101b600000c001c1110740d160480710030044040030500a50b12020020606603d00b22004203466503181c0385144580f040c0340e048a031881002189404001040d0040c50054407008070900c02a0303268800c00f8222402114080c00154000c010840c0c418000c0724112400b844040c1640e9800110880c00c1c2e03e403540080490100590740d184040c1804111140c041c0a8011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 162282715 1250 162281465 162281467
    0x10504050a17460f030f0e120a0b010506190804051932190804030210030203071707080f060402090406080f010609020c031b0f0706050403020f09090d05030604090b04150b06 76
    0x1500d540321084c02410004081c004c40340602044d460040604800c686401013440d40d00d0080ca2641d81d03228012410102c1d0306140b95000072545103440000d031400001c940d0b1016001044110f41100e0000015000b0781e180c0c00b80300e00c0f604c07c013074000740c00210f41030246105900b40c45000418255581c10308498410740710002412071071142000c200401d400c0c0c440303065000e0040160804191501c81ca40c0002d61003840c41c03e2401025030140c0155204082944440107040b4a5155040a036041102c0070700004146e800062000c003803120520b9042140500014240202800801c0444041c4c0d08690026400b43e041011410401d01030f217009030141c91310640c1000c00c60042e039039490040d0b4011a54030b543c0c44040805094042117003030041c21220040341d00c001e54524010b005a401800280c0c003d44074041c69880c0c500b0020f07140e40c084d2941c1e00080c04d2175807040d4002c40e05500060007442e0321984441d1600042920441414002d5002d00c0c1c00c18015002e1518040031503d40c44141409140c3c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 162283965 1250 162282715 162282853
    0x506010801090c0e031614011b12030608030315040e07030b040b06030a0c15090f060818070503100e0d020c0d0b100506030106030911010504050a17 65
    0x1910080301411212070140120380b2980b0820f080d18504400d0054640520503088980707456284000502c049901c004c800d60000c0c9800030046400706805118500210390401981c00020710b20750b01040c200c03040d440c0010300345441c0e2603082c0c11030740203986900d48001c2e0004100b100f803030184200410900c6110040050604c1c6039070701c8207400001403010300345a100300f00140c02a1418440c14242c41d034400d184900c2c032515a17040002010080c0c0b03095000510b805ca0101e450048000004156030395611400719075518101e00c13031049520884111824040e105002415423000c00400400160b01c071800319075080e461030706520f082e000e01980d604542c0300b16020000c546072000010317070190f045500074030550b4034850340e07018422040d4881504030300d00100000729607038164042030150f4410111000d02c104041c00440d001d000324042c456020b4030600c0c0410450300341005d080343c1e0711000e00c2594501100740d40541406105450540c01c081011404606141030313076100508604282c84200200750 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 162285215 1250 162283965 162283967
    0xe10050a0f030f0501020f07031e0306060909050a1b0201060e15010e1009080a080a08150603010b07020f0402071b060807120c0c2109050f06070b100b070503070c0801050601 76
    0x2007890720002c1c1c49000c0540ba968207214003034040354401e4005c12095a504c690b03d00d80281042a0311252000d544040101c0407541c82c4240621801c440304c9581d401c00c0207061907440b40c01400302070800c0001b59078500040080c1070420200c2c440d601c2103038000081c0940782491180303000d500201200d07640200000309440e60303a0412114108000d083e01e800489080c8804103869214040d0044201c92190881c0f450410414400402100d4565501e40c9215100d460481e011000400c1c0400c1d1f00190a10044c4072400703841002c3d2034944d00041c01c03060a03a03070140114089900c000300c01c0d1120980315910078201030111800341c00070f141500e42401645000000100b01215640440e24101e0301d4220408aa504c1030b034804107150703000349428080405ca12451124880c030b05c500784000c01c0c0500030008403440c10781000c00c41c000c0007a01c03181c81c20840d80d80d074442201c0c00516198407030700040c070003140782000d80000d002d500748180b004583e100c5071410002c03008115a071101344c442c2c0c1444c0401c43c0076 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 162286465 1250 162285215 162285239
    0x100f0e03073801090209150910080702030f1605010b1c060207020d021c020f010c0320070e0a140f070509040e12120a0b0a0803180301150e10050a 64
    0xd000481c81400c100c41945241810650b080350441091503090011541407013941c010003140c0e80c01c44041e01c600320408204000d0380030340b85d100b81e800f6415042c001501070081114035131288091050b2890080c42d80d9003411150400140c21220843e03202d001000c0140900c69050300e004200c4442c1884400500500400c401700c00340105070315004120081103485a6003588200c50f8020461035050659004a02048218400aa00c0f450028884540c554090400c00c00d950341c15070703103031401003100000c086402d480700c05008403184982c1c90300041084c3c6400d130240c02142c0c4110081521400707000e4078060802c01504400080b210002030205007900801211001c902c250303004124695000072141c2441910748041c91003d80000b01c0445140c0080300da01c0c810000c07640100043c0210030140044400d042c042c6445039030007000039560744550700c811261101c00050000c01c0071070b090345d80f44104818030362081d034515009400740866a40140142c0b006441c007501c007040031a2420450080c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 162287715 1250 162286465 162286493
    0x230f060a0b040f0509030d06090506152d1b0c0901121103120c01110327010605060a03090b070e01140702030c0603010f0305060705030907030320100f0e0307 69
    0x24065454600e00c445469580001c0f4003210b1440741002180f401c805455202c0d0301c01060111040e16141c0f002c1840616449a5030181c5006448449601c0c081141601198800c1e070080040351000c003080e48050a10307603080025403c42c08422034448800e524101c9c0b00b08428400000315801c0301c8402442a00c0d0030300941c2c111000101c00803a00d80031400e150703051641c040303101501401884280b8213410b5800e8028a45002d8402c020055804035a04110352400107455074000c81c0c0240c0055440c41083da00e0141c2c04025100c00081c0082d500c100081c0140e2000c0703900e90101c0d031248030681c02d0001c0820640d031320088034101451000c43d0080002c02108101c20040c0e181e900c0402d07084250b4130304100544942030082c041503521358490941100304180d07444100e440c2d00c0780e4400200380c2c5200d1001d580c041c0c8400ca004004090940d5015101c80c400b0b15060741c001d5100380b032080c5940100300014030b00c0801680d800180f50300e484480206603410540c10a42c0c46d1710420040b0009080d003181445 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 162288965 1250 162287715 162287731
    0x406020a0b061215011508040503030403033204020a1401020c061815040e100e04151b03050405060c0c0615120a050c01031a0603072703230f06 63
    0x641e07961030300000b94042003c8405120584280e81e40300721840221201d01d4180c604041002c03c030741b01078040482d4a0001158001e07c03a4000b0300114001038040d03009800034001250085529400354134135490355004045022004d50960800d00c000c0d0b06140c11444003604907490071400100c41d1200107550740006203e21409805c001820f440b000140c0040012040d4000b0700d0100b81c03c0798120340e20f400c1d4010f03001d5455004d0603500400c6035140c0d80d074131100031100340482c0c1921a0fa201e85079100d030b210031001d42d04421911803117800c90040f190210035031540200d0302c000400717080508090349400c10040c91441080c0e810484540e070900001000c80c0c0c0074410010007107021400c0341c0810000010807103616004c0c846c402081f401c02a0105249409900c00e036000c0000886030121000110a40042540c0014082021a141511030190346140501c4107080801e01e240050030904400d00d80c0c0c0c02a520070030440d0400051440f480090002d400840d03008101c4040c1404115460f1603001e01040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 162290215 1250 162288965 162288983
    0x13050a031103040f0b0408010c0206061e131409011b0e0d11030327040603020607060c030603020a080a15021216090909080a110a0c050618120102041a0406020a 70
    0x440007000c008036000303018002001180d144da0307020b04004540141c00740030a15420b214124201d28400500341d4031030b0030010301004109603110036540c9511206080baa40243e0803400400c03001d6954010340504103900b0070340158615102e00c003203003111000715092109042e002e07101d01c80c07903078045c40712033900804840d80320b0500400d1410440030b2950520960f09800085284e0b04548800440901d149846c0260469110422800c0008503002800029401041800444045540c59002a20500c464240006d0380c586a0700007481c1405164868000303940541010b60402c00b0520380341c1c2029180d0700c415400d080c0d80d0009030f070200704001c01c078080190f98280d900d9001d905c100c0040004005140041080a10905104030154850001040401d991451204907442c000681d540e40e5500a00d0401600c1c1c20300c42042110f910002c80f88006c8001742e0304045003039440c850701111b256903100005039900d03d808214503803070b0300e00090341c150400240000c0203480e4012941c1c07602c26611005075 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 162291465 1250 162290215 162290237
    0x100e0102070f050a140a02093105030a11060c0403170f030f010303110a05071806090f06060813082b1a1201020a09260303070e010813050a03 62
    0x10500901500c007014019086042c418024840041400d400c41402220307080301105008043c00d507140c1913510000c0d082400070300007aa1507560b01003600303140c0b582004041d80c6a07612a440400c103418a00003a00c3e0754200103501c520706d9800000401001181d031010f015213203040d01c5210854060ba104c00750801e0302c5201802000300403441200c09801501e031000ea26400c0103d035920400ca000d000880209039017143c421014500081c2c201e0045502400410710a81481500d50700c4071014000701183d282c03545000704000b041c500454084514912000030094a0014003e02085000d00700c0d819401c248036001012442d108200d0f043d01e00415100c0315056020900300580160112101c61481d160000189d180180d614114188050403110000f481103642c0841d13080b0301c500400400402d51102c4104640d8070040c0016a589203200c00d01890044040c5d4000e0440d401201c06400280c6401b521440e80d40e0004210350300020218041070012078a56642a9140031555002e002d0005202c41 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 162292715 1250 162291465 162291491
    0x803070f06020f042304020705060a0c09080304032a060f0513030f060b1003021303060e0307080714010f06060c08280c061406010905060304030522150e010210 70
    0x100c40e2080c50b12084a0342d501e680e9450030101c034481e603600d202c10048038802011740d0303c1c1c6070096868040d040405817640f501d800d00e44038000d05a403030440041c03023042d120002e8004420700c0179100071070044544030a003d5080000400190303201c842c80d00190b21a00d02800102e510619039642911681070540d03540142e401c40e480003021541c0020a00280c040e0300600b0400550400d0344040000d90b03842001469040c001d6007640100c10202c01c0c44001942c041002c03807440c0d04030514007203100d4103584c680304c00c94840000d2340d80a5001510340d20328080c0d011464000901c91800c0f403d4201404000d510709281008001c0200b0480c051300c4d510300420404118104142800301d1080342800d80f540d4120509070141c04440c403202c060780e8643c82c1417440070b007000080c5026032144074160b503032007011340c1480b08014207034001504c280e080080034016440c5207000180d5500402040c0a0540b040e1464204015100910480004200034840c443c844c0183d8002410400300d07000564041014500c1c240703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 162293965 1250 162292715 162292717
    0x10f151101060e0103061a0411030c0d0209040504110306130309090e01020c1c0e090115080712050708010f05060a0e01050d0e01090b061203040608010e070c1a0609100803070f0602 79
    0x108803ea620f080000041060592040540303003c140e001043c1505040f00700002c031000f142d10280121410070016580f02c1402000345101007111000504010004021804443e0304880413074005500c606000c03614a4100800c2c0e900c50404145442501c40980d001004045d0b14480d10080070344859080400e40302c00e40640e04a03030b19070421a5041c0d0028610314028041e1440346a010070743c441e0341c6c1045070900c04141ca05a41c41c417041801c059500e514111044400107000604100a140e020171100b200c40c0100d07801105d82d5a109d50855040c4040c240003a00194010792144100304028000c903500a072038000d00b2942400e02c40d488007608490780004c1e1040c000c02400700d51918880c14100807046482d50300442d01520015066000c03580c1c0107580c3e1140c2d00420005c210300780300408c6440948000903600c62000d1406600c0c4481c203507900350441c110188001111461081007100c0e03800d20b9021254061001c5031080c402525203100c540c4c50740320b0414080e01c00c0079101512410301c04a50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 162295215 1250 162293965 162293969
    0x20901030b0d121407020f0607030201020405060f030f01050d050a020d0c050d1b1202061c020d050f15040213050d06020403081c0c03150506091302030a0f05010f15110106 75
    0x2400e2040020590710340602201c1a030407000d0003080301200155451444c034829100c0c1a54094031003108850450104aa550071031182141159000c0101048503200d07640904000500241c201c3c3e1642400c80c3d849416101c140c0000e4003500001a029010410005035841001c0d01950001c1d034602c192300b032102c0e00d04031301d801181c3c00000a4482c135082040076030a42c040008c3c002d907001e0b4a02d880ea8000510168900f40c069800201448003100e00040950110046511200018a07180440070860184c45044801d2400845084200924050604451f43c1507901c01c5604500c2c00d400210391490401d86800b60313a0003a0070894a40c0f040108682c11200616000451641c50300c0001c001440c1310481d090700003e1550600c254520107501034080c0c03100504440355290b41d103a040070144041c9410001d41c25501003c42c4002c40c1d03400311148011406400681008114010b44c840440c050f6101030f804585402d100c000c0030498000745100d14882d004440c0703001d206a81840c0581340c0505655 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 162296465 1250 162295215 162295219
    0x309030203120405031501291603030e010b0f030d050a02030705030706050709080d021905010b0901082805060103030309020a0e01080303070f0503060a0b130b040306020903010e0d0210020901030b 86
    0x50600707061480080c0d01800032113134200c0417640c40900030721740380172680c8081c42051103103075849000300c90203c062007294003d1641e00c1d04c0c0900342038040d45170a120b40c01001e81900801d544011640e018030080c01145441102683d10a0840c00c9070404240d80e05450140c0f03d00700034010034a901c85034402e000b2102000d130840110b98590642d4142040140070a807480c5000c100d0b02c4100143d400c1020070f00403c6000e803a0003800c8466656002d04001801c004811116035584031043c00c0180d80c0c1401c002d0207404030070001c05100c540e000001480d0a4040a40c8500c0b0b0059840755000902c00500e9030305490380b40c60b001c14004070a2001c81c0c45080c1d2608002c041c03100c0b000000c1445007000010350f1085440e81e8076500250107150003900c040c4029925203420000058050003190500030003042801c0c0000c155440b80c40d561a000142038009400480c2d01d9070300000e0b0280a80b4090040c010001c072200041c081142c01c1d000081d685101a003141e100054001c16404504c0c2c1c001e501141070700c180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 162297715 1250 162296465 162296473
    0x2030405060f0d0c0206130b060a0e07082d01090b0a0515070308070504060f08040c08011107020f010f0f0804050a020405070201020702130c0507030309080c120d0b0907090e040309030203 82
    0x801555480b143e04000c03142c0d05182e1500660394035041c40000c003140206100002c004014860303032514110058020102500800900300028800001400e1103208040e1a964111542040c0b01c11a150541c181491030310302d0301c5d02c0d0341d54090644242e002d9044843c489000140c500f000800300304d1001c0250701040c0d0004007507600d050b000da950030042a08910075a2410025911141c0076142805540152800103011441c03040c1064000d8282e20b8100340501b0007809459500c9009a00355400314070340c5004044041413190850070405c00c1c43d0722044c0c003424008040040d400e4020200429500031204210304800172a092000c2841003000c0b05402820610091402440203800b039480f109040740070300c0308240341c035203e070a207403180004010440d40c0c1e01d850050613481c00c6000d01125030050398510b5042042c0c11052004000c001d4004e803210800a49515203012900d0484072031b000c0041c0214103200c200a0900d500605030f2040d604c0703110010515880b01d0034200d0700408a13405c029090f102d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 162298965 1250 162297715 162297727
    0x12040f1719080c060a02040b03191506021b03060103050319050706230a0e0c0114121509010f051c05030702130e010c031e051b03070c0b090102031b09010203040506 72
    0x2450000808501c104102201c10315241c440017070049208030312480c01281418404198801c9000511020924005101046029050303941507013026250b8003207400b5a02102908504c1c0c100100070b80c000300c0c02180070305042c0d0f01d0740e04c03000e440f84124134102da800032000300144100c03400b400c16560070a4104c001041405c00700ca80140304201e856442d140c0b4499500002803540030907014110300c404560014119280310ba500540f03801110b03691001c00b8400c24004802c180c0c0001d1130382480b030854180c07401a0100e1242c20700c2642c81044e00300c0021080398203018009921950f18030743c0102c954070440e030103500e240d0410034118001c0d240021761052028001d05148a000e4000003207804c0c0880080009000c1c0140540c1103812001c52122810611480041c0d6030078075511242d403150b82c8401d45c1d1a161031030b8848038207560080b6804000714103034400076014080207101a6a02c40440d00c02103186050440000c2d8035291421403103002000e0011344c000c81648288143d42c000d103009054143c580c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 162300215 1250 162298965 162298973
    0xe060111030418060504020a0c061104120605060405060607050705010c15020c06090c03010c0c080f040f032a08030304060903120213030213110f090f090f0912040f1719 74
    0x841c00002c2c030b90f1000c0c04c01d82c0101302c82c5082d1007141c1c003000071620b9003440c0c03041a544240203011040d00c5072601d00801d0100041c6194012400030341d952007150009085e14020080000729007000d480240031b03e40c00d0120800044000510a00740d9509082000741042685042e031480f1b44001c4070014090300100e04542c0d000e0300054105c1c0101540020f4801400010040c142241c1c2e002c000000016044041da6022600510042070407240355500c503841e1603110750542582180c981d004603050f806540c42001050902c0204543e510507019801c50034601d840c4146036240030162000d49615038802c22282014050f009144000c0d00303101055450341510b034800a207404951005034001c40c0c105420824138070140c41242000d0901a000504060000501d01c1c803a030030000c05141c10100d85e20041d40c1da40c0c3c4d0a0307030305481040b071511012840e00d840340717030b69003044444800d0501981040c4410308c0500495101002039907144980a000d02c2081c0803018900703403507002e0701c81031060300131071030b0041c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 162301465 1250 162300215 162300239
    0x60618130e0d02060703021905070218040f170901050a0f020a02030f0d02210a05070c271407020c01030c1803050a0b0702061504090602130f0503010b0402130e0601110304 75
    0x1024594080d00c0196881c242d007074040e0301c46d1030007064008c110000702c04092805031014100d41c6001800c201513400342d0380c50928003080c0944041d01c62200c00a224401c0180c9442980c0720464048012400d01942c5000a005801007002450070322152804441c030080c402c000700b0f461590018211055080c002c0d99542d02c400c1d0880e4044014001d11102440401d80052240940da1030480c0d10743c6408001c0c41c00322400c0d00404021548007801d071400041000c002440c81500b5501c0b000450446255051404119a014019032117983c9020b8104004144c001c81c0c035030360214003820089001e07a0003040441d541103d1a2880d8581c0c4401400401408800035175000c14502c20340d07860070545c80d410741c141d030707114022030307018096416490350840ca50802e07401c101011445001f01609122281001d0407006a01c2d800810310980c00c0041002145001d014030101220107a1b01145020b100c05c400c981d001308540241c024078110b06c004260140d10032804610382c8100201613036140c6850700d40070100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 162302715 1250 162301465 162301483
    0x2030d03020a031a0d0f140105010b1c0e0601030602030a0902180901060f0b030133020a020316180b01140d09022403150102030903030a020303100608060618130e 71
    0x107880d01c0c10031300785681c510880e03800e0100300030b001105182d0180d5800341a42500b0000f02d401c0101443e88403403903002401a240030345420100503403906448a07a20a511220882c0d80100904181901d0419880450401d0640ba0003030000350742c9681e0021000050f1010040c000e4001c00030040d0759096500c00c400d424058000c61000384907a0346e88150032080383e076950141034a0940b0070401002400380002e41c040072800c0d1418110740442c0c5844036802c42c00100c4a000001d43c100d81451421031a0600c444035800440350200d42010b03003001e041c420600c0610030844101c40c0d41d42c0d0000746680c01071101c505490b0346046501d94400c0a8007420000d080c096104901588280301e142c00b8050042c000986039142040361f0703034150780d210134408841da040c1500c21815030108000b081c0341032302c0034030062803401e12a030010b40e581d01703200180d2078040310950301050410a03a201030000c02d41d128011140b103201c24414040c0ba4412440018400c0310310204180146481c0200c0c2c03070076295000c500802 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 162303965 1250 162302715 162302717
    0xc0a08030406051b040b0a030b1c0b09060c04051c0618050f07030b040f02040b09010f140409030906050309031c050f0603060705160f1506050901060c03050a05090d02030d03020a 78
    0x30b90310b80ca4000c2031400c116010740c10400005000038007080710006d01070881c0c1c051a28002ca007110120011071010301c40000038200d10020343e01e501042c414102c860b90381002c0c4076001460310340f500f240c0c02c5445000320701600c0d2098825500d405040044402528901a0014010404044680032030390f0660480301d02103521340a000c12400000c013002ca0b242c0112500200a81003076551a070310102001c481c45012a44140c2d01d01c002a03082d110b500300c10703000c0e0107420f5440201c0c0d402c226001c8207120007440100d1045081074800c0f0002030344000c41c0011103606050207900e070b484882c619421400b4000e4510007082903100100d2800c00070707811107401686c0c0c40540380d82545031001072540310b06c8225101c801055041001810300614080032a11050280c0140356440320241d80e41000f43c40d20702141c5041355242c1c034041c40a4540b4908441c018a1503040140074062140c0d03025246004600c141c10900034086041c45460f181d0094801e41c02d0380c01400d49503800c000c020080e00035041011080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 162305215 1250 162303965 162303971
    0x6050109061d060303031b161112060108250b030403030207020901090b090c03060a0305190c12050a060f090f0c0602100e0c0603040201050c070306090b0f010e0a05060102030c0a08030406 82
    0x8110211025519802100b0207406141b8580c2ca0801c121044000c4040b4409510000c000341e40d0517420745864104038074403441103101420888810031200ea100c3c420141c080d80c0180300100700e80280041c1d000e001d14200102c0030b410849584d0035280c41121640617141e602d4000007004109030b41680204140e0f482103903201c40b5a41c0351032a027070885107500301103034206c6801c00100f040e4500c40b0020f035a07c42002062115069265501c80d800c01f12104026280785c4c1a10040608100081e4604400742c130110040304040880c0342c548036034a40c01058054280c5070b0f038100b107600c01c440d9600a28070319504481e000c14040039910b098691584a40f10300e800600441544101c55106409040003014280f03000302601c115180802c202580090012418000d041140c82c0400c403003840304200540c0a4030300022107180c00d04200b50b01c148010b0851080c0121b1034018410040404d1100d90000d44003031002840ea51074000607451403042c0306001190780b28000d0300c04100102440150304c02c1e485402c040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 162306465 1250 162305215 162305249
    0x80304050a230411090a090e0d02210c0715050a09060206070e062109101103040317070207050603010807180605010c120302160605071107150e040204030605010906 72
    0x150039034004140303201c10040b070180e003240c2d424905034100710101c06001800034a410f00080000e500000542d0085100c0364aa441c025907240c410701210440700d480740060403c1c5002c030601c07034440c8008010541ca000602144001c5100c100708003c002805194000c43e032245c0d00302c50b0140090704000400f00008006000200302544007003800383c050501a1035071905481c2071401c100890b0850f40800b0a0366000320604403102c1d0b03036209164001c0c900c0c5806030680440040345a030648419221080d800c200400034040020b510042c110420030422001c0c0c01c1640725400c00320f0500b030840c0e106c280d1004c80400046046800850b0790422110340a9801904104001c0400143c03039a5108903404075503509694008984c0c84040c198800750b1514006160900c00c41c0f0700c42d00c83e0080f1409a420f80c0c1e5650403c40c4c80c5401206441122881758000c0c15464500340c00e055401f0300c450035403410009410264107454840350165809583e02c00c00a208a42c1c690304088000c200b24400d100441c0041044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 162307715 1250 162306465 162306479
    0x810020306030c010c03080106050d020c0304150809120301030b0601030b0d060f180c1509030f0308070e010c1101230304060b10360e090a0b0a0c0c020409030c0c080304050a 76
    0x40c0403103655147d101c0100c541e10b0300c1000e80b4680c11005d060311045408205000420310148000e20141c0340654151801c050404030007081c1c1c2c0c00c02421044a03070b002c003440702c003c07102007000d9030704499110540c40c02640d100e0004a02601d00489050740007a01c9035048000c1280c0c6400951100c0c014000420850481046515400b19040d0b000703010750301581803e2215980003080c608070315400303052410300c442d680d80d81e5924151030044158000340110052104081e8008070900101d00c0174600442003000903214207502031641c1c0d400c603040c0542101c810f100080c02d4440540c41e04901c10340e1584902e494180316015003540703100b540c4212010160f824500740034164100703d1a95242c06040005d0b0440785c5245182490324280e40f8800c0600b800190348250300850758403a84416000d094549500d141840c05000003810091050303003410500120700e43c3c0074580c81e4040d81c0490700414015042e00702500c4008612401501c000b03c030100100e4404d400100a0049800c25581c0d0003441d580d07044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 162308965 1250 162307715 162307727
    0x402030f0a0c1b02120f0607020102180603010303021c02010f021206030c15120601020a060f1b020309100302090411030f01030308060925090902040909060e010903020a0f0602040810020306030c01 86
    0x341c03480c40054141040000b500306407505c40e04a4155204545082414940a900c0c2131011504400142e400081e0a17400500f452151742c29804103851640c00c42d411903034040c1d103030440700903481d00a990710806070207401c0c0300b50411310509031082c008655401d0b5095000c50611401c8030305601a02c507010110840307040003009070f03e440c914640c1181c10f01c41000d001e0441800054003190440c0300d0340c00c40d8404900c0e80d2245104c5082a0040040c804210a40c8240c0a4403c001e20105541090085003000e4882001d4130001c4500c61800580d1009103c0002e40241031072a0b1405800f03002104006004c1500c5c5041c42c1624002e4a41107060f590304410400152000c070b0f404004081104500c0820100c02124a010204503050078010581c40309603040c203c1c0c1055005214441e16842010f041c45643d02c9a4010200e4400003846040d6450f01c1c0699030f0301c7c40c641d009241c1160346d02e9180902403140c0c1034801501804060b0b52610720898800d42c0603410075508142300c0c3c050502080b10543c0211 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 162310215 1250 162308965 162308987
    0x10518040f06090503030c0c010b0114030a0c021c0908060c0c12030a0e010c02011a0306010f0509100803030a0501052806120209090c0309070e070219030306050402030f0a0c 76
    0x1a1414446030348036514849501d5500c04101e4400340ca500410700044d40c107201852040502200090f01c4d0307040381d00d60b1400d541035410b04a05100440b201c00d03441c000c3c2030003200d40c030842440f004241c808c00701d01e0407458801281c0d11038030000322884058100540c003400ea00308039680384003280c0d47c5459030b50000d4400d10480c1c42c02240342c1d0001c11107800103010140616807200c6400c8000498101c0c4041040c00e662100040e0401030359107540002c510803c618544020000541c0149000e40c1042c8001041520b58001c60703110307650040c005048510260748600140005c5810baa8907070030160b6800015003001e0184910461821015aa40304a200e14802601d800c0b0219520500e10344541917400004d9074503044103483e000c100b175600c503894002d07070030b80118100e0496a65a10f07101d9003981c189520b0f90000000348214806000400790b000521125030f01242d440018403210900d802c0d802028a940101d80190000c01000740107035485c003250344030311080c0500f485440c2d000c01c8100c3c2c1c10001c2c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 162311465 1250 162310215 162310249
    0x206090c090a140411091f0e06031e060907051c0204050709050409030203030405060907060f26070f2007061b06060e0403091505073005040303080105 66
    0x20901106890700c00e88590704410700442c002241d516103400001d0841d011a002c5d50601c1c1d200158490508003114200d901c00300c0d1401c010505010441c5032080c4142600c15942c0d000c3e440c001103400d42d6400e10030440c448031414005851001d0200f500342d2070300380440c0c001d00e8070701652500098500307100a9102c0307000b91074052a50541400e03400c02c0000d24029088008101000758041456100d81c410750f49014007a800a58072032409203403051500c1802046111745401c0003004109180d0850307000310007684281041c040c02c0c01d0305130b441c40c114203841010350946040e64041c0030006400c405000b20490183e43c90304070380d10a0b02164100550294a583c0c826070040341e081000a104111002000c00c40201194a10401751100c00640d5090340006070700640b60811f1200b00b60300174003e4001000180484003540804000240c80c600408101401e1500042004c06140300140302040c0c030441039085010b80b03042c078090010146d40243c0002c4000c513030300d04008262442c00d403001e81040211 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 162312715 1250 162311465 162311473
    0x160608010e040b1b0f09040609020403050601051203090303040f1412070501030e03040e040b1f030b010308090f0406182a030903110307061a01050304050a020105160b0c07050706020609 81
    0x580e40c402c1d94a140061680320040003030041d614507100d884006011998171051880d8641c1c0c410010401261a10b5028080c0030b841003204200280f0003050060441d50304846080940e841001c1190640c03040c00d17a1954540400680070640d403220010120a940101d4505110411241c0c00d114544a00e8461400c0c0d96121500c100041d40c07080d0060003c2c81802010b403800c166035070901d040c1c200303001d4804032031505280c800c001042d4074a501075140e0ba01320501000d481e81c0b450702c45020003181800050600b0b40c0006480c049902e5080b0b60190000c0064810041369540382c101044501248000e4655503041090450f0480d0149111907107005002e41e030140c542c0b4601e1401e03001001c0509044080c0306101d03503070084a070401e0000d40321443c0148070108141451040082480002d880b0080c1030140610600022600002c0c060302c48980c20300b011a55281004e4a400d03504540f51801040e000b80d00c070030000e015141c840a080500c0c0b1032011541090703114a400d0b45c0301c1c032040b00c0031106544 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 162313965 1250 162312715 162312721
    0x614010f021011220e06010f080103020d0f05030313021306030c051003150f05100302030705180a0b0a021501080708061311120307030e060a05090d140a05160608010e 73
    0x1c10740c2e0140c000c000c10095424600040140d07500011540007400801006a134001044030700d602410141d8004c10910b441c0f101d240c7c05c4503015003401018000680a4844c1203410810071070203034550071808c1d4021040304d8a0349031000d00c00380c0c8a070702440100e0003600a04440480c001142c042c0b442642d1b840485c0808040c00c1000348480c0c010040301920415440d40040200141913a040c075024080c03000381c00c0f0030307a0b04000030300c400d1086500c4041c08042c410010043d03916440310581c2c106407568512020810114400108400c00d40e8001800d580c500103000002d0b185c00085482c022400c41002190581ea40d40070700f031311104181b084109941207200010846c40b40c0c101305043c03262080320440c42640e50030021070411004e1042034400d5520004902017455084140f80c0b0341072200b114014a402549000282940100700606004442c1a4004400c001d4a00c1c004e43c40040c2020880d502921942090790303480821504025035540503d9020031807501c12442c6034181c8840300b6491000e52 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 162315215 1250 162313965 162313993
    0x3110c030909060d21020c031b0607050f01060f030314030108190602070b0c0702040f0c0e0f030f03130f09020a0c02010518030d0503090d0309020f06030c1b010614010f02 75
    0x10710040182d948000c8031024500050881c00030700c80c410705039400c05d0702203149912000e45007100768407989120340c1c010b52141d98040c108400441ca450b0051b181c0c540c8580035840c010b86460301503161040036509201012a83c0a4011990710880380607a5a403c0d8082d4110a10801403100703004101c4160040d2030041a005041d1054600d1984107050052500a46403074500c0200b5041e00c0c1c040260783c0010341c002c1549014000d01c5416042c01e6801c0290890480001e410300100c1c2c00703510701502e14241c4004035980c0602090401040f01800d40b940c0e03000008000805000360b000b070510071613001d507010466069900c240c95a001150b111004601c0c420340055402c0d805ca940360b0800d0303403444449040540c40600038500350720f919031038540e00d03400d043d030f0854113000038807000d4400c25182410325000341e0740d040e588003481e80d8152042030385c0380c9410308600500c3c458640c00421050300714601f83c20580055004408445260030100040140e100045901d002140190310060b441107400340140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 162316465 1250 162315215 162315229
    0x71121031f0807060816050909040b060102010212010f03120906050304080f0415080a050a1109042a0203040501121404060507031d070e090f0607110313080a020103110c0309 76
    0x400344100107052425900ca08a6282c40300c00d030461000540010f0030b0044044c0365014003e00005603060490418010b5004207561079001403000e042c0800c828080340c0d0590003903044a80c46240c05030340b0710b19903840e01c41480d10000740c1d1108481358000f81049101c1a0310540c4014262078242d6521891605c9a403036501d2540c1100b00051403564041000055054000444d000c0c0c9156a44496280e850300703221807812980020507441703400d401e204850101c1003a15040311044a0201d40008a0400b2509000d40901002003030000840700081601c0c9240e80020107030040340c000742e0314440c04610040c00c040c00c5c1c5e071300e0407000842001e05002060024045401c8654003050928000481c1e04d1342c004940b14205500141d944260071005c010b1203500c2104540c1680f16101e00018030f00c44241c100311075500c1400424003000c0158000f0071102410091084030859800041000940f640325980d031500d454050310100e0100b440d080d2404414030b002c03400d82e060220618095030804051200344040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 162317715 1250 162316465 162316501
    0x18020426070504050403020c040e010e070303030203090106170f0d0207061418060f04030b0c0301050607030503040309030210111605030304060e01030902130209030d030e0c042307112103 82
    0x420700031180041256100e5119062156000398000c0c081d4a00050030301041302c03010f07105040d150741086509581e03004000b4210301200d43c1440c0059580c1d843c1405a4010f0010303822418080c04c64440e6606151800550320b0f0106d17a292042d034459640c0a001a81c1d5241c083c4078140124103008807286007010101d014000c543c0318202440403a082000009000350b00c191050041ca1002050600130b00947c3d107107995014018000d154610350601c000140c107400b5462008081260000c0000d04040c41072807200d0081d40e01030050f400d105407004016260501301480180a84282105081a0100c462002c0204c86000d805103180c141050f10481c0d0302000c1e191020705150f1120810340040c3c4a80565100b0b00440c51070042e00ea40e0008209820000d5900c080002c060500a04030200f0b840400c210824140869002500100003076075000d2005040d4101c094600b03030382d020445119088884c60890b100c02c1019259512040040443d28900350154010804400d01c00100b10710840c0c42c003950 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 162318965 1250 162317715 162317789
    0xe0408030601050c0706030510050108220206040906060f030b01021606110118060207140d210e1501050a1d01031218080c010201181505150a03030207180204 69
    0x701c4d10a240016502d4041203a02050019a9401c2000580804c45484001500c000d180500f4142401601413200140000900d1080b680250340c2c001150303102c40880d0f0051003405828001c813951100c001c0c0400b4008906840401d042020501c0158404204d01c0400304451003611080c50410744103c501c07440c1c0d500110400c2d075907604031644050403800c64005c07081c03040802503030b500318501c0d000d4050005119202c010394001d0f940b1150300c80d00305140c1a15062102892610705022440844c080e0500602e85882c500070465004004000e4103d483e040e02e4059a000b000c0c030303555075054840c154030118256080b8000c0350040c00080d02885d840e04085220303146c00f00542d540d1803500f80040311b02da072041803503501c0100103101c103580a0148a00300c45074a41d010f03a0b4a00036403101c06141d0342510311403120aa03500c0020380e035005582c4040c4484180034141450980d16440c019517603844034041c0308100340595002c419106894001c0b54203480100340d8140504003808050401c0718190380c4005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 162320215 1250 162318965 162318967
    0xa0504021f2f0d0f050d0e0a2003061005010f0509120f060403030612030915120f0c0201050c070804120f060f0204061101090c051e0406060507030f0206010e040803060105 75
    0x109007104040100c5440e0354181461007003940351a8000f0700c0c1504406418061103081d40d60112050380003819125a619034420204030b04028121140c01e2841d03501005103101340c1a0500d085000320705680c00b061003800d9040320b81613100c40c04101c9480705540309450020314900d007000c2402c0c0c07003180600800b0a0192101101d48041c10709181401d03a01403040c200e6500c20400c00090540c0f5004040c0104080c103031803aa0806181c40090080e800f0380514081d09140c00089a0b003244601e800e10050a0300040c200020502d0800703081c050211003448100560030f05000c110b4112111046079201a032002040d417800d840c00314102e4407a00289002e40e007010504240e9008200c01d0b000e0090100640b1800503901c9003046805801d00d919a5850f841710303072600c1d000000160349028070340c00f916800c80d00e10705240a805103074140c031841504955040780c100b5600142c841e40040c042c0c210b252080c1c9407112007007901c84c0c00b2650b40c2c40900c180e103031004441c000302e00481c01001c0219000001031405e9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 162321465 1250 162320215 162320237
    0x50f0a141e0907020609101a0d05031e04080d05131505040801020a030c090602060f04030806030a141612052107080a080106080901090812060d020d060b090a0504021f 73
    0xaa0b01c80022600c2102607007202c000c11030131007014024180080244902005803d83d03150203049111640c544050244401490341401d00c0410825034208030001e01038058000ca0760f246403483c9400074465200c003032003006001c03030b0141e0041d001d42d0f5201c2c030410a0200704515141c005c003030001417903c4003400c1c445c0401020442150a000030300e060703c80741d100400c4100307448034020030140d070766442041150006400d004802c000302c00b02d07a410941601c0c0c8840c080d283d071400030742021040000242407148001c0750050207071001c00c1c0782d0700700c2500c1303d04181000e6950700307050304111001e10300614171b4120180a4040c024052807505c000345514840c41d007000e0300380e51040141c1d841020400b0114500000402505034460011030380001182c1c024000f2500c0e580e1385007514050301e0621030404204600040341034a585141c0804941c00501804080c651030400b4001842410f0006024100050028645d05d00c90b0050724000d03540540200440c81301416042c800f41003290707001082011070264 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 162322715 1250 162321465 162321469
    0x3020421140303071710050603040303090314040609090e010b13020307030603080d050a060b09030316051006230109050d02060a140310060201051e0601080c13060306050f0a141e 78
    0x145101d1320840d250000c4110800c0d404e030b24503100c01450f12004642ea01014485500d4020503650015410304010880000ca464140c5000031800c0c2200d05100021400240c4035074000000011039042c00c00401c002c1d281601d0842c26107010882d2181c0003452203495100307a03601e65009540c000c115141c0050850b032280d0361164185e100048425541d0313221303030500010703a403644200c3d80140f2a021580b89410310040c040f86c3c80e80125009224005102c0403000f0074484203010010942d541150200400c50315401c01c0300f02c0d201042d0076800011018030041d44194043d1484a00703aa03402071110011603815400c001055101c80542010883d080110f01d15418840014501174041c5485568405040c124000d0844400503e580c0f2000141206041400310100846400907400c2ca407e07200c0e0350f611030140b02c0504c01c1c1d4400d012034010002002490039415030140f8141d4008941c010500903514007040114607090080e80c3c0d40218003882003400d8a0504102c40f0190000d00701039010610b1580 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 162323965 1250 162322715 162322717
    0x40314040603140603281a0702010203041703100e0c0904060311150301031101050313150b010e0d050d051b06090a1b0e0103030c03050d18030f030204211403 69
    0x100c04000b0030744604880301d255424a0300d1540c4040c00750001c1500c1406180c190306a568040303080d848034054810424140070482170080098001031841c9001804c006070f000307000b940100e40c241c0e10a6004650704030396149080c00c8034003c0c0296281d516000d410601003104001001e004c0e4075540404010300c1056444500413200110300541ca403044085905c0140300074a2060101000410f100300018000075078007115280380c5800070319141d9284d07034600e207a22a4001c0e00000c05000e1110360500030440c90016081020600404c1c1c0c0c1e40c0300b500d01e0900a01c042060320240c02001c581181e202460348038810070190003807185801854149250720303685513040000c241c424074096040450341c0424424201152010505507400041302396140c24084a03e802042c000142041800304c103980c285032082e030982c1c458500340041040714682c00300241e840140c88072030807070102c0d18011490101500074400d4030100c500010382081503985403030542d54040d42c0301c0e000b2658100341c66840094824200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 162325215 1250 162323965 162323969
    0x2191a090a170a03030c020a0816030513080105090c060c2a060d060503122812020c031b010c200703050f031c020301120b1306110912070501050a050304031404 70
    0x902a2240310100d080c001c043d21b0494030348800355801003000c800014020380850322a400c0d2038203c41403010080c94203d60350b00c174940d00101503211040012a12807010351040c0c0c001d0140a0880d1002c01030308062004902488190283d140c00c11541003201c0c048260305020a14001c01c00103038030703154030b600003401c54008000050301d6a9640700184100d00317041000002000c4a03051803424898020f681501e15030841e9544180300f00c00c03404d070914240c080d100110b401c0f0a048815501c8030007141e54160340b40c0002613085940304103203118103201e40040c410b40c04c90b6040c903a00d48184494191202006e545000080b503420300c2050310000100c0d0040c469002000c0146016664480e0000c90a20021040314100410b0b00d1040004001500b40d4501c00704885a100c070b24410165183d10040100f1001540090080c0d402d00c4081c00c4000c1424004245000c4100d5518450800c500241503607102280200340c0410030030050010710390701503409558000d1007442c00d260500e9810100b0383c4150469 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 162326465 1250 162325215 162325259
    0x50607021027031a06090c160507060e09060405010819031404080a02030d082809060501030605011a04083403050303060a060513090b0409020d0b0402191a090a 70
    0x1070701e0140304101e1303641e540d082544050001d03116681004800110070b0480508040c14184000601038120b02d01d040001e0201c6411100356500750765243c1d8080c00c2080307480c42d00c82c4a01b89010004003146030600c079680c169040c02000340040180c03103100e000c82c0c0503441d00540a001c03109004164110710000100080d1601102074201e01e40148141460410241440e1050103000c104100e88200b51403d0bc0c1010410000400e0000da12962110001e0030152000340405003040008028803d2a810150403a8500c8080111a038080303a454003090190b40509812500700c03c20501101ca0300310150700d40a48501c00441007079100750f80941c0c00440950080f01c0359040481003142a140000880d03001380301506100e0310701042083e0250307010240303000341c410480e5038100c144282c2d199035000840c02a4041e1070f00c0034000c42c07401e204580d0481240d08034410140c0340e18a0040030007002d901d2084452880d44000d0914070640045440d410071403502c0c0d0000c24201c00018060351420356540c2010b04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 162327715 1250 162326465 162326537
    0x90405070302011101021204060213080f0606010c020f030f06090709090503030a05060a0f080a17070506060111030c1b130207030c11030a0f110915061b030c0102042303070506070210 80
    0x9104404c80bd8401c01c0c1c0c010034a58001480000400c50b01243c01584840246441414040d45100188903200d59524194060bc200365040720005c100150160240c05000c085608266a46c0d20b84400c0d1444040c0080594005001048444146800c800d0b0480b070010515031140b41c8440c1080402c041c1d5610000b2a0b40c00110941305200d21a1003510741070040134006032410000703458180d90b0300800340c0810304021118401d2a81c16000340240d42c940c01c00701083d5040a10f0b07554541c0301030441124518440c1c044400807156010780c40c800c9622a9030b05440e50751640c455902c4501d500500c0034400360b0140240c44038080058064281e40560310301c1840300941500d80c4400340100000010070002203010f000c650841d0700d43d50001a10005c40445410705e1803e20300c52807482c227502070001800d100f5070000c030380403c041e40c007111403035198040d180c2501c0228207500c0415598803079034410710340c0145c0d08000c480c0250030310b50702482511001c4d007086008100110b03a954040c00d8030701038036840000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 162328965 1250 162327715 162327727
    0xc07080a0f030f06050603010e0402010e030115061815080403120618050f07090902091306060206060316050906060904021c1a040905100504031e020102180904050703020111010212040602 82
    0x50144544803a0f07000c040010030200b4104004135006110601946840075a90f0000808682c482c158211103000c000e0024082c120409407500d040c0b4401e03000307641c04500c0c12f5501d8182c014001c0c0040080701d06401c003141c201c000e2904c0035940548080c00c140c2c10044040c1e100c070790001140c02000c000345581c145415034103420507845000c40c1c102400b26000c103031840c000d12111940c03100302c040a95100a42c0165200e42110001d4044455112945407480c20210001091a00451407511450b002c0d001e8442d41001000d440040b103241b40500da500c155150046513503418141c014110307201019000515000c000c5000c45002c5a070754110039541d07602c94003201c82110510710500014002136406000c00b128a40d129603c800020b404c201905640300c0006080c58482c041c140d141d02003403400321129150800000307021398001d503003800f0081001071042c1c1803401e0480c0842d218a4008001e800c0b0036007968011202c1011404d0b40b00103c1d0b400b4003c41e0b024080d4482c8840c0640c0c811f810040c0c0d618 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 162330215 1250 162328965 162328967
    0x50303010803040f050402090d0b06040207051b01170108061306020d0e0c0301060501090f0b0c0a02090103200f0f010f0915120e03030402060403121b030201020705060606031e0c07080a0f 82
    0x103140f41e0000f40c080d41c01805600070b23039115155401400c170b0b8400507141d502e50314500030030024010010094428414048080480f2500c03504040709168280c1c0c401d20301422511031402e000000b031150084550014002a40f103d1001e00b00b400d406118a02c058900008220800b0030396403035083c07007234464014801d00c14091030240301d034000400c800e0810001d010325001c011000d041c01351040001c2070200086424401c88188640608103500404000c2256100e0920a10140c0c800c60040d1414900100e800d9852808401c40003000c04001d00c92150026814011107440c00c0b201000014040303c0d50700450b64010040c0d0540c8500b190369514582c800004211505030b0707080760740b40c412940003002400050788034007081b5404d0705d402c15561507402c600c411080b5030222400c0c01142e041007280510104069064008002c800d004404441d81901c0d00b200700800c0b48000d80701e40f0481b020400c1180040d4901160890380200c14609160400c04030f80c8503407203980d1100e5941000204040c890341001c0d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 162331465 1250 162330215 162330239
    0x30903120f0516031b0302090319080307080c09090610020a020301110904050a02030f130f0b01060801031101020c22090506010303050a02070b070210110a020406080d0f02122505030301080304 84
    0x5225a464140403c031416585c4035040d007400c1030300c41c3c00c054001648403a0790320200b04000b0320030b40010400403454914205000990815103408000580440104110303440a80544002510080642c2050748810080090745c1030300c03182c0e400c19402102503900c0513035000e01c074242d42003454450981d981c0290300d04000468a0003032100c0c02e920b20510911039a07008010100d58488004510105800d4043c108228503030505600201500201c50010419503480382c401c504132481444030101c1101214010382c2c036880604182038000340b00368680c0405846d00d141900a0f0500a440082c4c08080d540703482c0d0810380709030006c1c0c000c160300060040000d5410007580700107150403484d0078104040d40d400501c0003408801e0300801c01159800d071015842c418480d403501c0e5540144208411342e82c908500b6111408520101f01182e2140c0b50407415500204040d441880d4101e03c0c00e1070210507240e006900c0b0040c02c59000760822a1090b10001601000214042c06d50131008503212440e111120b114 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 162332715 1250 162331465 162331501
    0x50d0b01030b09181e060f0613151719060f09020402040b09010207170c101b060e060a090206070605040f14061b270102030f0a0903050d0804080703030903120f05 71
    0x203000e002c1e80c030545c20ba0041000e0f908a220f800800c034094a070a00009c0281c010204040005031030542500c0c0184820b404c4003046030180180307407420181d4440340f0b81c8c8400d0b031036800e1a484514802c0820000d5130700c2d8842c8440000858000030858805e401007030480e041030700302428000c0000b0700007841d982c04101c0c0318002e1500050569048425801c01600c07808645885130044050407000c150301c034020004903080011070502500b01c01e6282c10700c000a003000d908040350703601900e0041011041d40303004000d4050b4026004501d0b0251aa581900a000c001d10645644100c1c5503500c00184010b801c606081000e034004100d6414014500100020107903041c0c0b08101042020308089d0401c004d00316024240c0c4034084101130904c60040c0c0c1544501c01d80e4079500000064001419500187c2d920156402441100d000315101242a20340200a48019118103400e201c1100003d10a400070910240300786801c14084200100450683c0d41c46007007401843d417154100840000741140400c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 162333965 1250 162332715 162332743
    0x15010e0106021b0a03120c0b071e0e030c1809010608010603020f04020c0703020306070917030f16080708030f0103120f1b02030723150a050d0b01030b0918 68
    0x1540340807000b942e0307480d01600344002c44070050716184507980d40b00c200100540c1c00c0104a070300c09115400c010805c0c800380c0012941403528001141e903a0780b140103000c0c00041c0c042e490f01d140540d200e005403132480f0342c070350800c0c1d0602c100c000c41455a2100030102c0c000080a811030b842c1801c0a0a90500750303040c582104aa50b85810b90801c00340c0e58560034445d5140064500507560002007550b0750408030603400180d0903200b4082400384441d4003c0046003110442e1030515003400b2040e0303002d51203100c0c404c40d0b058821403c0c03009481d0a81c0040f02c0e94030080c410302080c0e1410050f43e88081041d00200e6035035482241c10f01c0100700f80314007a010f69526821615001c1d01141a40c000070341403030b140b207440044445441d0111421034504000010140801c81c00c141d01c0d20503424481103410408604141c018a0801104400714840500f035540101c02e907102d1b1402e10f0819450000100144c4819904141c2c54034070105140c1c403500038450040340710071000c1c0d0b00010300051712071609044da44019 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 162335215 1250 162333965 162333989
    0x17071a030907140102030a05030901180308061014040902030c12010306061805040201080408130b070602070215030c0d0b04110c06040c0b040503030301051e03030a02060103020f0904051903030608030c1501 90
    0x2200c0e0707a17010041710207030203003030500c16100d85610001500514100d0142800c07402000011001d02d6000344c841071240b403049445014124a07154111110340b00c826103d440e00b5004d02c02484a00410340181d90302c141c0425800d402c045401d0480d0304d40400030383c07080d075625580310014818900340780030030700d51458000b00610890415a00007441c4510040000e000042d0108055403c81c0030f510041d00202a022485519084107027803020081d841210300700e100700a0301c0132421400201c1c00541e8400d1040d000c91900b444882c9968174050100d030038965500603940e001003054401744202901090792005d00a11840c80d140c0b42c0042d0900d104d1704044610302c810702c4104001c1e900042240c2c1036420a03203950680012580c0410b120340c102a00d0213525000104ea0b80d800e180e4000740550403a07000300d485141c0000301c2c409104a050b001e80c1e01034501d4004420101110321441a410321a034820f14000980c070b40d807210010305607003240702c0a44554014514400f10f41c0e4216215502600c44440c402c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 162336465 1250 162335215 162335249
    0x6010e06270403031a0d060903030e010c08010509090a0302060a09030c0206040e1e10091e0e0a11040903050403030309020112060602010b040b030309061e1204030905040c0c05060117071a030907 85
    0x80b81034080002c000c07c019181e0305240d042502c81d1b082207496071410802845010b5110502400044003401041d0041c52450b002402c102000169085025056005040380351111020100a40903e46046d003c0c015240b41140044e110070703000b4402007041054005550070244212030000074203200c81d031044030382c0d1400e226141c04d40410340740c1161004800011070300310031140001440d0600000b41c191900d0300d1940301f81c0020100d008808648034826854070090700700204811203901c2074024001a000344428800a03000780c5c46080c0190050400c50a0f0071861013685095408580050006035100e049117039090a190188030340c443c400310095400d0445400104610b8041c1c1540050300655045151040e0985801180e10801c405200c200c1d040c0b50504002d401c002461003807031700451400c19050350319171050340703075412103517021001d0042c41e4030301180195400313410038034090b19004601c0006a000c031400500e4103040c6004031519180e107400390409040c010150710078050460b8036100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 162337715 1250 162336465 162336469
    0xd08070206070518060706060f060201110403150e1c030b03070302030a1106070501020a0203031506070f06020307030b09100302190602190f0b04051b0d020306010e06270403031a 78
    0x10594003080c546401d80c0c465036201c242135800d09031050401e0b08018002000f03400d10034103030030020075a00c0b000e2456104641e82c400032030032a55400c00c480705002d414401400003540c000d20040c40d40c54844000f140d60168840d0290030408440610a13034251512814101e05070103000d5144400002c4014010b601d1464006c00d442d80d054102c02807050000307050101c8079a03280310030f94240301e030020000c5440d8417840c00081e6803580305a80350140c50010f00060b0200d464001c00f02c580940e4080450100000e03580d43d40d0004c1e4002812070b0045c151035200c00b441d1921804401c46c411092040c1c0c00c0c0c112031440c01801801c2200680b440c80304403220f103050240c5900010b621694004600301c0e404510350b1410500d060558808000f000104040c0601c0140000007584448810505c0c1c10000101c40030000c002d0703121070045c0c00a405400c407000402000c0c17080180c6a500c074001402c00c0703029011856403000c140c80d4034824101d00d402402e06200a1603414410080b60300c5600020910004203100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 162338965 1250 162337715 162337723
    0x41e2414060715090803070306030b01050d020102030715021b0a12050a0804110d020d1a0a02090d0f0f021008160801300507080304051f0503180309090103080307020d080702 76
    0x120140030030094810f00c640580d141d904c00308134503402500d01526400d10490003005000750340300542d00c0c07000e100000324540c030b0300318005400241d058005518003000e039640e050521418403e00484190b090001400c1240c402d603548d80c80074089c901405003502d0501e49250070300b03c140109010040300303201154005422009070307604950485c0140d107542100800041a00d07410390b03c02904041e8140103e000c2240108800c0b415900042a240180e070b2419021000c9006106189502664035030307525001c582505052a4254096011084540300c0d58010644a900242c40180000c0c030310010811089001d00543c0c102113500e18122134107514085484c26040707905540c003a0b2620b042d02c008a640080b01201840d0543c1c040150b460f041c1c0c3c0c4820b010b4480c0c000d44511030141e82802d12a000c41da4100010440d12407041d1030705070442d203e00c04056400c42c000b01c0d81140900c070800c0014195510b0800e424000c40c480c04100c0d6503854114402070902c0c003104c414606010b001000e000780e4540102e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 162340215 1250 162338965 162338977
    0x130617040f0f14030f090f031609110f0403030923090a24030605060a0e0c04060305040305040f0e0103020a0b0c0c10090e090d02010518060105041e241406 68
    0x141c800032800400f810003240042603143c612a081c4800940711881d403156030040c10a13907608a45103480902d50a090580b960280369400d040041141d0041c00709070100e030f01c07550803101c913001d0304d50815140321002e03032455000e6007040c3c011071319084040003141504000ca940d200f032101c8861980503000d102040c42032101900c0019215260200c4014802c108402001402c40310080303602c259550781000001000c096135042c1c06411a01c10100380c01c6503441000340100044500c0b0362a291074444120024070014004504100080100007030551100316010007800900065000c1ca514600c10844602c20950001d43e1150041c031404882d840041030100b1404170690310960240074000c01140d030024175822800701c1d40003075001c0c8002d00310009081000c046481c1c00070000d0752103409030104c0c0d410102c1000ca150781d1040c801440305083c5508a0164407689500d80f80413010060024020341d1079518800342c075001ca051164181040f0442094014800c000c0900021011540840e846104007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 162341465 1250 162340215 162340223
    0x11e08070e04020714060630070308070b25020604020d0204060503070b0403060b0102010209030706230a030b01020d11100e15090d0e0306010e0a0f0e03130617040f 72
    0x1900004100e140144414441510010401c542e503420030b00d089080e4010b80c0d240742c6454800c201c006049810000403403204541205450050b00201c1c07110900d9802c4860001401c5000d46180000000c12800c09410006e10444481d03440c2d10f050032484540e41d00700341b0b131b20515800c0c21444c1048640c0105a55800c950142c03034103262240c1500104000d8825688600d415105140c030005001d01c24402800550748a440300307001218a04004a00b0303030141604203607041d0042403040080c14018245407440c81c20040a55680b440000300507a11070b001285c0c1d400100c2e445410780388156905004014490304241880b601856100f00d82581d40d00000200791001603643c80d034481c940908000d8070500c4a60340c90b00c000e0300d1a200e41d2154071003803080d0304180454684036031010345180200305541030321440c000d490010b9407500a0303840a004c96800c003542e07180c0e8803030014405510500040c1200030341f204072a4805480c19100800700700070880008060034030391040c080040c0c4103501e2a400d090700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 162342715 1250 162341465 162341477
    0x91507050609030405100302181c020301050105151c0e190b060306010305030313030c02030d090e0a1a060306060702041d0d090b03070c03121802040b03060f040b10050627011e 77
    0x7540703021030709e2240b04020035920400c11552044040010f100081c403151080c0e0081c002a60b94000781302c10b4000f04c0750070310301c3e01c00280f007020700c20b850b0301d80d0b04072a42c7e0800303001040b8a810119080d0030002e490009820b008141183c00d42800502d6011030f070052750075401442d140d032540d11406d0300d03808080c00d82c9000e0070001100d03c060601c1500402c1e14207400500340c481c100a001c4000c0c083c5203041c484c0500c1c000b001c100140c1c0c1c826007482a0399030b00190000b5000002d401c0020004075a0009210302e070300060a026100250711103200300300d50103003e42504142201d00341d81962500c0710703110803079081140d0100180045003511050340d40005a42c00c000c0303d811104e1a040e030304241c1c015070b148203030303031400d8028000c60000d0022410058000d503420840e5048400515807203240c1107031107a0009a03a84081400210301e401019031251401d40c0d805e010980b0742000031120b030302103802340b8400c84855000f81656034080c0554003200900b401d02e04034202c00c0d00d41c072040840d8000202c5060040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 162343965 1250 162342715 162342727
    0xd140108030901080115180e060a051c0f0c1805040201030b061806090a0e09060a0606080103051b060c031c06080a0b0a0c030f0f1d0d0504120503091507050609030405100302 76
    0x100407041031403982841d0b00340b2a2000c3c0ca423020b064200b1000c4400510036005400001114244820300c52907801078448034400358403581e02c609000d45030403402220b0600840c40c1c00200181c1580c55456030080c01a0082a2401c05000040a0340d074000092071140c2c6081003228054000440c242c107007240150341241c0c841094500050320340c0c016601180d00c440f008420840c07102c00101d01c992081211480c2000200d0b103940b0704403001c00007400004c201e43c0c8601c20b40740c079581c415898134103518001840c042c80d001d01c080380035003545c12100f8809661000c402242100000c14001c00c80034190000003040307607103c591280d0312889405400460b1255690790301804c014480e810880b240f5200c0c11040c002d142c0000001402041c80301c900c000003103d000121120a103000c00d84105106040e40c8090a10b0300f0841031480c21503803104101c03001d10040002d81c40c0c0340c455071050720440d01d600701d081c0d4031204c203828035030b042200c001c1101019030400c2005010654136044209a02e201a284c010f803150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 162345215 1250 162343965 162343967
    0x8060f091305150108070e010b04120507030c0b0403110f060906030703090b040f02011e02030d02090406081615022407200102040f0603091104090503040b0d140108030901080115 78
    0x1ca0045406841c034021480d200045024031048141210560f508494a807a036034545403a61400a00402c0420134080108100030141c2e400141189801038050f02c0e81641d69955004988146511040d840300700131a003001440071210002e000c001040e01c00d00b0082c800304000800511031401841e10401002c40440c40c140d100360b000d60303006680078108400070b040034202040c08001c0004124000782250070001502d0034880200c80701c1311055001542041026469440650013201504e80c005d5955603001500e481e04004010840c96144101501031741404c6981c01d075075507003040100c103540c04234849802500c900c08121241c12060b009013a407607251250100c40c1d00103840e42100c501200c807003095059501c19401041141e00c070344085040e259540400340c00307840702500043d140c02004c4d885110320b41415089810140e2161054070303d0581c41d607920303540c19084552210201c40c0d480046e01750400c1c10808080c09090980000c504110b60540020310740f480501540003804581c4203600141 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 162346465 1250 162345215 162345241
    0x301030f0f29090d02120c121903060807080a0b062d100905180c04050a06020f0111040b1608091005030a050c090619020c0604031101030b0108060f09 66
    0x240c0e0b02c140d030880c0e80c1c80407404110050042d91041c0c08052a44800b00b0070485000400f85071000c0c243d00a003403c44902c110525090300140a009410301a500d00c0407c545418001007a40c1c01d000040000403c09003480102190b01a0b080195241d00c000024017100c04001010550036a202c400302101d5a45c0402240c0c815043c603900140e10000c0e8416206110201d400b080b03159842902d54410070014007400b00c5e1135201c40d10445421480c001d41c04c454018907070b0030b091703840380c54040342d18a05940c030800300d580800c4c19480400140c00c448400c41d1031030390038002c1c28030ba00c0c400c21b41c1e50b0600d401e000040c4114441c10a0051004030340f903c07400100010402691515803004043c0710f0354481c05880030b42658804c81c1c848000340e2404d000504000000803d0724010032022f0589401d2040d141c600340300c0b600c00801940c081d48030340c4c0300b00d0006a45c0c4030014005540300e5100000712007103940000d420f603100c100746941801034180801480d615009020304417440125442c1030140c135a0540e882c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 162347715 1250 162346465 162346493
    0x17030904020c15060603060607030302030a06150809010f0c08010501050705070812090f040912050d062103080f011809022205040c0b07080301030f080c01060609050310020f0301030f 80
    0x1007800419024040c4102040520390f103158100700c501143d54020400c07200f44021980705a1041c006d1000001003072207135000e5030740100103800020303001d03807110711101103074020410600c0042c09010410001070020701034541e100c1500c1d001400005020343c0054206101406000d041080104a410a00800300540c2e401048110203030380c1c0d0000b2130034000c909580241e003458000c144c1c011180005081c140710751403945802c800c441407002c6030a00d00300c42541c0f00b040000201911400c000c55000350030300003161170303143d0500105d0045101e071801074800000101035130001c52480f001002140d909511800001181000000304c1e50140d100003150110032101501040200000c01c8510386002d912460003280110004481103940d07441c0c0b10780c98840d00e04010207404c8180010800104c3c050818a072581c40344000a0400b08010000c0d0308603411076022400048845c034003000345017814000c1e603150078000c410a516003d2480c200700410320042c8402880c5540c05418401803100306036071814 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 162348965 1250 162347715 162347719
    0x70501090b01090209010906140f160b07020c100c0c0501081b04030503040302190b0d050c16050615010e010c15020903031309150e180c041805071a04170309 69
    0x305035615100c900009401081c07174036003c110300321408200302e0b001d00b01c140d890200468110f85040405c001c40c41c40798211402c08031081124040000020309455446803054074564028640458004c08204040040a0741c40c0305001c03113114510301046480305520207680c020309000340140c0381e00d48507200e0700c01c1c0c03182e440c02001000f00d004000c005001c402031044130700894a80d000c40c0e0082d40350a01c20142c5101d4075104000c2003280c000c040c11950040b40e40070b16000d0200f4207040c00c00050a1700d00c0d00c41d44c022606600000200040818140c410a01c105400c2c45c100130b21f000c0010000e01301e04020380c030280c025000442101d440750925011510300542c0038060b02d40b0750040310b40c0c10a0861050081c0d100c000d04080038043c00380f0300c0901035002c48042c1c40960030b41d070701c42541d108400f280320745154256001c0e0001c99405602d0324010810030802034044203102c40941d003000d504084154110540e1800140240b45420f441541a10141d9241c00110783c110b10a401c1d48901d14410f42024503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 162350215 1250 162348965 162348983
    0x60103050c090d2307080307060b0102070f0605030f07110d0305090106031208042f011211040b040509010e06240702040903030501081908042102030102030129070b0103020607050109 80
    0x7000080103d441040c500e5410050361070720040585a00d8817150b0150101030780c0306008100110744a504580541c01c81801980c00140c0c4801030421420b03041c1d004034011900000c2481001465046d081e1f5102d2510b01e81001858040200b803905c0d080e40261b03480403d03444101080c9105400e41c880001076034060f00109241c0c0440401030100e180488041c0c6425114541c90003680f00390305410140704882c0d401c01c0c2001d000c00030056503c01540304400c0d41482d81c0300340c840f4502000c2c3c0d00030005400c4003004107071224905000c01408050581200c1e501940250a2000711345403c4140208060a0a1905282094040e048109029812000e50b002e4184030700d2400b8581c03d64002410f03502504166281c0518204143c2c9c5010105a40103104903810001003200394903c0c0350100c140a002e100882e005200c640002c1e09980081e00030000300c03030fa200360034601c1c3e911440c800b4001c10142034900e4184121a00c42030400c02051001a004540000742d2004100c029800015603544c0141a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 162351465 1250 162350215 162350239
    0x504020304061e090203060714090d05070f0504140f071b031706060304030c060e0a021509010822060f0e0303041b0501111e0f030a0305041e0b060103050c09 69
    0x2a03400b82090755040e8041c1030f0164203003a403414890184001d02500540104010303201c100049500c04841c201c5080480018082d01032507980d241c00011025000b034000300320a504001e10ba01301d90785140d118070710a80c40d050fa04d42072002e0024543d03a0044c11078160a4181c3e44105080d25000d400d2104104000a070b450040b041542090031660b20240107141603a4030f6450300b043c41000e00c01610090085807482155500080311504040c061801020543d8000c260f943c0c0414091030440c0c3c9622200c0302c011906081d2542c0c010241030388480e031101105280710003807649003603894003600042c100d82d4540010403000e004a4110310b401d6003004044940e6442d19040a01211940050303040101510810000f62507100e40403950414110901400c240007a0700140300407800c6400d06400e0a00070501401801c0c1001c0c809400e082c2c40a0702c01042500c0c05151801400300c4056004428848644102011422207015140d00503c01c2c2800105500d9001c45041140030318008a43c0c019422440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 162352715 1250 162351465 162351473
    0xb0903062d0a0e01060614070f060e0f030d0506040501030f121b11040e0d02070909050f030325020a12031a0310020403030e0303090f060a14030f090f0c06030a0b04060504020304 78
    0x10a0480b079140f00000c0048a4a60300704540c04841c03043e00c094242e03024409000400d050800c1040540d11468000550420181656080c03031021484038090360000b02d0b01c16012900c9014040d44000300329000c101c00e60559a4001c16034400302005004d9071103110100d502c00d400340f54001c040780040d80c03000072550501c1c86c281040305102115140602c2c10400708801c501c5002034541013100c8690064412203003000407240003400d1400051f07515200b1001c0c2004070302804e00003580108452080518017400101400443c0c0500701918000c42d8801c40a9001081c91079400742c0b1000300501d00401c9410070003030300c15138140008030810781c10f003d41d07a484558401158001d1013200d00c40d89030345c50300704078201c1059141e01a451500d03812169101c1071042c1403409070010b00c0c038603681d070501c42013121030740201d0640c50700110b980c0c050820180e401c0c090703001e00812080c0c40d4500d10b0750003841101003020104800380400f8114020160300c6c6c00e4003442c03650b41c6070051300103480090011034491503e410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 162353965 1250 162352715 162352721
    0x60f02120d0605030c04050103030e0d0501230105090702030403081b0309030106060918020304080f090d06140403140703090506030601050c01050a06031b1d18010915060b0903062d0a 80
    0x210340f034481d01c0351141c414140d003060301626040325050380380d04a5800895091203001070107100c00b20b074655031301d0300c401580e86281901c6034401229110003102640c1030000f0b202040d41d000d45902c0942d40244010400201120119290340c50b2081c1c00030340200000314003929500031142c04a40c035508040002c52002e52050001d0210780c0e880000ba07202c3d0b1500300d81101240b03c00d4a001d0080d14041200300500741c0102c00806150b41c024120441c1c07800c45803201002ca40310031412040210125041c0424160700040c10a003161b00c5e01d002e41c0c64420180e5005c0d02c0074000d4400c1500680d0084006403c40c1c1c028019101d000ca0000000c0c0b10700c0c80c001d1b10300c4c00103004600003120900000303e07031003030b020500342c0c058000c1d10004000494881804139540305400d4000345101e00c01c07c281032022560000a010329856184513075018082c0303000300318044040e1040c98024800301c44090002144541e0006041303a04412041d40180e4030501980e03201200f843d01c40c07640c10881444409228018803168 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 162355215 1250 162353965 162353969
    0x6080f1b0109031505070306050114190203070f06020a0e0f130903051308010615020120090a0312020a021f09170f06010f0611030708090103050a06170a020307050a0e01060f02120d06 80
    0x287d41001402e803244010b55148580300e01081540005204040b11070318031045170100170007640110b90910400350355102c3c5e00724030810220307581038002c24410840c0e0307009140c0c6041024121201e02422001c2d00c00f180100d1100c103418403410b511255202e0505000d10101c0760425032800d020014a5202d244440c0a007034903210750711202540c000500c40182c418070584500e120020145036031845100c54144507600512045075110700d42001c000000340101600503038038806038000d41203043d40d60041050b56400c07040640314604407030803c27908080e0f2001c0b000007038a66240105010020f1152060303e401450720704901107116600010079002c04d022f40c02400c0b20301640d501d1150410007090340340c90b4003842e10002c01e000400e2201c5a480e6000750450b43c1e21454009001902994038038100c10b1542c03407404d10200c103400c602d4680003541814044600544030903910f12511500d00941441c11400511404081005120003511654800c1c401c24190301e08440d503164441d08000f00d040001d040368 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 162356465 1250 162355215 162355217
    0x903211116050c090103230f01021917041101050a110303150306100602070e0c0904090602030a1503020a09020a2006060406060206061003020d060302060301090b0406080f1b010903150507 82
    0x80380745000c46203000c3c1302c030906032a03010542c0400e44031800b0b88011170030541481d40c0c4541c02030050001d14032509102500150000d10b42e030a298040101c40131784050010700400300719000700c00401002c02d6004441d1b8810742020310b0081d588100111045440030904503a80360035010000c01d111401000e200c2201e251001101a5151600c0300d2803e080e581c070aa03c2100b000d40c1040c03104006140442401ca43e119541c104403624002070040043c00329030010000b1074490b07501205021070b500c540d10030710f03013081c00740b9040d8110315086400051006e00c49109407080c59130000350600c209803094021161060102001c41d041072050362003191103407030440700035000f0747c5400400030350715100103101c2c0c1c083e510213400c6000740c52b84040210082d52100e40c9601d03542d03459400000c0140c9800004500030710005000180c100d541004200503260a80e0140300c5130703408101100b02628000c81c980c0d0421003819205002c50070784100581da140c1c00c50703201600341c3c00c4c96090f0304881c1c000f079003003c1c0c860401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 162357715 1250 162356465 162356473
    0x106080702030310060c110607050f0609070513020f1306081501050712080c1b07080c090115030b0418060504052a060309100e031903090321111605 65
    0xd0110201e07500d01046450452143d00f40e401044458060304c2d204400b14010221100a1424480410b21640c001d02e012100b81c0e0080410042c0c210050022a402011010140040919040c00121907202001e01c15000b103a0001d03010a0306250082210144810075180b124441d40c2d51502924200c1c04540b8552287c9004c00311030410340c0300b2000c68500d95440801c40115802054003110803010080140891180c1000314034544610341c000422080d220200506080741000c0c3c81d10b090403440140e0a000d882c0150040c0f1865030285285030403141c030703032900203058040d900004015240840342c0c1c1d01186d400360303000811720500e42c200e01d108034041d83c1100d00c1400f40f62007151110000c115808490ba040810203401460141d0003160080548011580c1d6000750280d81411a07080c0059a46240e00001e6940003228a444551906940310300b0708102c142169200941030b40314107010a44c41d1403103480109035451141e88070984e12201030051603102d003107955041141440703101c016a07081c42 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 162358965 1250 162357715 162357721
    0xc0304030f081e03100909030c0b1810020c0c090c0d09030f03050f0c04120f050d090302011e020a12031506030b040f0b061b0a1502070309050d02030c010509030c04050f010608 77
    0x43c200049a000d80c135114601c4207105d103003080110007040c0400d0201c04000719400d100340801c5c800003009008808100a004010301c080c81d000d89000c55520080088600501400e61010030201315041e4011094803122940d94170030501e09113500c10b440e82003000da85080b50000c241544001d5082440c0525101084151542000c449440b4030485600502c0f070410081800701040e05900e601c0c80501c60300403111282c007160749440c00c003940352111200003510b4003010025903a000c8002d2519044058038410a40c1400000940b2081241009440b40003100e04a60b401842070b80000c800c0020305021000035504c8200c014007074000c0090091080d4100b0b1803041448009118042031003200a08441c0340c48070801080a4180035400380341e4060041031156004900044402d0090342c50002005994401c686400307018482c06c0c0e000140140c5a070f00301c410040c1c030300045d4001c9441007403d00940341d220420000b45804d11410301542c02c203080005202e5289001c507002c5050b165035441d900541d0b5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 162360215 1250 162358965 162359017
    0x306101b060c2007052b060b0f09070212090a03060c020c0103060f32061207080109050606030402090c0d060b070501112d09060304050f01061502030f0c0304030f08 72
    0x2000e01c0c802030f4030300d4000d0482045185404030444414000d0a0465000003012a4642a2041ca2040141c0740c194a0b058076228900c0c000c0802d0140f000d040702c1c0c0c503003a41444803000b503448c12903001981d200c01002440c850359030f42d00c0e030003080203580c00001440406402c80c4c0c000e484402c00d01a00780805d052000110340884138986180903a030100b00e803811040f00d81035601d14110035242e0520941c1e1815102a0311644072400204031100341c168083c4103500700240f00034800141644104011494441806496a1a041201c1c2c003c0e1b012070340503841d500c6815070b0f075a45221702a0541c19042c40c1220000705501c080c40a000d20a0082c1d0003000341c00310303551800c20148102c0c0c0f0751055070798840c840001c0319410144115070b8107410948043c10810640d022801c0350344140d8007560681d0040d200d02c49030000c240a98405404c5503400c0040c480b12022010f507a90003050200310a031900803a41d085100740800a8a000790340043c03407482d054017a03007402034072640511011051410f01c030140030542 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 162361465 1250 162360215 162360257
    0x30614060405010b09010e06040b03070917070608040f050c0909070915050603041b050d030804060b03070602030a0f0e270a0b03102301080f19080306101b060c 70
    0x240c48001131145000e40700c5004407900b0741c02a83c4142d03c07000c01e0101143c2d02d040074024610401c7c10342c5a01080908200c1030b1701101a4400101c1e42e540c1c0080424000309074004185604990700a051028005c4907140003810000c1e011181c0d0b401170583c004100d07460500041c4041181d458060400c50440199482040c00c01540135150300007100700301140005020180240b050054455801d1099496800041c0407640c50f99068000405c100c4c01d0000340400c610950f48510f10441c0102401860500c1c00780d102c2c050710200609000c0410701140000d07020b03040b20355028400030520009c603a184102c1140c0e401030700e035404110000c030100050030210380e8455000750300c2005009040c1e1381c41c0c00e12410041c2c000703482080384004090390742d480181c610b01c1c4c5040c040c0c41814040c181514800c1c4420340741601146034141d184002d044000c0106a0800c1141c1e0000e07001c0d01c90041da000c04030380c250b801c4007070780b842e28000ca01d918102ca400c2c024645c1c442c0041030900d40c1e4580c85054906015104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 162362715 1250 162361465 162361469
    0x605040b071103070b040308060604090f0b011103120109111c0914060c070210050909042003070e060f0d140a0203160b0a0305060102070f0e0105030d0c0c0b0c1603061406040501 78
    0x1405c03d403900414003081c0110309041d400040108a00c0c0b43c0380e1282d94090548a801e0207403682d880e101c0c5d44142080d138201503441240c8a11800039070612940c03509101290700188140102c090ba00c282d584444540c0404840801c107013012100c80e50b40010b104100100b407101401d445030140d83c109501440d40100f0441e000c5d07160220481e042c14459002c2055204c3d005240d60140715007000440401e1321000307503051240d401400d8441000300300c00c140c62007080060884500c2a0440c107020f1140c55a0040d0664000c80d0030b40d5804074540e40c40c00071903d000c01a0002826500600c5c0150700342806c00a03425440d2803080e400d41c1d9079000d11030300b0403e910800e40511440310170700344000c00d01a44291302c1661b1001c41407045941050341d501d918580d211490304407c074411421001800306041c10080d0300003500d80ca161004e03021800ba29055920341050141400341c50001582000a420400c40ca50442604501007101540e81e4940000100511070300108040d0b41da00c0001d11314a8148074584c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 162363965 1250 162362715 162362723
    0x5060a0b030a050717280e070611010e010213030606050609010c1b050a0f1a0301051005030405100219020d02010b030c040b0a0905070806030f0106050f0103090f0605040b07110307 79
    0x10850315a04241400307804001c01c0c5900f0003c13190610505801711405460080700c8040840c02078001140c20465240b0201621074203244c01c0c816100d2003007200080c40ca04460303140c07512602c1e1424045406001d0865403485c3c0d01e003580040791810303e15845003032840071288504020800c2640d19410b10044c0d004103001607004c12650040c68010910b141c1c824a101132410026280300c076140e0b0300060f000c2215030080070b40e5001e840420b0021800040c2141401900200050309544c50040000c1d0081c0e40d010203002001000b0001c10308001c803c0011300000e800d050404c0d926210981c06208072811440e8401e0018451a098100d8150042c0f08807800200003502900518198a05100143c00070050b001e400c01081c440001e02d0944078450715005d4015590f0750b00140c146501003500d413002034010b140147e49400c40808c00780d690104d0406400c442800e001c00c440281d410580101b000120000e80228244000c000030004030041152141ea01d40d01c40c136107500200141d55680e801b0b01e800040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 162365215 1250 162363965 162363967
    0x60f260d0806090c0d11030702010606090506071202031606020d140601120b01020a0203010f06051504120b060402040306020a12060611100908070213140c07050c011d04060303090905060a0b 83
    0x2409820903c0415a11580e403005491601d80300c0107615003203a540408150f030b0200040140b0551603420301829000b401c1d6843d0550300c042c288000240d01c0e10a08100030645104240740310a0b0318001c1c000d4803c0080600e4041907880c0b010304000c8069030000c07081040303842c03922018a8000401e200840c0c0030340c506079a00c0c07a012030300340da0071001083c1c0c0780c0145041d403151725590b070b0040c0d40c240140511075103e010042015480e0101b030181c02031000100e0082c041c02800140114001d940900e980e66420103203980c0d09465170004180244141d801c05480140006800001c880d00101101403401140108014131235440d80201d40c10403501117007000070381001000312030b0f200087d04030981c4a800f0b81a040d203001110b50001d00c0310290280ca0550f600d454101040704100502509640030044000785403808001c4e5441584900e800e5240c24140480031048012296a880134890300000c06441044080c1d140e0501900416140c82048025410f0100150362410f0070368829045032070a503401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 162366465 1250 162365215 162365221
    0x106090c0203031305030c0a0305040f050a1508070315030615230607050c0406150801051c060504050c040f0605090c040305030301052b03030e0d11070b0a03060f260d08 74
    0x20f20404407a401302030320a07100502807041050f005001000c0510704c207483c1e8a43d03c40ca0721742d120b14615020703840548078902104007000840f81050702000c1c180050329109511b5510000103034001d180e4040304e41c1c0ca807219180084100042a0300410461803252000000c06a0303031215241c00740700108107a1780d0440c80b4040b01c003d5051500241c85180d110310142d480448140c000300f02210701e80c3e801060b4507003d00d6626103840707030042c961902600e02034401406443c2c140364000a00080c5010003021207560306e0004d41409414807103103c28200080060080303078600481200074100c0c60044510422a010105845c410104121800c50380d00c82c000e14296840c0c101000868914441010a2041080c0507282d801c1c1f443e480403507180344a034600007058a2000e00311303850603044200300c000f0312040b0032130148483c60000e0a90201d660b0000919075a5400b068110040c00c210b5200710901c1802c05004203041c03403901ca221504040740c80002030121491004e1542d2a40318030aa84d003c6411a004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 162367715 1250 162366465 162366481
    0x703200f1012020d090303021b0d0801030b06010c1a18240712060b070c06050711040b011808010b0306070f0905010c0201110d031a030a080d2406020f0106090c020303 73
    0x50b4940304950094010b00701883c910f035071016284411800c90009900060300b61983d030780fa10000c10302a0060000304000e080d14000580350080600024015102c400e001807603581c40b420420600c80e82c1b02040f401d41c1c5c40800740309404010107a550444d8141c440c12818400b03d00020040b4801441c150780040c07590003003521022000b4060001e004000c1b42d420341d401c2c01c00c05409540f004003400003400781c0c2c0318202d00b401050180c4030b802c00c0c800c0050400441002c90107098001d489901d0848000031030a0300040181c4540c50891100c0c443e1b621240e10010705424194050314140000390185c81d800c0da90f803c0100d5141510007000e001085401c0014003a55114461010b00e551060400310100c4100e480c9040c5080c1d290302074400000e0311140c041c044051a14a4010425400d800a0403c90550360759000f1a002d84c0700d1802c115035481705d008040010200c40d1004406e0301c5508141d00d2a100e000003501e030b1202041407140d560038408001003c0c24103104504c055210ba40c007540c2140c0311140c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 162368965 1250 162367715 162367727
    0xc08030c100906141306060e06010c0b060109052d0d20180c0a020d0504050307033504080c060403020f0d0f050706030c02010b030601060903031803050703200f10 71
    0xb400d4a000d41d5407202c10800099448580703003c0d4000c0021901124411b142c20b0b402c1d40d455402441d200114031081c4881030340c000b0703401546e0907800003504903a50381e440012150f1a003294403c1d070340b20643c003504080004001292068090640c8184a18510040103101c1c060340c42c000700a2071340c4444040d40c020f000e0f090007071030485100201a2000340c040710488146009041e42d1140c16180c000641c040c08a80400901c00050314504015050074500bc0c0042c0d00e43c422840040c050642c1007030180d2944030004101d8074140000070744482007032070780103000c7c403541c2040c0940384080c400c1c20041c075800c2c500b981c1550100d0380d0041800100c0741c500024040340c20003000e0105c480c40f84040300280000c005122000c054502c03a90300144120803c135000342903480c1105117074000d810100040c800e0f20f038011010300c1501c0c0c040c2002e20310a442c440a0050540c3c0e25031016100d0b01400d140401006650a40103484582c401840c8108940160810008800c00c0050305c1c2d100340900301c0d102c0c406000f18 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 162370215 1250 162368965 162368981
    0x509090408090d0b0603010b030604020306071101060503030c0726120711091501120608071406070803010b070605010504020306030c01030c091707030320030724090c030c08030c10 79
    0x90703015040001207000301e8180b042001d030485000220350200000d50409100700000400120020046410300d80c01098581e080130740300e0f60411810052182e0340041c2500610010613010f01202d50303a0310101521500c506075402546004081c1000e64546072500340c2c210802e203250b03a000b80030b914840c411112919031202c01c04859030000101400925980d00c00401d00c91240f0140c03070f090342410000010214a02c42380300d031940307528140c2c062065100024000c010b58905401e204095040c560005050b80600540100b5002001001140000d052000391800c0780c0f19100030b1101e40d80700d0007004141c0c041207400c240c141c3d1051101c80700032341c030a4126200e0801141403038008540c440a028100d2140c10185001691014800f0006c155000101e0300c0c0b200143c06084081000c2d6450941d124414104090302d880061f00c070000c4100c803005200034400c00410700030800c0c2451454115003407a060701c400d91f06503102c1040040d00d41e41c041304a4864188000150a0321041807a182000b41501 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 162371465 1250 162370215 162370223
    0x712050a0c0209040501090201030509030a0c060b06090604140310020a170c04090c0518090615090301060b0a2607020a140102070804030302030c2a010815060f090f03030a05090904 79
    0x740000d0805a2110a880c902407400b0301c0c004168500140000341c03d84501400502803540104446201030368000481e0f0416544000041127202d4070300300098460040d24500d03944030800040c0003c0e605000815082941410b4082e10651020410888128042c408284000c540d010111000c40385008801c03c2d030100e04075100b82e0400f500c3d850076038122003141d251a0046900000d280c101500410b4180c0c008220441d0060541c2c50220045035840c4407034000c20b902840040740c2d03020141e50a400a001411788101e020307442702d028442c002d000c00d14416903408000d41403030305140000b0401400c1841041d4540080a821209d44da6010044101030808041c6560034481c00d00000c60500080c80103500a5008507100c0d004190034a05011b64548000902c84010700641f084142c020035032034041d2003d08000440d6030300c01112a00c101c03043c0c00096807085c0c00040502d080c0c040c15014081081c004c0e101c0550700c0e44c01100303240e901d1103910104404160203010100051815060305540503202d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 162372715 1250 162371465 162371477
    0x50a23010c1202010b010e0411040b070503070506042328050f01060e010f12051203060117101a120c0714030307120506040513060e01111209070b0712050a 68
    0x15500c0b441140c140220100006075114048032640c1d43e80910480720000c81201c04001c14400071001000c40d1103140b00d801a0700343c001c1340400074414103000391142d80d5044420b8a60500e020300d8458004a041000c0010114022404641400d00060072031302941ca240c03030112180a940d041c1c01c5209041c1c81003128075200700c030b03075180f0042c100703005143c028040301421001c1541410b11080fa96490341c1c00640204184000d1400401c4000400c025042c1051f50384954a4580c0740048640d02c4000c01c07064100d41c2050240104a64040411822903000e40d5200c2450035940c10031140360300c0b50003000e00781c600310080801c28040c241c40041460f1841064210b10b148041044103007590000c0710050046008020583c429045038080e10307601003000c8804001c40d280858141486a590070300290480350754856a90400500b544280d9a0f00180e00300c8a071070f584a9040904241412104145540502500040d80c800031030291400f865000406e103080c0c9030010360445603034100e04045800c120b2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 162373965 1250 162372715 162372737
    0xf010815060d0e0705030a05100209010504050405070905030c18010b0a1107081b010903081b0c0d0501240308030109020c1f0903020c0109060e0906040b0303030c070c050a2301 77
    0x7940000401c1000d44106000c25402400c04140d41090402d5204a019410440074540043c2c0082000900340451080040c2c07200740c2d40c001220789001d9034102e51341141c41c002c280200329030014611012614100c08540800791080b0911101c4000012091603900414006000c1c924070540501096201c03460300c0f108604d044000b880c0380614940c800d12054001183c0a0114a000c00a48102c400b0a00700301c00d81e5843d5a451411a06c1000c4800145002c420344441007048140301140801c0001440108000303441d040840c02803140030448000c400d12401030700182030020160908681d0131080943c11686410b4030440654440983d0172540d0080490900c148500e112481c54500c450300c3c0000781c00c00e140e15001c0e07d00f80022030464180009100c041150a070700c54400d01d079000060726404130a850703010104002d828201401649801f0110411541c030584001074031010303001d030001c14034940d034a40600504d0341c0180900b10742ca00f80c403858103c91072024030785103a441c98185010541c8127 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 162375215 1250 162373965 162373969
    0x1406150f12010905240108030f0306010503091509030a03150501050a08040602040e0c03040203060a111e160609120305041e0203241603020903150709030f08041502010b0f010815 78
    0x4403072000000d49041680b58208100c028207170a00e03001d049004020361034030103041210500c6000091005042000000000e010018140702d00c415180c8500c03074101e0b080c02c2041ca100d131240c0040c141580000c0c0b416000d41c00b00702103010076908540301030f10f03103500d8900c6c07040044400c1c42c4014026181c80d50208000507500c807090840c0c500c1073304840d422541b0b030304142c4105820840003902e001182420422000000031416040f10310269003084504103209103c1c0c1c030010203000d048030549410a62000c0c0105001103900715403082c0e8428801d43c02c0c3c41c0010a8281c1c1119429603020b000956044503030b441d501030001d40140d005000030300312058000c24625140c05010350109030100b1603a01400d00808040c51111400ca02440b03080650605000e100401e035034030007500008d4a60740440c40445c2016004ea807144000e160402d8034a0140c1d8500e0800d8a1123501a10030b10000746200c0c80e40135107107813041c802d03080301000080c42001c1682c420001107900c000080c20300844038600c1d144c480c0301ca03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 162376465 1250 162375215 162375223
    0x6070b10080d0e010305070206060a051908100c0f21090c03050307030c060b030a031b1e0303060303120203011202190902120103050606010c02090705030718031406150f12010905 78
    0x26500c9580c0742c0f240b503620100010f0948401a001e0019076001105008203aa02c03a540c0c0001e803070050741c2c2c4090b010003000ca074281621103940408450700a4460301040381946400070914400c49403510324840260300c10454217508a10707682044500600b90b140c0d814401500f00c503240d10300030225290700305d0b16030b00c400d03003190b20a010843c00705480c29021b50800032117004030041c86c1407ca001d0325610602d0348000d0000030051161250308899036100304104540004240100107080c09840700512691030041c0080490f80816004140d9036039442c8035002440c001c40b8181d031851088400d00c40410750a00400701c5500a03032050103104404042442c05c0b9901c0a4681200b0704001d001c0c01d0352441c14950f04110024042c64100150556508096110110b545d5049109464401c1c1e40e0f940d005c00446160680d44074101002c020752400006010306103150350388415100b019280241c40700b10305588050030300f141c0540c0083c1804d00ea12400d2511224403910340000200208804c081d5940702414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 162377715 1250 162376465 162376483
    0x1050f0301080c040e012007060608060f0f0108010501140f010c12031a040509150a060f060909050f0106121104030b0f0106200a020d0f150501210206070b1008 70
    0x65501110803401ca5203484d0080c00304811100008121192203045110f508500c1f5403540e00f1140c40000d2070300d041200c240d00c00401400f407482175440d00e0800000d000c0c116141030750030b0400d6411030400413031200e03410300c00c00d41220046481081250085014440c042443c60070041c10b002003000c0800112b6600c0e051003d456505550006652041195200c8006541440b05024510b064104000901c2c0080d00b17540002118a01d0901c44d41c62440e030b0000b61006411551b1402e040340c02c00102c6580000094050b00c1603480305001ca90703215140300c001c4032400d115032000508010407000329015181d000002d4012198251484d081e22602c2d81c1c91410300030b50780b1441074101207004000e510343c060750021060b5060340c007440100341040d0100f540c0706103801000e4415900109008104414008201c281c01d43c048400101d042d00c9003218001454244541e20030245072041c1c0c5030345121a03541200c2d0441d401850203080644076140c1084510004100c1d911866090802003a8242d0130010201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 162378965 1250 162377715 162377729
    0x10051c140609012708030103060207080f0708090f0301090507030201200105040503091005070b0a0513060e060f060102070605070b070203070c0b090f0a0305100c020c130501050a05090f070e01050f0301 88
    0x140b000e6403400c0306440da210700340c0651009061604082c4c0002d55200c00c913811290170403400350701c514a07030070000d00610812007040060040080d0000403c014400549200b2008460082101d000c10061500340c800c684001000c03a005540140015070150a00350081c08500c2415542d001c8110500780c2111030664064415500109080150786070156052120302c41500d040c03400c003072480e51150309682000e010151102d1b180c000180170510900c64031014580c0020043c05140c00300000c03d5125034043d12090400c801d15400683c1c954000900c030001c94009a4a941c6441070580381c0c1c8032180b2003d407117002140400c001031008114904a68409481550390342c0b56a0701c103042c20031080d001081009406107010300c3c000c101041000ca201808000c2e494804100542444000c17818001c001c0c1a09a0001180817100c1d6080565804a8140c41003034481284041d154020052200e0003290000716202d0428002110030b1300c00c80800384d40080c1814001c2c00e01c0c002c0b40d00700c00190406d8010319 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 162380215 1250 162378965 162378971
    0x120c050c0601060509010903030c0609080703030203061207080a030e0f0d031d040c090605340501060801020f070314070f1101020610061b14010e0604020910051c14060901 75
    0x50500e88040c00311500410719400c041c2d15041544001074194281844040c1c01e200c00c4980d02801d100c210f8000102c44e580c4101c000d40d8900703840c0340181c002d40003918004d00400204e82810124400011400140d4010000602c48146213503002c4401d000c3d4403283c0d03500510b82c1161000075448422814403954883d841d0720241c480c844c01001085681c030750000c0c3c41242003224068405420040150a6603007510701241d0360761034401030101e81540c450011070011484421801200d20361031911100e1031044009108555550590074203030300408884001d080010445040080c1c020903502c01002c0f03801001c1d40c10603105846104410243d514180d8421700760502d80d0a0940e410301c9055801101103980d010050b09040b0010500440001c1c441403c0c0042c10854003070000302c000309900790380090000d11841e00801141034850308191070407070103806014080780040c4280c03440740c001e80d1300c00f41c100180b410741c000c80103007044048101640c000c0404104140140000d02285200f1b0501d42c0c004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 162381465 1250 162380215 162380227
    0x204020d0203190506010c03110c030a2f180709090908030a0c020f06010e0613060314070b04141c080c060f1008030f0c03040b0c06060a210f03120c05 66
    0x11003507443d508007054181a03d03240401000d86e030401c00352020150145011042118809031151034995a0880a0341c07610810540000708100c0708c070b5a000d02c681600b5811f2851115000b19044405402e124652040640c40c18524241d442010701e40d00c0612440c121075074907919040795048440303045096402040000030040b01c24000d0281d01440f005510041c030083c003400c26117585419042c0250000c003c600804a607940e642d411880c019080406e1003003004568901e48052001c0d205031010b43c0500822600103601a1001d05907012600385503d03501031548140b0800c0780341c8102e00882804100f010600e040810905400b810f0802c0e04000140114242070301040407510300248040388000b980714044c0814000801681c01c0ca9000004603603c1b90b0b8000340d01c83c10360149420821024002083da10481440080e003640540c80584000c003049031200380340400240c000410320a0512000341b9240007550f215003088800380645004850481a921280e098078082001400015404958 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 162382715 1250 162381465 162381481
    0x907090806010f050f040504061d03070b01050303071a040204110408011401080619051e0f0a050603030f03060105091305090f0c10140d060902191b05061803070204020d0203 76
    0x4079901405060300d003443c3c028034207400240c90000402074240105d4586000c20700b00a40f64001c1059651582c190390042803915000b5a07032604110001e4030148040d500000c3e95050100171070380c1300c541050400c0442c00d000b00c2032440e0140054012038105a8401c000002e0745c0340100034001810303e000001c03a0190082441286040040e0400c8120350090018094094555885032180f25949000828207603150004481203034225807a215502c003020041201a05c0820b00907440b4403171001041000d5140e880030b06540c1e0166120301d441c83c01007080483c2e00e66000303c0181c042d42c240203040401d03410003100300005507141070713132020300300d6100040030001d0301c1c400e004d220000c12050b500101c00000350800202035030b007103004581d50054002140344801441e0b130001005020411015940c2e410805000c541580f800851840011019000c05002c40d03007003001c00d119160843e004020030b403554213560b1400315502050310845e1100b0000c0c03000589035800509400f40c0d0710100141caa00c1c0c9628 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 162383965 1250 162382715 162382723
    0xe0c0d0b0405101208040314060f01080316140c030f0102030105040c1b02010c1a070e09010602010c02120d0e0a0515310f0b25030c0e0d080909070908 66
    0x414074070540c14241001000a80004204101c07005291600c0c482c0e0072600303100405104640000d00062585804104e10304400602c02e80240352845010240b681d90b4204d25480380505060840d401d240441000c002c64801c0106ca14001c4246058508070131146e030000380b414a44130740b68409a5008001000b070740c036007031003150031505982c00c00303034403900e0110305100c4039090400000307040c0001e0142d000c0a05c03a61060340c11203a05d00b041c24850500702020041e15500c40b0701d41041c403480041f400400c0e1144180110b100e1f21041d900141002040d400c501700c00d940120408103646a52600005404103007086038054041c0100050803100d50303442003500b0f901400415810169440341c00c40d060355804400c2c4c482446244c40054401c5c0d410515240c0400e0400b0f0780040d0a2450450a0196035102e2280d000e5009103201803088118000e4201a001d072800781d5034030380220390f6000b03950790309060181e00e1a480d2441100864940300b00c0300000b46051509480c0900050214601480200030800c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 162385215 1250 162383965 162383981
    0x105040b060f01020c060a090308130801051503060a0c140403030503061005041d061503040302030d0f0e150a090b01080a17030c0417010f0c0f03061403150702070e0c0d 74
    0x18407120b08003282400040d645409481d0200d0007008000744100780b691141d204003002e940d01c090540e0740c1c1d18007058642c0d0411413a005040b500c0d441e01000c51550031021030f80e07090041016000e0100750b55140c945000811a03607189405100c2180440703904c400e144c400603c06180f2980301d05071030b810442d0612002011444001341031100030030041c0710346a07a1240080e07014450402c001820744da43c41c0420400103028180f81e100b040d010043c4070030550044007074920921021020040d0740c0b440e400b08003c0c1e590580702c00041c0c0d005941c04078004408040615800071140c0d01c0810340410340d07911803000b120246c0c00740d042c035044043c0340702c100240c0d00c5805407000b180d260001e00b036042030402036065119922624038404076403402010182c100707410904501881140c104040d440560025100032420807850b000685400000304807556103001c5042440750150040000c0019100300c0e420045000d0034440651013009800070b80c80c581003445912684498081ca516000e002c0d1003003042d00c0e19a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 162386465 1250 162385215 162385219
    0x3030d06090b0a051f11010c0f1b1e0302010b27090a11010305060d150501050f09090a0b09070f1401080a1a06250f02030601060c170a0306080f0105040b06 68
    0x3e800030001503403440b1070038030503600b001d100390011586280141c035601050b86481043d5401d041400000641006480c640404c150700c40c0506c820764041414003000920350000c0c8900d246075a050388001101f85c4440040348240000215504a040001e202c84042e0b07884030301101070108180005c8024007011900110104c0c01042100d42c655a112031100c2c4e4200e060303040554580000311303d41c4e11401c412400c0c6411400102d50004c0000190000e0002401198001d681050a2090b00d0900c1c80040d442000000c0c040c049084080c0d88019000c08040e18042c1e00d840f4000300844ca00c03400140401c010415070040000002130000050b05400300140000c4d000d52402520405c600c5100705603820481e022207103603a40703d4020319030b030032004010300c60842c5040f405102c3c5010051281582d488c068001c8046406907aa1403004450323074140e80000030460322100202064000340840503040f01c0a6500700480e100c0e03290f5020514189180c40d00700c44a0791682c06220a0181c01c902c800d41051003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 162387715 1250 162386465 162386479
    0x30c0f03041506210303090c0518010f080a050a06111207081608060108040b0612030d060503070506040b0a0804050a06050a090b010e070917120c0d0206011203091e0503030d06090b 79
    0x40b400442e6032019001300a0180f644035001c480401030b0245041c0083c0000800a01044140007003120012009024441c211800303100301103804c01000a40110030396100004181e40701d0aa43c0301c40150541400c04000d000302072101a00040700a260181f00b10000d603501c6003a030be003c18007001c0140709101030b5424001503005100181c1d0b0703c240b009038400d800205143c49601e8107030107e80540030703d981840c170900010881c40340b14071242e0046400c545003101241d603903a4803401040020700c80c0b4400e43c0c0c000b84040020000d42401030302d03c168014024401d4415090782a200c84080d568100d80d4a015075030b0380e2403d80c0400500c5114036015104001c1000c0807131030301d5800900b491b00d89009a0441c0503281012600700c800404c02001441452801c40d500e039014102d00360354030300c003484524000d4041d0000104681c0000d200700803c6607019520742100300d20304801544011940f0200c03007044030003240045401c2c0c404100601003035142100014a8910340f01c03c0130120b65440342c40500c6491 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 162388965 1250 162387715 162387749
    0xa09020c030d0c0c020a0501110a0803180f0111040501120902030a0f02041a0102031806160c050306070201020c060c0c1009030509040c0806030c0f010c0b0c0a030608010e070b030c0f03041506 84
    0xb175140740c1b0810342e002070800f035060300d41d83c1c41503504d401612200140345c550004100710702c1500c02400455207a07954402c0300c215500074000c0500342c4908501d10729022005000c2000a588680aa2480601c0fa048001000821500407038100107480c1401e80c1d6a801c080b481c80118180751285800e92100c00402c42001e181d82c41c0000e40b0383c4a500c500803400084150540c65a55030441203585811003115549200382541c170705003510703507514411a4840e01654001608550041c004c8600350a6040c024040f50b680c0c50b40c0002c03c5800c040f0014540d4411382c800140d100886100d1080c24074001e45909807100080400c000c20344984441860801c0288024002c1503240007802b80990310f421603a40c40320080c1c1d000122101c545029020344404845020b11081d00980f10003031119000310780c0c0921401d9280c00204e030903104400c407080129030103510200042d849076009140c0011400e0100743ca88640c4400d01d00c400d800c103640c192849007005840412000342403003000d00411010a403017080c14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 162390215 1250 162388965 162388969
    0x81308042301020a0c05010f050408030424020f0c010c031403180106050d0203060c160c090b090f130b0c16081201050d030c08030601020709050a0f0507051303030e0a09020c030d0c0c02 81
    0x11705544a41414018001918058107004d40181c8014000c003200300c2c0c3d16613a441101c02c010072a14800500f03114400c0c2d0074440c50601c0440e030f01c2401c0340300d00028021021140300465000b48154419010400a81403184540e982c0d20001d5004009080c940076910300805441400c6400b59441240700d1080c540c424001a1408500580c8c4600945c45942d201c0c15000300745d20301c02803a403800603c070710040b000109203000301c0c0d400000b407001c05841d69021030f0345010003034500c4201038441c41d14007800b104400300002d400ca4a11f65002d00601e0078a4180300762099224410b00b83d5150440d1a0b04005c54138905418908543d1401424200e500c0400b000880e20058001c0740c403890007800c103000020010703507143d000f000f1540062070b111030700304913610b04840c0b22001003c00c08400c6d0885410b1801151016224a0984d1a003986060140c40001e103035a50a50340b4040c0c40c214150001c03a40d24002940d08036501c0035103414000e940c051581d40504201100444403000c00d10001c1c414410810800351b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 162391465 1250 162390215 162390233
    0x12110102030310120f05010c080a0608061302041a090915090304210302010212010b1c0507081515030703060f06030e100b04090c080d030b01030209030607081308042301020a 76
    0x2203141d07144ea038040c071400e402c02c000c0d59440340c0f0000d09103608100c41d2400003680112150310800d58124100403158507028025150b00064a464103480c0740242c96001514150748003d140e14551010715000d404000080741090070300f01e444030700e16040180708401c2110350300340040d88202018055442c20741407000e0380003ca0850340790301074040208074803181014000d504661949520801210341e07981d5541c0a000746030700075244c00e071031400c031103042c07003108a0f0078000e560144100d41c0b03a06072199a284100c600710640072001c540d00c403080c01c0c0c1c442c89080000d0011400740042d55004038070383e428085211544020307980312808240c50302c404424116804103101c1c25885201c2c0010070b41441ea0b00001c1c0107840c11000c0a0010841e2000c0000c016000260900898882c6d80703003800b90507056001903003240501044560560440c0b00090661440340b15040c3d03001c0e8200c00320400c41c894540f585040d80d00150020b000807090708420305580c0682039100700c1c15406c02d1000b4541500c40da40c458042e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 162392715 1250 162391465 162391469
    0xf11030d0206090628050c040501030609140a052d04030e0d03050f030a110c0705101701120303020712260c0a08061f0201050402192103140412110102030310 69
    0x420a4200754003100c9031710300c1441d210310111a4014052402c0c01c0c2200d5085510620034180481d142c010300103200d003024001e50750030380c0c01c1c0111800e041d505d00384c100c4040c002c018450b400c0d1900e103403a6031107044d041c1c08000400c1031030428141500d15042c90040c0103022034980c49441602180f603400c00280d8040d04803070f4501c0d110f488035900c030340b580d000401c0500360501d680301081c6004a0020114500010080100c84040b114502020900882940c0c094807800a0200089480005103d00754001c044000040d01c01c1c40c00506e03003607581c1c80d01100003140c413450707400140e00d9180414060b0748105818031011064000341509041800c0d0110062198404600c1807202810003e00c5660381c480240d100c0004000050031b00b0004054000e0082900300c030304030700c1103c4070203410b40c560082c540008107a6821040c640b021007548015000c401c0743c1d403402101000094200315080d80842809171000b03161f000d81010913201d10340341009c3c4002582144604540c400e10400142c0207003440c031201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 162393965 1250 162392715 162392731
    0x101112040e06030f100218211c23040302040501060903060536010608030a050408070b0405010e01050309030706150e0a09030f11070801020c06010f0605040b030103020f0d0f11030d02060906 83
    0x642d0312100390b00c01c1c1c000014041f82c150310907500440c0d4010500c01541e42c451641e004015a0b003604407030840d0a021031072105504000079000018048094070744840c0b08001180c0f858101c2c1040d5480c0e000506a44098001302d0028029400c10820450940101504102e1410101c0400554510300b140c1940a400448a5034413100d6150b805061080d032104010340311130000c1e41d03660001711101406507401441070340007501c00e2910000d600c01451080c0d0b02a80c10517511502c401c003100c0011540c03071304050b1610041d070104104640c00118280300700c1403d503c8900d9540d07009450000d540074000402000205c1036804d0094510010b0340c40b080c041c412194505222954a550702140341c03a0070950b4101440540c40020486100f5400107a02e0307040b220151107200760310392105030480d981c1c0583d21031f500d0500010310041c0300500d0582181684c98201034105011a90640c0315a00e040400a1081e9030350041d0501d4140c4608051118801000041c0028207690500c05495503607003000a003005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 162395215 1250 162393965 162393967
    0x20a0314120a09060f06030b180a0c1a13060e01030b012d050c0307200d030c030e0d210206060406030203060a050c070206070507060e150306101112040e06030f1002 72
    0x83e0800406601111107a00b40c41d0042142a81361710705000d08413010b84d0643e41925030100000c0f5440000a1181ea41a0b80a18980f00031031800720360b60791700c4000b60b00310350f201c540034407507114961103401c6a5401045590341d50604c281200e400501202c0d01120060f0400c1003400341d110941e1094102c68003180041000035414504035074045806010311107480d07101d804002109014445205411034144119416000300102c03080104014060440c0c0010003040c0c00d000b4000c042405289401564400600088e41100056a0b80c1014540244082e040041c0c00c0d120150096410080c3c2036002c40180c5040040605640020380e9412000717000000450311640010001d042d00070a440c01031b54044c02e11602c5501c5880d2071500c0e16000c2c0210400a07018501c204102e1810480300a030643d010007400303103952124424400c03240001045800ce000c0b450b4080c907040c00003040740d003010140c07001005459a04140204400d03d20261205100c0e1f407104081e100030b110301040758201e460300d0341001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 162396465 1250 162395215 162395231
    0x108030304020f0118060815030705091f0f08011401080c03070b030604090c170c011e080403020c09090c03070f0b0f1b030a090501022401050f13020307020a0314120a 73
    0x4841580765103500d1a0020203002c40029051f802c16100ba0080400000d160160b180101c1170558800861180590200d90301000c10540c2c4400414240c0c080454994006810b880e01d5042c10078241c0c9034001040b0740c0d595020b168025a80c085030074003501d00071016003454808040000d41d2100306018450b484440000803e507255216030007080310940c030090030382440d6542ca001d03403d19041008840740501440703034041e0b040e41c0b04151341e440010b075241505561207443c2d041150170260041040701903108013506520940e07039450943e441003d02c1d90041c020ba510b820149400c001c040e80c0701c0c000038a81401c05120300000030081c0c441d01c0340384880d682d40b6544c104d07080601000c0d040e1250845400005100c20034103a00c041c850301a61020703000c8400c403603100c1c0c0c2e040f15149140543c4030f1031a4184401400f0614000140440d00100103052200101a01c0151403c99200303a40b03240140e071246410808040c2c06c54010500ca220b80c900741070800c494510b6480d5649401082c80420703030b03520444 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 162397715 1250 162396465 162396467
    0x30105061011190309060906020106120f0503091905040b1c080901120f0603061409100b010311040f06200d030b06070b070309060608240402030106030f0b0a0c080108030304020f01 79
    0x3070071140d128202ca008280003c0c81c1409840f03121349008000004a4100002c903040e4014003942084440f00c0000e907076008015210411010f42e1030000310303951700080010404569502561600750a28880050f10441c40c0004001c1181d6001d0242030048103084591010040540081e500f100e8003c2e811559640d04800102e910110403064054031504c4c11000c60184106540800181da00c07030359042210301044071011514400032218581030b54400070300304603141d00c650070808000300181008110340e20b401424506940240e0000074104443d03940070007800303910444020483c0048500a0b000c039884005942c0c60b0070407410528240b50700e5404c10b0035907854010403596056001f14182680b420f0885000300a48240041556220305085c400b01d444a004500105000c0400d207416220600042d01a4001c1c030b0014401c2e43d141d540c40030000081143c0c02d4420601314070a404071b16040ca02900140221100840014208080140180600b42000080381c0c1c0260301114402081a40800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 162398965 1250 162397715 162397723
    0xd0f14070204061206050a0c08131214180a06030b01090603150302100e10141c0f05040c09050c030f071b080409150918030804080f030f15030105061011 67
    0xc85021a941c1460b00842400309503440341c1d000c1c4015150901690784c1f03489044804074015a2001d00c0d500456210b1030016941c26504c012f8144c0e9418a13000c0542c40b800c0803c0250014801d415038070595111515661404155031000750a440c2410405500d00b1800200241e8a5020724014142d580e940701220007000d003041c800841e4010641c00036650885001003108103802c1500c0d01941c0894140303d29107000d810390300441c0009500c000e08000c1d481c2e10a2a2482204802c0d08410341d03240e2846000800900502e84a64010702900241070314006920080f210002c0c07600030703144814418410080c020002454210185145c5101000d1640d09103c150901182004000d036500150014503e0407039081120002000304000c0070081c0d6415044090b40ca000303401c0c444110a40c1d88031000607000310703600c40e086400350320710070300788141c0c0d0000c0007155005507029118600e8001c01c00181d07803100c80e492005c8000c1036000b840642400800314510245102c0d103c1d0034000c121414800320b0900700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 162400215 1250 162398965 162398969
    0x2060a02010b0d03050c010b030f1b0f0406032603060303040605180d03020708160b030a020c0f0102040602060103020f10020606150d1d010501060912030c03030e01020310080d0f1407020406 83
    0x1410f510550110745000b802650181014020302d50078400c0100b140c0c60081348104800100c507002c0d09000074415546000c0c0c1541001f46076124500034200036858842e88115006140300fa400c0688012600070305140c10303807401c00c1c034050f2203a0800c1085103545022043e0380c1144d0042c1881c0791656a034024944075503034041c0565805c9200132240805040d80000c159003203c2e88401603800d443c0701c0d0003200380c5510003401403500c0840100003041c03200010303a0041c41c00305095000d44403114508014039081e1380c03080d0b00800c0168007603001401940382c00c18400f01081011680c090710150906d8002c0e40b160001403440780700c0c1c000d5508a92100c0e0315a0121558482078140400074640015900c000c65200002c61035030707030362900c8000726038035003e020000159000fa046c4201d41c0503071542d0407984103c104504904041d00d920703030b81850300001d002440c010b1164101c40741e074440c00c02c4920b0385001d04500d401000c10208403841c108094005403800c4115240c2e4260660790700060020a014211503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 162401465 1250 162400215 162400219
    0x10090509010605120c0a050f0307050303071208060a060f030b0402130f090b0907080114031f0c030c08100b0702030f0d0c03020105010e041101030e1c050a1202070b0402060a02010b 79
    0x281004603000041d440001a40c0301103403410040d0805008040d41c51140040190300f112020030b0034021842d01c142d00c5000380000400b10340c00b40e5112404a402d40c0c0111130300311044d800002d00e580c003e0f07801248240d4802e03001c0c1d600001441c50b1100040c001d444541030300050658560518200342c4681d01201c2c0340a4034504648000c940c0d400c0d1101840c00e6500c00e2080321482c15502c09818030300070191501501325696a201940d0800c01000788010030391a005500d4810b4122013000a4408504111080701001c80010306a420000260548401c4100001004403010402c0003502c14419040f00b034403840c868813500c076038907880400c4c0303029080c50000d081482258030240c000c1358001c2120b1300c500d100360f00a2169981e187d400341c40038002928002c1040700b0300002840310f94807950212030742c1d0802c40122040302842c07a501081d80100c1c0000040001c1001400600743c0d50018a0003801001e41442146041007545810b0304500000d0070082c410400014a00c038014400d4000300211000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 162402715 1250 162401465 162401471
    0x16030902031618060302090c030901090b04030f081e0109110f030a020a14120601110a0f03050a090b040e070c140102030c040e090604050c0f0d08030c04030b01050a0f05091009 77
    0x76003002908601070611505502c0c50700b980b8840c0e103c00013800340004817035003d04081c1c42a140c003084100c5540000740494030755942c0b00707008c2010030000c28030b6600031030294845002819618000034100070000340001d4500b00d80a11188294040f903040c941129000c06000840d809120780e103921921840c540d1480481d401310a00c00c4a0076181d0041100803841c1d101e20703910b08445c00c0d2620303881c01102d19141d1021210030004081754000e008035804400f9a100f603440c0c3d454140e840c0d04810f035002400303400141c000305407401001e0b0011201000303030403103c40c8181442e18041c1c495000200c001c00c808100a07000040304c042006158000517002d010000a5440b072810484c3e000b041d1300b1030302c921500101400d000c256041d10116102d03006c2ca80042c0944480c44e1104180b0030f580e80740316051904900d00c41c4000020540c8980518011160842c4c2c240c1d85038514204007810728010b820141c0f040b4a038400030441c0c00d201c040c0540417030381e050324400c00c195100b103501a00149580e10030010182 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 162403965 1250 162402715 162402733
    0x9180d0f1815091505030408030c090409061e02041a07080c070605090f04020f030a091b120212010c170703021c020903100c09140619020f0c06090105031603090203 72
    0x241072540c90480750b00543d240111650f40d032a9030a03100c01e9a000180120344200f000c500400d20040055a2045822000b103142c0810480420103d5081d018281c41c482e0b0394480446080c20160094401420801019800d02d0304048100c01881014002801d955400003246401c100b42e1074207450102c000d441c00e4030280c40e0741d0440600320364400c40c00e840c414070f0320301c003080114a418429603481c030380c10507255400c40d5600d5643d080107042e90034064480c84090042c01b1401c0c03c1600260015004d40106010004080d01c14401040203c80c5030150b1641070001c54400d6a40c42000d11440001010507514180c40d116000ea0003441a4152040d40000c6140300c40e900010540003801c070f4007000d400711a80300c0f80808800302242c0001917440700096034414100251500d040642825180003402607180c03008030100820341080341c00e110405a000110a86440340041c4250300c0420b02c195607152500c1c1340940000c1c5648001040c02ca03020800c0c403203280f070341440381d80f00c1e0300c2e01740d805000c0b43ea4800d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 162405215 1250 162403965 162403979
    0x30a0e0d0210080103051c121802090c0a08010b0903030a180915031202010e0607050703032405090a021204020603041b031401060f03020310050910090b010509180d0f18 74
    0x2500340010b445501c51f54221108400744c2c406c040c3e40c000e03075503500c2c015468840009800684103940440c0704005000c13a480300566104200365009803000c0819a90392500390320b001d05080f80582c0700700c4200d0740505c16925192008002c6680d45030940c940310454101d011601c000c004901c0e041000658507040a42c00c07072104510840c815603004141410515125201c00c030300380c8408805110b00741d00804041b80b09113029002902e8200e10906010400b4050b2040341c026180641c0200c0c00d540d80144400c0040c1d0600c030034003070341103414070740c05514003010a500c503078801a01400c000d008550000029042c4021011480360884030b8416181c0c0c0c0c0f603601d0a08840d00d20b400b1404101d40c1d480c110000500036020494a021280e0203005000b002c400103081500405004150341e5060040d5045a030546200b44182003109124061040355541802c0502c25884030041080940010f080640c1e020300200040710003008042e0303d061881c3c4084000f08880b6000c4000c4003000450284002003802c3e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 162406465 1250 162405215 162405227
    0xb010305030d0506060a02070303141b06070912030e0d0c270507030b0a03150209090c0a020c090103110925080402040c0801061710030c120c17030a0e0d0210 69
    0x31407614410f000d030340c841108110b200c0c0b007000b551342c0c09a4000c0200700300090007105001804807502c0806411b00086224600c00c07842d20548080003508603504000d080d603004801e81000c1c0c0b0701c181b0250201c00c141c0e90058180030603187d182d8826445501b12900700b1002040c11000f5240c1218034400490b10f90308112585040313881c02101681c2044002000c0c180703c0d108580c00c001000b0660030507075103551180340040303810110400da040e400b000300070029180c4080c0a40138265207100c9507500c1d4881c000090500504c01c0f822841010171200400104035090000403090704201e488aa40f600c0b03010011520b200c0481040006a041000c01c01500d0307048290039100c0e138001c1d2400d009903a5000003c070b0306403400340030700b0b0046100d074606065817450007483c0c2c40d48402c049000c110842d49070b440d034003006c613002d9112a8a08501188180c01c03c220048442c000702180c0217a04540c01001c1c0109450703000e80c440c94001c0000c18141d22030b00b9904c030100310f83d00980141410045420380c1d41e00400e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 162407715 1250 162406465 162406477
    0xf130b04030f021807140904021e0a031a010914010e13060302090c070f120903050a140c151b0102070c0308070c0b090d0b0612010606090f050103060e0c090604030b01030503 76
    0x851008031342c080603000b07244030ba800d2140610f0b65810495480a9190145a81001d0103c0b41c00c1982403201c00c000390408409070070748002c0c270042d09072510b00f500001401d0752810140c0b01a4500c800c2520081660004209002d5a20340e090940c1c004510740e00407142a40c03072402082e40b081030001000813204165100c0c0064a000b41c030305841941d68500801c003075100b040c80040c004462148100e0101d2098900201651040c0c42d26554003a035940b9018a001400241607900d01040c2d6880603203000c0400910b0485807054072600c1e900c1007101600c091500403800840d026018911381201d49080c20b6040310400d0b5408410001c21588030304000109411075031007110249000f80c80400e4945500301a1585880000d1500102c410b0903960104e403031030060282c41d048280c0000e040c0140700c080c002da501038480b950b200d1a200f031805480d1100044181d01c640e040c503141c02410b10003400c186121546c0803104202c070a80e2500020f000c180b03030b03214a0b80040c0c144950780001000f001004002016 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 162408965 1250 162407715 162407719
    0x30c03210f0b0603060a0909050f0102030108100f0e0a020108100b0310030605010605040b0409021309020304050a03020d0504050d060b06040503030d0b1005180424060306080d0305010602030f130b04030f02 90
    0x1c182c2c412407060103403610080d60919404072000400f0440002241c001284507803080d01550600c034040307282c60f030a80c0c00a812580c166002600c3d4003612000500c00c1090203440d40809110400c411039400751102c4001202a04104102c030001d42d4010707600e24203074010040b041103035950b4a8903c80350181c4039543c2c0400c0b0f40c2d5038100000020001d100b08151026600004101c43c6172610301200d40e0025070082006420780c40d03000d40006140070181c40a035202d14010f50103004501c1851400030308181000e05c0d154184030040c030091202d902c0300c6c18003e8900340e1227180002c0380ca0340b020004244c1e0185c1d5109503450310000404900b05880d5810048086000340c2d010701814040b0341068440d4001e051418142c0004002c1c00603c0c2e241582164031003108404460f03c101460611080303500425404c05000300e504d444041160040400c0308689861180c6020130042d410310100030b40b24811124807042e10100882d0111000711010f8189000300300003010b25a840b0b6803840c0c003054110961038140c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 162410071 1106 162408965 162408971
    0x117070302090c130b0316030216021f0201060e0408090f040f0f02090f040c05030609040c12062c10020d060e010f05100203070f030c03210f 62
    0x7030f001d0656030600360364801407038030401e28519083c1c0c00f05060030300800400c075040d00903800c0f86030f03000300c10714000d60b030303000c03041261044081c02c40b1000e903000281d00080a4940d01c040715015201649400a0141585d82d040e91040064105c030b000c0e000c000308010440441c906080d4210440000400002c0d060003800b07201f00840300c0c690303224445c10351300003034a036650700d460501c0d6000c040d0101e0f82402002c2c4000350051041c00090101f9004020740804641040301d05025080644401f4584180426181c00e166019254022100450105841d4030035070b22000402c01221019030507004041006035200c1100007544041000c4140940c0c40c04d002c80c12405100015001f00107403080c00b64003a050108202800e440c0038800c1c0e0541d8400c01c1510001b64400865171140c942606101f03030007201d9810180c0711807000ca84900d544182c5100c1414600a044c0d00c80c28551059840c20 = true := by decide +kernel

theorem cover : BRFrame.Cov 162230215 162410071 := by
  have h0 := BRFrame.cov_init 162230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 162230215 ≤ n) (h2 : n < 162410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
