-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0281
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:56:53.028981+00:00
-- url     : https://prove2.me/submissions/ad335a81-997b-41da-88c1-6c3e764e51c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 50359716 ≤ n < 50539572 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 50360966 1250 50359716 50359721
    0x180105060d050c04080f240105090406020a0e030118030e0405040b160e09040b010303020c19060f031b05121806010308031f0602060108011d10110c03070809040c020f0c01081008070306 81
    0x88100d800641244a506134000400c034075134121278001c3e1521500365255200ca1009400c04a5500b003003000c400c800c2103295809005841079600e117180356102c0c12516180143c000300c0844c0709d180c001ca050400300404660882c400c194003a200d80c1d14001c2c0380390800b000303c4010780d968040c0390b80120034200f40810b00003014001c5060317a1080e001c60ba498038164082048451030700b4140201c803881501c090041a12450020080b022a07060201c3c10f0100003107204103000a07611101d0005c0e201144c203040700101920155004802d00c050800881e540c00307070958a8030340500000c1c2c580341d0004082200f0085c44050a100710441c03113180920980c0340c00c0001c0d26450207110b0300c42e0b150f080c44498080b0441040314802e140010744001d003d00a5080d0f0a840038040030445588000c80c10700a04500c10010f10040c010035114400d02c070b603900c0c20314040104546102c9503040441d07102d1200d1100c405030014028200c8034090811004a41e2101031f4244079041c19003204004e4000c2010000802c04540c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 50362216 1250 50360966 50360983
    0x3050c150f03280515040e1002040e1b3603100516050405030c0f0102121207200307061508030d15060c03080a05090111030103050c180105060d050c04080f 68
    0xa018080b00481500002e009032003003510309802025017604481d00e00c1c90140c2c0100c07104a03020080e200841d41000c0c40108981055100765900d658140800080b111040c602604c203244211000307044c900c800c3c1050068000300142c95401800108070410b54a100c4203070803a032240300600312920b9002407150480645426194180c1d0b040000131010303403050050040d2000d686001c0c00611562504100f00903810349002c040d6030640c0104444150020300450081140d03034403080c0b0207000c0b801c003407000404071681d5201081c028a07503c2581d440102c00030044841882e0480e1002c07400c90303600702c80013000e910f1a9021904511000030003106451107504a50982c0205401c0206030b40c2c0d643c6002c0e01c1c654070188000f40014064000914060b0080e4407075600030f849980001510f9404c46c500307542640c0280c00030b072000e5100c508000a2840d04a20690050254600320300480d4581350214010380104048403070030640398800a040d082500040c0c50080c42640704480c860f42c100070700c0304c0c4c460592 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 50363466 1250 50362216 50362261
    0x50406030c050d092a05060a0815060310060207050109031203090212030301060e010305010f050109051c020a06090801051018020a020a1a01150c0807060207060b0d061a0a03050c150f03 81
    0x40c0000300c100b039136417511000200c9801030308032850304a94150844440d4001800036426545001d009500c6803218000b4501c1b650403000401c544500b0b10750080d15000b429880340381008030a041c20300020350f50200c6222a80382d142004940f601c0a0701c0043c482c078250706d185191500c00400002801d0354440c0c00c500c880348003030720100803998a8042d000c0c1244854001c140c00705200b194200000e0800005504120b000080103002445880e400600b1b00390b986e5000800048030040c05008080e0700788580d541011021310b03001e924030710300001040102e441a5003400303060b81c045803a082c954000d0000c401910792151080100c40c0f4414803400f80b200c2c081c0074801a080090380c480c410749000d080e6444109802091080c1000640d5951801a500480c4110703982500c035144c01c207168803582c1d031403c0c40768807440340070900083d40200b0006000d52101f010303200d455640b104001042003c42c090920740000d0303641843c401489210600148501c28850507400400401c00c03081c01c0000e070040410403207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 50364716 1250 50363466 50363513
    0x503010603060602030903030a0c030507080304060b040b181501020f010f0207060e0f03030a0504060605060705010c0206090106032a05061305190b120405071511010b060a050406030c050d09 83
    0x4a0f03620032070381d900032046019015441044541c46682c041c21541443c3c0744130342f81107450808195210355a540082d05c04451480c1c4584004d015072405001e076007a001001c2c2d52400076244040011102e020010f80000c4d01021440c621031101d034401e219048102c22440000d011186019444100131752042c07805407074961415a500780c1180011a1480c0a80a150000d42c02c3d51600d444420041c40003030012100e040c0e50300740004d565110700000e000680e000d0f0380001141c0021460190505000800440c896454a401440026400c2c02e02118501104542045200351210500040b05654001c0c0d5800840407c01007401d000741c0e030300c80083d40c50554446000d10901040000d000c501070184c080c10010a020349001200130400f4958464000e10480d2001503403080c0c050074060f41802c3c014001401940310105010017401035507900e0342c06852030751505074807800c001c0503402203021b079004143d1115003404010384103006649000701041e104000c03549042c0f9044c15940030140c0020041c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 50365966 1250 50364716 50364719
    0x1b07140c01030606020303070806010201090b0103050303310f080d06120c0b0306091501020109020907030204050406210807050a241a0f1003020d06030b010807082b1e050301060306 79
    0x14424000d0350204c80440d0004c50a5844001c401c1c1e90100340148028115940c0f9110103002c10b04044140b03000314081c1c0065540d0342043c0c0f540f074841c070b0500d558500b02d55541081c144d404024180c5500501134210080074964407152500c40c6192258001d4092000d04100c00803564142d001400410316100b80c50005c1450783e5036008540b180805c45040e5270110003080080c000044c0079260031099201407000180300607642c3c1c0001c0c0c401d641030700ca840009a0101d402d00890070184928400ba02c046006e60b1754034071102a24162145001100902002000c1f85040030441c0801c01c1000407507000c200c09181750807480c0000500700d05428540040d82c145400d90b40b42c88481109864250009000150511103040a0000a00d024046041010350803c42c0f030030b000c4450701c60310010b1481524041070740c1d450140c000c0c0c030f000c81c00e40043e00d0b11b0300121405280c035440d0304180600e850080b2540c00d280d40a16401303940500c801e11007003101d45085021112890742c01401141a02d620f41c40810016 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 50367216 1250 50365966 50365969
    0x2060906070c02010c0615090f0b0a0b1b0f030705030306091302030726010203090706110d0e040f020f07060617070303050f0c0f0d080105090a02030408070b1b07140c 73
    0x400041d9032281c04905400408800755200e40a29810140100d5021510301b442c003407100350280965100c803001d99940c05c80c075040c403001c1b80039407080b40398100c808448040c18114002158484d001200d41740c1a0a081d03100c2c000c030303002d01001800944c0380050f01c0c0c4521903400d04039203d40c400c4560030f21a031190700c0000d800b21541c8613248510303500070b4010031949040070304800352100303071a0f4100300e5500fa030b030b03070741c03030325000709000440c4207058020251220320310b4000023810483c082c240a00e80c032f40042041030b42156203c10034644a11085a010619142107403054009104428041101d490005540381c10b01c051a0030880440780305403086501001c0250b0a261a040c407400000d001035010440f0f4245094410050410703801070b4011f8681c41040300c06080d140400f40003a1501151a280041095262a10000b41e008c50441404e41c507500e400d40c1c60740c00c58130840900400340c0769880045041000c0c2c501e510310080c4094bc0005e591500c0c00c0c101040c1d6400094111821486500c4070500907 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 50368466 1250 50367216 50367223
    0x3030206011d0f07140c01090317010e070203030c0906040506040b03040c17030d021803061306050a020a0509090405100e0c040509120307140d05010b0405030c0301060e010909021503041101020609 86
    0x110604440c00c041a00c0c0c4c2e003011501000e036801e0071102c04000344000c42181902380308a5089070721139140c1c2c0c4c156407062048040a0001680300141032000c1380c0c10002d540e5004003c0f20340c00f81e004184155540e05140006400c1d00813500f0058000f10040303008210201224008c5000302d004200402c1c0c10790360740b09600f1703a400508000310002d41040c0810400903407150090401003000140a1000080560129240c4101122580d80b40400b201e4114140700e0b462050300d070030400d130b188190710704514500050024842c044445008079210030004081c44401c0c030908000f0249030b4818040c41410050469507000b124200d94491444c042c0071600f4070b100020b071044102c0e0301000172030856031005010303105190180c240c4108207500f0044010008424429540039010040c03070140c8490400382403502d8008599010303801f80e0f142c941c0901030390b04451f904c141181d0311510042160300a51010684051010207041d88603940401800100822404031682da04401e90031034400b0746c0c407101015076 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 50369716 1250 50368466 50368471
    0x120305070b07030603031e1d04020706050f0711070501020a121b0303020903161206050426040f061106010b0306040f0207060c02011503170703030b030d1d010203070302062e03030206011d 82
    0x101c1c8041d0340c405101c8480c40b8694480408c020300c0181040e4054a80d0740c1078520443e01171400521410801c0507154001d10305448a2001c40c009104060900f00040c0d0340700c0c600030024144407028001016428030541302080c5820012030603085e200c41c94034016000c0c0d0031090340c41e44a805000c4100c102248001890001c803050f100010100c18025100d8030001e21001d0300946618480c0d00400d40c0d0815901151140c100c0324900d40c030360302c500c3c02118020001680d00603204100d00e840c101c080714200041c441d81540c0e24154066130b00d446040c00030340140100c4409450749030010031464140a0705900c8085104030a40090020420203001000c00b22514080200f6030408031018100c10803018010384101072090600113800024600000c1c6441030b840d55850009201c070741808000c80d200c024150b2042001e000440c18581e059070080e440f01da000303000c2d8034084000200200e081d400300d501000c6500f079000144008a840341402501c40700f09020f8003001d2800000c1901005056110052 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 50370966 1250 50369716 50369777
    0x2131506030e12030c0a03060302090f04110607020303030612160608040c08010902060d020a0509120c0103060b210c09040501060210150609050108070c020303130302090a0501030b01120305070b0703060303 90
    0x504d141e40e42260405070350000c154400c00c055030303801c0102c01a151109154055410f41d04240070619281c03034041150042c0b503141d80d008038000e00030030006032000416641c10090498414442140d2281024030300b00d02d00c2068445582c85031400940c59800401c0c01c0d005600501a064545850301a80ca09070741000700c000b5000704041001c8003006d605940500028041741c5421407401c82840c0c0016641448030344543d03120340041da0010315940c0c0603c90000148503040d00d56003804151446604400245000d030001c080c1c4007000510400300700c0e01221008000180100710075610340030002d40c1c1d4001080107080c454034140c2c07151011801d19000e0400c40e40550b4840700c44500745401107801001c041c0500040c44150301941006980c00c0c4090f082c1e441c51141c03038504461440c0100b1907000c03406400d807a100e9103090014070114021981007415036954070100c0b04111103d150817100c62007103250140c1442800000d00420742e6041e0400c80c201ea0003076450504581c1203440441001e003000c000300d07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 50372216 1250 50370966 50371003
    0x10b040e07030b0a0e10020d1b080109020706023001061106190b040e010b0103110909070c031101020309010606080108161403030c0a0501021e0c0d0c02131506030e 72
    0x80001500d0124210340c0401e550f607000c550b000c2e030301940511b400400d00b603405030140c000c502c010310361002c0d2188400340b1002c000c80a07009220083e01030b0000030180200c40c1001d07000100c040500c0a190126044041c40708160700005080c500c3d11a48030b01e5484802c49054000000090854403905002038075032034200140040c1c0e120428484900100142045440c980301c0320765070019552740c410311000340002c1d00003061190b1010001000c50f0001000031032810070500051541d9201c95030400d0b444900c60600b0100e9200c1414161100b0b070203400322040310342c0000100318403d601904000106e528640fa502041c0e62580d01590f2110445680408809c2411400308120b000c41c8841d403409060184c06e889c07801e008001d4007410f05014000c1652030b42c2d0001030404020074103070181a08544070108076030900c00d00b050420b85079a1401c02d104100900c1c144440155070300c284a02d4800080508100000c4c0d0040d80c2e0b61000301064402d440100340703080e07034000c0030b15401728181819000b2140c98 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 50373466 1250 50372216 50372219
    0xa050906070f050a060f0f020a0e09060301021204080409050703110d0c110d0206160201060e0f060a0e040605150109050d0f1403121801090f080c120417010b040e07 72
    0x3400556002540191201d0081c08000c1010a1040c40040744d0030703001d00c101141140c0314502410540322511018881c445c4104010342c3c003181e11080d19034840c0e00c100e402040c9a201c1c40002802785c007914101070b0b0640c08081c140020800c0e0003005004540201c0014800e550f80c40500354121803c1481c2910550b100300b003a01c080344030981c801440d818803400c00c500403a40180c0614913140050680340c0140c0c1c400b100344040c030711050710b0701411440b071032000f48062030078644054007150300a850100382c40c01c01400715640e90344105000300500400e400082c09450103080030009801d090b1a08421844103882c084a20751003070022005640000c2d204000300c0d243c540d07950000800c014410364001c18442807240803018280014801e0703117403100c014010741c04d02c480e0b50040c1e03140102095580b80c4c500000000002d60028104030b500b604401800e80700d03011100710505000901441e020039510000313010601208120f00740302039505c0040204a9143c50506101c22210344855085035580940e40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 50374716 1250 50373466 50373469
    0xc04020315100908060a0c02011b0f11010603081303060b040911120a0507030b042102070509071101060303120b1c080a050d050112170316030c0302090a030c0302030f030a0509 77
    0x40c055070b28010b81c6401c807440c60b5611801410804150f803000b42940d107420100c00695424020035072075054000f2050401d0444d020090484100c54100c8401e110605060807035504080d0321a00095400c2800e5030340e61a40c0780c49000156680e400111003803881e0a000038103034206442108000c0d64480c2c2440c1c1120781240800c84e45401c0c12001c9501e6120707441c003040c00524188554001584070b002c0d115064101490041c8941d0350191031560090140c0e5058a031140d8002004030840da0142c86010607a00d40d02c0c400c544601e120340c600001e560034100f0000425611942100c030141c0c1c036580030005d4201c000c08220281110300d4000c1011804102408080381018004003001c81280c103103140341400d100d00403015a41c00741e0003040c1d903144045030a0180007a40d00700214842c0c584901900d03616041d500450441c00f51100c420804d99181c1c0c200c482580654102d940100c002440203c000b642c0c0d2804401002803030000300d02900400c18001c411030000020b440b00c01d4101d407074050803c1803400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 50375966 1250 50374716 50374729
    0xc090f020a0903110a12060504030201110a0509150405120c10090f30050f060703090b1f081218040b03060703200c03030403030506150405090c040503030c07080c04020315 75
    0x202105d90110000c240000ca03000300d00d09800c1114400c0e00c3c0890340f4900740c10040d00312607a0b607180c045800c42c03c0201601030742e800300448003081011280c000c104030304107010701c0c558003540c2c201640041500c00200404100010450920b02e4200c801000340b5401c0d42e0111030b108140d1142072010140400280700010b0210440000c40c0200e50f002964100c65103e109401014204190f40d50303003211920701d0381980b09010700341d40302100d8101840000420703901c440907503000400503401c0c915101c9402e99203154100558005200c00012a54408114002815954400040b10300080c030040e60010060615004071804803800602610141c0c2c5d03600030940103011480300350041102d10604d501d45080c0300ca03020700301c0d600340c28006584a103014600a0200e89000d0880c0713201e00200d0a0310704000894608450070b8502c262803007076070f681303400c0e0070b03415140176a412240d4907000104e505151603c000a0002c1204c4000b01240d10701116101071100300e200c150b0306e07000c1031001e80210f1056401d010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 50377216 1250 50375966 50375993
    0x503090109080406080f0705040b09060304020f040c030b01020c0d0b07050d02070204060b0a27090b03070e09030705070f14040b011b0809030c01030b03030a0e1c0c090f020a0903 78
    0x20800865221203581da4400568416046000800c2146007480004540004450352068550801b145003900313118418809001d005203c07403140000000042c1103403541441d01031080d00240090201c001c6111000d00a03000d507222103030052140110414007407400000c0002c007241c00c0754a01030142c4034050200c9040d0703c001c50501030543c0810921006072102c0c8620340c0185440941c1588881c06024010840c1c07140e01011075800d921202c81ca4030903401c405c0e010b802c41c0c500f0700300058012900740c0403900b84141030340034200d00c034488010410f1480000c401004541c1c0b01720280d0700b2072501d4001d1288040100c0c041d111036605c59107038001c40d608082d400140c1420050410030740030b62806e00c1000049000c200304451084e0042101d00240c141001491540d040908061101c81c2e403043c04255280500345040080103005017100b8605c0c3c454010503100304483c4c01ca0604a00014241140d00259910804131041d00d80b40c00040360f0101c900c2a00e820441994614110034a1500c0f40800c10014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 50378466 1250 50377216 50377231
    0xf0f040201020a080307030c08090a0b0c091c0503040e0705040614090109030506070c14030a0e04050a06050310150e010302030307030807110d0315270509100e0a0203010b06040b07030503 82
    0x7103a65103c08200c201010798451500d036070b008681d41d142024014015840585422503544c015483c540004603010302c595403205c0c81400d2030b9220ba9030580003030001c04c80040c003603100313025a148081c14040c011004100b0340e00b1004802010740c8441c44122407a115501c554000640c0c0c100d110349180c40880020301c2d1403d41454010700b06522030720703981c1c02c0000541d04e4001090711041240100f014040c0c240c104400403801550904404900250988520311100351103940c1c0c0e000000c000c4145c0764010006031070040d0842d0a0410540d1918004201001460038020005070001810100205545050320b034050003540c20000581c7c1e0540f9071070300260a1a0a00400d080c0c140d0030002c08210703003104110b0030755010450343d03910b640c1003004803040d0b04120b01300c01414401d01882440c41c1c0000c214000c120314000303035584c0c505020a013062050b4400c440711500785000c070340341c0b43c00000301200307518003c40003000103480040030000c20384120300c03407245110024054036020034050006235502400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 50379716 1250 50378466 50378473
    0x5010c090305060f1f06022526070b03010b070c12020d060203040213180303061d01050d0f08070b15040b0102100c0201060509010b0a0906020a02130f090204110315090f0f04020102 79
    0x703000b42d005e50041c2e0407040042e0f00410480515059030030003502d00d0b808601d500d09079141481440300d040d16640200304004070420010402e040010480440280300d00000c45071256121142000702d580800c806031404880c155001c035290050300f4002094950090490340011815511603002c2d420060099070b00440b104940c00d0080e056028188001003503ca07480400d850520340601100c1d11a00b200700c1800c50350011500e9055003410290540d182246d10710451002c42ca42a000d0b0201d034640249190001324000301086140006240070303208146502e409030300d41034240000c440c0c8210381a0300590010141281e1a525503101c000341450a00c004640c5645410115401b80b1b820707407100743c0a910008160b910310f50302c4070410002d00040d20203061103088540001d08800200440d41c801c0c0c8c2da541480d1498242c13154005688642d02800c01e1040120304001c10005400813640c01c3d0060040d15000c0860f481c1000d1060300c2030031001c02d040c2035600e9070020340340320380310060040b0f044d0710 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 50380966 1250 50379716 50379751
    0x70302070507090e1005131103030418090c05010503090a08090303070b0c2109070b0d020904050403020703060b060a052208250f06120c030b060403060905010c090305060f 75
    0x2a400d00c4440d001d00070180f4086032140745801320610344040341186440d1a4505001d102840d204085000f400f03540044046c101c200d50f20f40003d040d03105039030240c2000c13070900340403000562440d04102c800c2800344940000786a990300042d1401e01c0300702c8603800320382c204d03080200005041002030b001036072000d0100c904000b410340c3d03500722991090f43c3c4480340b4680460044031000688028034150819100da01c202c505201200c9550f4406500030900305040c0400c003070b005030710194181c43c440d403802002800141028100030b0b4440c011804240c3e8100c0c28151004a1400c02a007240c40c0c200c00384e81e03900c0c40e10071100000b02428014a0302010701c00900080064841ca0800c00c03944249416a1480c41050080440c00308849843d13000800000702d4400800c081d580021020380d00c40f00f120004110509074a800324020445200026881040860301005101c46580301482030340c840d6008011009404400750748040203440010700300c0e8003000005016554070321450f500003003150140811032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 50382216 1250 50380966 50380973
    0x9052e050d0212010e0a0605010c24090f030206070816030b040605030a0c14010f0f0507020f030f01060303020f1c11011e050708150102030a1103040801020a080708011d0a0507030207 80
    0xc3c2d01c0703003800c901030701400001805031844103100243c03c00d6240c5400c0082c24500b0001070301c5d01624840c0640422481e5504860301d81c440005c012078103940003030070049030707480c2e240011051036002c609a005100f12030000303040d540140a030328082c90f00391800c1400e8072030b568011000303400d00c8401d0b5a0403035219840090151010030000c894140b160f400c01c003116003031003201c889000e60f88000364100400840d000740419004000c1c00d80b100d4052a000790b4030760715400403071403240c0243e4005802d0311900c401a001c224041d032003002a40c0c800e900362000700074480e050720b640d9030321903a480007010b00b4407001101c0640140d2404165070060400419107520740460030a071820340503802603d4544a408000ca2940e00510301540314134405081d801281420300000d43da0b0040d40000014450380304074041d41d040341001510014035140c1c0c025560303020b101600601c1c0c80400c1e40c0e5100841c80140004c1481c840a03035980d008492011402c01c0b89545813104080904000342051040c035500300484000b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 50383466 1250 50382216 50382221
    0xe1801110c01050105130603020a03140c030601060f03060801110301060c1e05010c03230a02030a0617030c070b0301080607050a090518060108010501090b0d09030201110c07050109052e050d 83
    0x18801c2600000402d0342c50300c424001c1c1e111000710014403107890084284016a5442d0700e00003900d811007082c1c0d000e5104411420324007007520340019032611a0000000d60700d6800203154000008940d8140442599110381c02e0a8665190350f240a4250500050024501c41c45040c0b50750713070080034200404600740c0c1c20b40c80600106002034a103651500000c44510380c16001d19032070040c0000c00c41114003044d44902914803400380200590383d0b0004041a1200d5094010751b01034140801c00641929040c0c42d07050341c2e58031a410340c14031806803c00c005500c4c5541015207048401e006c015110079682c5400840b0f4550101100c0014401e2640011409440e01445100f010210f2000e440081c02c080d0700141c024801640454100034800f00c0074005030b09010142c64541140381404100e220f00317458164050407044e55408600d50010032002c2d07008100048a0b002c4a90030380b162610142c40e88107101c140400d03880105e0078001304458141d08100304d00c01600c00c11081b803800c541001e881c1e014100c01d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 50384716 1250 50383466 50383477
    0xa0503150406181406010b28020c1507050f071a0a14160c08120f090f0d0804031202060708071b0605090c0102010b03010c0206070f0908010908180a0e180111 69
    0x2404c0e000d048010310903040400c4981d01620b0010707481307800e1840300b405c1c5d1041241c103054044d04403108a0740d04e84e010740c02000b411019110084c1040702002c003000c000c2a25810003c400c1d9030030704c10102050b440348bc0100c0d9180c1540c041d540c500c04008215440f408150380507070f940404001100700380700300020782040a0131422031500d030680800c0e08541003104d90481c860304221101d0b0441c03245061318045d1041146c410015040c0842c0e26a91303901d0014004050100e000354102002030b40000c00c0001002c014020350340b0440032201c0340c65410b04101d80e589000c035071a801080709200031031070503401354200240c0c070750103050704440100c015990b040640300d0948984401ba0f209101c1e460180d070302801a00103414082d00200210700180304001c0d6030707030006004102488004c0c1072819949100d082036030f0103004004028030495800e807500650642c001b0080e42c4d4840c040759184407041c42e000409100721210141046215211441c3d0f0a21807461202c2c140a07d660f224405c00c40c241d98000a0720 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 50385966 1250 50384716 50384723
    0x4120b04020f03060105030303010510030b03030406020a050708030a05031302240c010c110a2d1b060e0306010b030a15030f050d020a0308010909020a050d150b0a050315040618 77
    0x24500d0426105100e108480301c40818880d4100000521032a240013040e281181c400312441e0548864035002035004101040c080d0380c160100046c0400c04036000a0300000c1c80e031040048840660b9600300c0f4640324025204424005130040000c501c82a0355400540c05040c00200403c00015243c2e4000000f990174100c40003940d5004280c4007070000081c8240f080705001b9050002480102c2c0003070341d031610b940c1c0d1070091038a146102921784401000174001000d00010320440486810340c1425080c080103070103030300e43c2401c1c600301c00702d4094495901d03100000c0d405401000b00e0707400c0c812500c2003500001c01000b4204c2d628110941040415a0407100031400740e00b0810700c8001c6030070311034100780702e42015030195485880c000c00080e0384042a04c0c1110700c510000140c80290b03100051440c1100d52255900880c1075280310240100e11452690412003148104125021901031141d8a13020380b04250341600444c43c880710181d07088042a9019105080020750900c1050507041403401d1800d0a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 50387216 1250 50385966 50385983
    0x180a09050609010c02101812031b050702010f0f030b0d1a0703150e1302040c020309030706030b0312031f030804060e09040b01060f02010905061504060f06050f0c030412 74
    0x1000d004041c00069000700350031000740214090300802940c1c440c80c05a03990030a80c2e84420500381004031b04410036600c0c4d4000d40e1603034189030350000240034055002600c0c0c044140810143d074194081c00440b0800d5906031038a13142080d02010645500650500d503109140d2100541c11150f0741d952030104145100312041561406004484400c8903070081c18107040c14a8203079503441840c079407a1070300201e9001804410565031810201030000c421a20000e421138105440581425008405003110000950488a190741e64142c101d0545176501940c0390185c100d20603411013041540700541e80a1400003d912064000740103000000d03100c0e078019603080102150a01c11260301050001d14407004071642a214102074960006c040b106101b61003c3c0680b034002005054000e4022130b0b4400e80150a54202e440c1090704a50811104007003144a50700d40440440c000b001c540c1044180d48695072140d007404d43c14042c03544035a10144a40640c1c0c80300384000a2110000c5c3c04501b030103440b030040d6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 50388466 1250 50387216 50387231
    0x1030b04110603011e0e0c0f0c100906060302030f061009021e07050307020a091112040203160f0501120e0705090c04030c0303030b01080a0506010f030b04240521030711180a 76
    0x40d4680c0481c550401034952082c1b02c184481d038001c0f9030a41e0520741040c140155591048040e0904d800c0d0740340400403481c0d04015518003408500d030b11a0007164003c4d010f44003112000072249807203490403038800711f0707120078040244000c0c0820f82c033800021800b07410104800354841070750103898008010407100c5070b100140440440c245484181c00410b0181002d000d60f81c60030950341064000d882e01e2201115070031000509560f0108041950f0580c1300e01329020703054658842d07c514149500406003c1004000c8500c4202c038503101d04010011650302400410303060904012118030040c040e5815a0404d00c00032021455600300d40d002540b09840000d584950748001625625000b040002c145180c401045030340d903006480e08a0005452a00240c18803c43c00090b000385581c1860301180d5460700d450500503014485440d00b62041100c04081c0c011300c010824808000000c000c21a6030410301c941e10024031391102026000e4001051060010502c0d9114a42c003002115a03c40c4182c64425 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 50389716 1250 50388466 50388509
    0x1201080705030a110d0c050607060f0b010f05030411030a140619090503030415020d021309110c0a080a0201020706020a0e0109080705010c0803100506190207150801030b0411060301 79
    0x4108001e2030140d002d0003004920303032901d24040c0d0000c800e107401a040203030007030200b104014544c4050314006144d1610754449041c1240145048038800c0090392a1020042807507020302d6000381c1c00501581c03001e00c1c1d59155503540e11261071940542c1d40600c00c440c44100000d030050802c400740c034485001010a032509128940c041c091101c0006e600714540301d10480810008000c0300d60060b0000c541030001d80d48811080700901c0340d410703003081c403600c0842d620a00e50051400141169000309007803000311551810074095100d0300509040c968003002a03039001030301440c00f4282c0d00141d0300005040c41d8017611f80100b80e13444002c240c03000803400410b070b05c4990381202442001d400810010f0600c1820517002030f00b401e42c5200090402100440012100007419400e1005080301401e41601d4070380b1800c030b498200301c0f00c0303c0b200e0142c0210200802c8542c00c01d00c0c403070034081469880b204582d2071034850410380710014002340d86031030030b06401140949810005500901041002c090000301501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 50390966 1250 50389716 50389723
    0x403020607030b060f030a0c110f010603110405091e030c010501060c21050a0311070c03050705090906090a03050c1e0c10080105030304140a0801060905010515030601021e12120108 79
    0x810512800f0140175010586004d0310641758049010fa0340095030020300c541c10f8500480200c1e00220074030540301907280304241900704108072403088400c201c68402c5101000f054a404a9461032564009803820198415050f924a41444030b50181c928000d400b0342c800d401c1d42c80c26004070000c6003510410204000040c40c440401c82c8151410080b00140103100510b1845802212000c0584446108201030b010200f1a455160f1021401804640d01d19105880b9049841014451800440003604030340022030414401d441c1d900240c883ea5090f82d07003d541c0c5802440145d4401e114089003c109105111001c9034400500c034000c00c1d50442c150108507450310a04284001c01c00414010080c64034008103840556020721440d00100d02e9200200f4030011403580300c6c42166080c035000003141c84003940610f058880960303203041c03515012146901507100c01d03109a40141e01007010b100e5158a298040b9020100100a5803c114031500c0c04d00c0958002000e10070354280c104004020029080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 50392216 1250 50390966 50390981
    0x20907020102070510050601090504060e0f07020703030c06110f210601020307020f0607052404020a09020f12100b070602030f16020604030c050c150901020d0203040f0909021503040302060703 84
    0x303200952500c2e043c2d981d41c940720b1102c200000400c0b5100c0010585c1c1342e010740302c2d00300501400b0b442002240d075108010168980705460030f0034000e034080d011071402480456440e0590303800d51589a00013490781e035040010300c241850142c02e084103002c1c98804285e84401400c45402c2e80c80034455001d45600000403e4001400d1070381994003c108000040e02ca642801c29441d0084522948a10703090a000d030608041c1401ba0030b40c3c41c0409a0700e8a440541c41d10180641d009031490f0110301d849084501c201d11500104400030002444441182d981503080c09600c195450550b00505940340c4c0515400d81001e01c0c100c4000e5000b02c2004081e50f025854540d205901c6880c07021140910400a91140c00240010b42049400c00203c81031280412200e04d44a6000e0160020740004200ba420035400c2058040c1c0180240030350403001510010a0300c00703807541070008811662421954800810380050100d800c40d80a400400c0c0302d0041d80090340c480c3d4081d401404052500d82002001c80d54103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 50393466 1250 50392216 50392231
    0x7060b040605060c0709050415020a020601030b07080705090d0624030303110a0903140c101115010513150510090515160b090a0209010b040f0504110a030209010513080a0209 76
    0x20f04c030300c18804000007507002c1100c922510002c0e1a84541c101000301c4169420090940340c00095280502070340021414101c1c0c0c042c0b02c002203140c0350a2000c40344d844050755000d0000d00103010307400041c03401250800c14940b2480d00001c3ca01400e840e0146203203101c0f181801a041144d8080042c1078040c01043e00d65401010310b2480c0043e41000501000c00500002e408180f0780e40c1c5d00b18040c81e04008a10600000512501071010381a000600c0c9404410143c5124000c622002c1068206000402d040c0c0ba4000d28511000d10707a0310b0504003c00d50740f81d80f05100000c210000440352103003001031650390095528452070300d003000c0620020364420894140000c000b040115940203c01803802e0401e5844040c0f00c074543c5442c10391a1401b03408503c081d50140c0110000990880000020812200c01441a4030341560f110100000c0b9051002c243d0f00701350302004900742c010700c01d90003400d04c000141401c50401c06c2407401203000d4540d0350070852150348030148003420740c640703000e400f40c4c080d24 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 50394716 1250 50393466 50393479
    0x50c0f0406030c270608030301090c020a0f08090312030c0c070e09070311220b040f0c02030403170f0a030e010f02070f0b060310180b0f0402011e05070807060b040605 73
    0x20b182e45a010355803440c0304000000c0d018000142c0b43c0c401e02191688070b202076940500000d03132038010b03c0c2e440e0b03070080c482c280381031740781001c2c211a881c0042949008250410113a84414190b0340700e94803558820320840354140541c000050030591044003460042d0240f81400d0f40324046e1542441c80c00c0c110341c1182e105000120104003500100040d9582600e600202c4e8214140007603002c145c419003503014001001c0c030600708001d071403006070740650102c28040714140405d1015190f014111010442c003500180c208000a102040e10848080c0452240303510711803504501010703170819508a1204131000035141ca03030a1581410034014800f010642a000b10300d007aa0715a40c03503070700d180d0101008103a88000b100140e00c1c0d54044c030441c00c0d4000c1034601030000701070650b00b8140c803c00070300e41251a68841c03408240b009111840c507034441d5078103031607180a100300c1c8618010030001c1d00198000300001080141d001074500e20207810203510441010070580401400c02040d18403a410250203a074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 50395966 1250 50394716 50394719
    0xe010b18090d0f0509130f060504110a03020c03040302030a030f02121c0903090803040609030203070806011a0313020d0812090105060609040e0a06090f030f020102030403051b0a0f050c0f0406 84
    0x1e01040720b211584241c14552520f0111100075106402112681680820b082e1205030605255800c0000721386000d620030000c0648420820017102d040512026045009000c040e80f4240030341d008020310504c2d030007141c0c10155240d0010b403034040709100883c0001c0402150041741d64042004200a50383d100910341000345404c44a200b001c6150010b0200316154240981810b000e0441c2202a102078070035280d503941c0301c40c0041c00f129450b2001324040c0c850b21100155403d00840d5160688520001c01d00c03003501002d010b0007a503000509030394200103400c1040703c01603407010000e210440c8111240c580302c80b14501500341050004004444a904010401001c2d60320312085600c840c00c00c880005e00070545aa00320314020840c82c0c01030186207020490000d2011203184040b0283c441c0d6591003281c03c108000724241d000680e8002c02180050050520b4050001d8049407002074100460b41c092403140c90381d25080300480c40559040d00036003c0f45001c3d081c400410052b07001c05442c1401401d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 50397216 1250 50395966 50395981
    0xa0f0f031404120c0b100f0501020312130c150e040b091303110106050307180b0a0303090311010507021c060e03090604031106091207090f050610030b060c010e010b18 73
    0x10240240002d245083c030000c1c0c540c0c0ca41c080e01c40540c04540108a000342032400c1d50742011555003d0282004042c00c000000236158070000440d441402060342e01030440d1121440555200007449040b034000c1c909807404149103003101c07114501c00700b40b59121a0402c3c0c548c0107100031103030749110182c0508021010803008104409540000543c14940110610102101180100481e42280f545401141300c005140d141c143c250001200840c0c10400c40c42d10500204150f12000f0300c030040c046100010300b0404034020041e0316030f504070181015807a080d55a40043c82e00405107082080c0c0d0741134281c62000f03015a521901c0e0b140d0f210a4015807a280600c000501c1d02e018070720008281c0b0750800b0002c0d0480c0c030381d102900c201c000d024000d25064a40080500c0d00c03107040f402071072003040c0b0300741e00340b0f40a55842c0259409441c01170118401c01100450480242550310641034100b6030420013212070050074442d03640e001450307a000091302c1c1800c070100301d040d000c2e0748504005c030300d40c510901110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 50398466 1250 50397216 50397251
    0xc08060a060c030809070f06020303090f010507270e0a0f0501080304051e0a0e070207080f01050403090506071106030c0408010612050309100e030304030311010e01060e060f01030f020a0f0f03 84
    0xb41d805051084043e92a40e0807a0301c0d102c0740d90440030803880c01d81800140b960f000800746001d2150b8000307446140c074034078445a0884104030342d41300c00510140c1d0300580b030070240c41c0c42454a01c030408a00d40034036102c1030344040042c8180c49005a140c1c3e242403100d9624114454540501482c00c0a1450300303190100041d010705d4030780b000c29100f840c0700349017081e9941c0701a04c1c0402840070030340042c0d161a2600d4044e44420a900c6900c0381805403041d0001c1c1d80b0810311540e84a41d5140d10b59011280c101000c1c40f0701c5820048045485100915a4030030b6596a01c006e0362207605280440d0740d03260700380b1400700e0a44620794841c0c601da5074019071040020340040180e031142c2d18296826920707518054000c41c1c48000c101071098140c00001800f000303059003d003030341e82c3c0001000002e01036110fa04081c1401c807941031043d8158126100b01140c800c2c0307008003d048206ca4145400305845d24941c29410032640318520000105000307820f00802c44d40c01c01c0c00c036908860603040070012440d410352007004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 50399716 1250 50398466 50398487
    0x121006180506040512010b0901030305121005060a031d0708010e1504020a050909030d090309030b0711100b0103022b11070c0605031e07090630050603011d010c08060a06 74
    0x4034036807010601c103502100354003503c070307d83c0021f08400301543e6a040180140d84000c0c15010101d16410000708590640c41c1c4090440e07401404480c504450303140110002c240c490545c4100c02d5003600f002c000f4540402460000c2d204c6c500002402c0c9040200c0c103032400c000310040818442c9008100300150342c3d41440e820880390240d0b0000400d6642000c2603045126407080800071030315040c001001d0661004800c015240308002d25401e43d29184026100b850040500010075172069542d03a195540c150054100300c2070606000d420003480e441c03a82090f8032400115451040358221110a201e000c0c02455004c407410500710f40745c010191030b10740b41c40001e801014240f020002c00b04a00c41c02d0380216144480720f200d209200f6040c44440180002028450140000c812079100164105d540503402100c03800b9030740e10400c00c1140b025281c05001d0082c22503505540e125402d096038819129008540104580000b80382d111443e0301500c03200700604442d0048140311000d202d550742000400d034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 50400966 1250 50399716 50399719
    0x8120313020301090503070605090c040b0f1003060f17010c050708040909080d09120305010b030c0717041d160509010e06160501020f120a0902030c0d03051210061805060405 76
    0x864001800400d0242016040081c4a80b000060307c01c1440300c642e0019000d007050002b1303200c81c05401c4c010401a1210f12604036481070f0203400000d8185044035a030882807425003804036110703549a59820701e030291a0320041c6401007120944503045000c0c818020109642d080060611544d5150030a00703000e503000e802489036640c005030052000020542c0c0742000302000c01d00400141d403a04000031065080b041c03011905110020842c0e0013103900b96842900110840c43c103041254451049203545182642120701080002256a1903c131009541da061070b8a9000654240003c00e0f547d040c0882c00b681040010910445104c0d81e40800382d2124280202d0782036071507a0000c0400306003070b007440030000c1003503200240d1104518000406041c4000801c2d0701094250340f14008101a2000401d0003541900a01c948036001d1610b1800820000c2c041d2030b15034245000b4413140014000162039200f4803c000c001d003040f445902c00c0d220f40c410b07181d82d1081c584070352801c404030300039020f03500803c4d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 50402216 1250 50400966 50400991
    0x30a0809060a03020c010606050d0e1f1505040504051e0a020306010e0c09132405060403030f020f01060305070f080d1d0112090b04021801030f12050c1e07081203 71
    0x4070b8505100780c06079182950403400800c2429901c000c060204d6102d0000561140c0c10041c0c05079014001180031982400030300b42411030850301540160041c03020310741d00d1207441c800a00120343d60305c039440b81600c5a44210000d1150080018000302211800c03c1c1d95030441c2c1c46950240d005071800b04e04141141c04000000c10030f5107503421440413034001d07100b10a402054260030040c040c1c0c007130b404c50880310710490001540504031800d00030807610940541600b00b2810041040001c0c8101038010807051684191111407003001d0b01d007421354201d54800d44050f4003140c1c0601c00c03041c0482000e00107010000c001c4c4080540c0340c00c0900385440c0e004810001020816400c490350340909022000c1c01c074840010018840c40e85810038281c00140e40c140d00804000403050344a0003841c50f558160b03608110030030010310960740c4038006c06000075207210400c0010711070000d42c02c1c0d04004280e1100079011804401984240c403030352422049a1101444c6d03803140304d41c00d0103023004008403a0000700c1c51040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 50403466 1250 50402216 50402227
    0x130b07030603050d021f09020a030212070f09020c150708040b06060c030c280b0a0203100f0e060f030636030c0706020c01020604120c0203211305030a080906 69
    0x150020101c41c2d1029120340034810a000441c0c0d804501c1c400171045500c81089600c0c0822800d60440c1c6803054002d4000300141418400345c50070b50346000d500c80a2100301c9044944441c03411510010342c8c0e21074000c00c0c2d0081040c0048000a021051306090300026030901860499070042c480100030708050300b5810705070082010790b11a1801c848004000d0b0b0120f95031980c0401c2c2d415030341c2510440c9102c2100f031211040901c481d1a130400c2c0c440540141c252542c0c2d03122883c00100a61000d0506134030000d41c0362000070242c2156080c03070001c00d841201e15510386086014420400000c111440c0300750031000030040111290304043e14112120603100c03c51044c0122686480400d0000d10080d612004c107065810513400204c0c1010f40349158291032a214480c801a42d4030305040d64000e0401c0349203080e4440d4070388a80d01c20300181d80001d0403548480f20340078034680382080c06c014445c030b2500c00240c034500c8159888265001000c0c1030b4000d02581246485000c0c40b405046c080f980b0480000030b5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 50404716 1250 50403466 50403481
    0x60603040501111c140403020303070810030c0308070501050609040203100b01050903030301090c090b0c210d06030c17150c0715060f030308010b0909150102030c15150306130b 77
    0xc000d00d4a43c10f40314156a9540034480d00e0a0304240181000c203080c24080c506240040b80082540078680c51f03001982107459a9009a40030703040103000c0b4820f030354401000804910042086c80c002d5010f82001c07690b1718042e09003a403c1d0380700200f030030313000d481c02e20203210041e207000840114040e820800000c96840180c012600c074800c0d0040682d052001200100c1c0392000b60f40411050845521121044c51b0341d00b4042c01c0b20b000f4113500261f2500424190355900202c0e140c4000340c0c6c848070610314580010f40010108a8030389800a407401841d01c90140858090900c2c00301460114038010310341c04c050f450f0812074400c002841c2c2541074102041801c2001003000c44801030340c100d1081031205a4840c03c1243c10f8400a00c020b900160307101000081000c04c00040798281d03030014050159a6851030902c05449240c408903504511040051803104101803101840b040300303004e1061081d0902c904035038460401e4280b8148660442c00034480150074500f5410492580030801c40c64581d280c00c07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 50405966 1250 50404716 50404721
    0x1020d0f03020d1401080607031b05030411150d14100f0306020f0702030703080703030c051207230a0c0c060512150a0f0605030603060a0b010e060706060b1b070506070308060603040501 81
    0x1484100d1300710070003001081000012400c03620482042e6820801310394030194922825403c004c4800100c0c10420101c0c011403644000c109a005010307280e00552060304100c410164000040e21900c80e0b92912500104840034504c4c941020704440400540ea0070031300050b200302c100d880000c1c44980c0c00100b0048603210312043c0c4442c160010309a03280155203003004ca40f130380d0102d4070880019203441407041c1c1c50f90007141550407480110918450a40d64075105403009481000209103078042504010401d40100008221030030050380c421078100c50b07a241c100c010703220b15007081b02070090610180c2d40405088642d1a400004000b84a0035001f191000c9200e5180e590000d0303185400c501404204150032000950041505808840715941c4a40322403080703860070b11180c0d00140303041e000342ca241c3c42c2003c05003100d50b020700400101c06550324040101c0e91b003c0740314200386103040e40811540f000140104802080c05542d1103103422901d55000b0103011009100071701c143c0340400428140042503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 50407216 1250 50405966 50405981
    0x1107050415141507110102010e0f150604020705030a0c080708030a060e090708030409150e13020907020d0507060c030906090803060a0f210215030f0f0601020d0f03020d 74
    0xa40108840d007050350a400c1828030301d01030b03280c400d107080c50710801c503040c03049641c000155260710b020308007a080d94904440c440700c15604c504564131040701c0000e0410512070103001c6000340c40102140e2a10b40e856070003031f4200a00540c0b00d00e1060152802151000c0200d462480e072918040c568411145070071a030341d000e40000508140400320400c05014043d40c818001ea5005042d81d4500c0c0ea5000d51940d903580c5240240b103d5030b04140b204101d203e00ea5044100140d44685844541c940c542c01c035403a0524049894090324000c01c40144c040d030900c000406d8200d60148060443c090081034068414030070b04a0040409507103e83c91500c4074801c0d03100c0c0011580c490002e2240000700c5c145034145410035182ca0740b0441c400e5a001482d0301d00107081c08211480381d0b00021640113007040304001030b8402d8800703a81190b200b12800c80d1400e02c03100218440e6008224500c1c090400d11600032003074030000c29007410340d03000e1a201c502c41d54004800c410b00d00540c3c5000347c0e03a4000d18003100090301d0750 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 50408466 1250 50407216 50407219
    0x7030311030715020306090a0209010f050a030b04020c011d06040c060e130c120c02010b01081b070203030d1b032307030b030703030c1403030c030f04020a03020d060203070806010816110705 83
    0x100c80d003c0202c20580d0002d6000301401c0f04ca1042c03039251411150120b10601040c980890781c0d024050300c1341c4e400fa201a01291089081c0003a50807441c0c1c0c045026a405a400303d003140e559031000b8140d03210ba1607a40141d442c0c0403001000246001d0f903c10804100c82d004010902440d03071020300081d80e0705580d8110720b540c0281e0a110314011198050b00b080001c401d6402103d0808405039401c41c41403140e03651481341695242410703124100070b841c103c09030780006107103030504009150140c1c40410007056071080c9042c0000c2da640c1164082e051104020001200b01401e00b01c560000043e4401c140403002104881c40c0001e0301e400c00180e000b400a2540c081c1c140c0241d010000526400100301c45c2d030b06014403904001406078082e01610b900c0201c3d4482d04100c001d0000c01c540400b41c0030b8299200e40b014001d407850b00d80700d80029550307603080300003200d82c2034002041003602c80e8803501c030340d4000400382491181400c00501003034004680c1580c040c1080f43d24891800b80000403c02e42c0000e200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 50409716 1250 50408466 50408483
    0xc020312070605090f0d1209050102130b0a090504050105060403060b0f031603030224010b1b150a0c0305150d111003060f0f080d030f021e09010908010e070303110307 73
    0x40c0c519100010702400c82e50b02d00c00d401540550340220f48041804803541c0c2a69540c80001c07481f81440304014403814a081d5901e40d82480030941071140000c1c060050045916482c1d1a070101481c000d20a0708180c010038066030a000041080c0d8803000107a4003926441140030516841242c085039800650b0b090155140c40b445440f0000e14202840f440281c03402942600c08a02c80906c0a25188008001c50b00c1107440140041025458400c09407850310054900381c03400c900c82540a03840c0c04000d2a0a6001d0300c84802405084600e0b841644889581400c0a004500c5d21610005043c2e410100c46070058051075185000c0040c5a40401c401050007804c000c0c50014581006009103003900440c40c034002c0c80d400204039107000200c0c000454441c0d500a00442c000b42c682100540512034a0158a54091160302110324031192080c4180c00100d52060b11209114001030141c40d00e0313400004264507121455240c041c021500c036060700d4044c10904481d10034030360032602c0c5206800e0003501681 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 50410966 1250 50409716 50409727
    0xc0209042906011b050c0d05070305030f0406090504090210080a0e060a02030a05070206010b0a050f1204050f160e1302061213020906010e10030c0e0d060501081e030a0c020312 77
    0x141c1c1104214007a200c20399607078150f41d1000c00c0c000403001c42c2d443d0142083e0b1207252400c101e842c2c0b810710380c1902c1d8440e03800d0b92441c1d980d0b56502c0d0710715008040b0282a14601040900941d07500050304002450308560502682b40241c02082c1101000c010400420940034009100b201483d000040720040341e030b003100d83d0b0340b8000140303500a40050700c0c0111440d0030040030034841440010218141c030f111400030303450180d40e1081940d15511014a2015082051254251043c2900c8040c0d00c81c60050010303240c500a000d01c49810108000b41c03071164240f08400c10b0100000242c40540d010403194484c1c00a1303680c5000043e000e018014018184452000810110300e03103a00d0078454035407082c4c40410481d00c035040191400014070f0421500301420701180380c200d52080d04a000070030f107030741008204841c429011483d20b003010740c410b071803280e2074000401400703208200e02c2d00621032018102c50208000c4285c9510380c400d40040d031007041080c0c0e8868080d07540900c02c039013244115140a580d81c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 50412216 1250 50410966 50411033
    0x213060903021c0c0b03070c06090f020901090509120d0605092e050f0d21050a020c0402070804120615090506011b0210140904110c0d03020a0c020904 66
    0x1184601049002e01001c034101800d03020f1006180607440c0c0d1040c141032030981482804d9260f904000c16840c100080048035001040e400d2152084540c010314000201001500500030480c0f010b03480101594907040c20090848008600030a101600400c4281d6a05400104001400c2d1a8010580c000609402e0018503045000400e0780c02c003c030314044403510f01024022140c2d991038440c0c1e0b600489840c108016610b00300210003d4280302d41a0400000d82503001d10200c0303410703c0c90f0b482c0410000100c1c0310102d50100a1584070181c11641980360103d66603409076540241d21030741031034210007003d1404008498000890680c402d10402c00c0c295a41c076003500280105407911404031380d21005000c0c0d0f10020138901c6041c5a000b0301410420711200c84210b8402d10f80d0258102c40d80d02c207015076402039599000d009a4044400b00e020f0301c580401e00014101904110041c0c207243c41004116500d82d00400002c110540445043c030450343c0701d05080c00d011502444c014440c0342801800b01070b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 50413466 1250 50412216 50412227
    0x60c030424090902160206071401050906240d020409150e0a1103010c080103021e03010e030414010203070b01060f0504030203010903110d030e03040306091a0a050105030c04020a0f030c03021306 85
    0x5101e03a6942c42440760742c908509003240309142c203041603002e401d1111005810804000c2410a104594007815032a2460350700d401c48000f81d4500c142d6030060750070700c004011400040d10a14850301c003100c1e407079180c400000c1d50039101000000d0150351030707442c0501070107628680c3d800c03404c01c1c82c2428002c0d80c0c042c401ca16180d031101242101e01018406070130202d414144260004800c072500c1c1c0030b09907400c68080003903011448031403040d12001000124a1501c00380036284805010710000c50b01d550600c0c00c45603a0710403542d030071411580140003010210b040c51011b6030440d8114100380500300300164084900b4403c503040a5050b6083c5080d01e030030940c3c13100740c8006014440b0150f03800e281540302c0c01c805881401c00095200d0b40240b00a0000c10342c0ba610018034944100000702c00483c080001aa0b40b10303041783d0307148040359100010011400c3c00c1c804c51074403039000c481c11490309980c40700203084842d15002001c10142e550382c04030b500302e0299041310300f0103002d039004c480e4259840000904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 50414716 1250 50413466 50413529
    0x1409030a080c0906090f03010b13060302100311030a09020a03020603090a05010b0307120b06030c041e060503190605091236060a050f09060301060f081503060105060c0304 75
    0xa01c0700d0002816000038103003914001c000050030700c0c0c902518201080307074010007600003d516560f01d40f8910341558844252080701c034514403011035414994010091500820580b0b9402e041c10112440d100201003811683d1240713060b032000419004a0020816007003558000a4000c440003060103045900081e22140d01889007000b801300e41e00f60000e060300c0e41c0340340c4079001c0c000301c4911228000803e40d003400c0d54411005000c0b29000281c807070010741a5120607101450100c1001e11241c9258900d000301d5028040903070081c110207540c281204a000d110b80e40141240d0754841c0440d0030700c0b800b030100e00e4041c1c0300c2c15581500c034040212180002c104810001021401814540e020202500344612031044010807460603c1da041d4400e45040e4041490240042c10820603000544e0f6014080d6000c1e0800d80e071640c9910030484809420810050720300018a182c2540d5049555000200107055400a8a06680341c00b0b15904d407910b107020b99081000d56400341840c800407032082c10100d0a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 50415966 1250 50414716 50414737
    0xe0a05060405101a0a02100203040c050109080a081b030702030a0303020c0106120213021b010905010213120b040816060501080c03070f0602061501110105100302040e0d1e0201140903 80
    0x220b25240c001940e89011294070511240000d0019100c1c070341c1e0002d1000d40680310160059401040da000500c0d0f0032a0700403142151038541d40704080c0314650703104402e02c018000300320050046480503152001326010310500140058105141030407004003d0083d641302c198050103c90b906805441c016010f074000720320350748440d0301e80280000d99a9010032405042500a46248503101d4040241c4001c4d6104503000d0340c51041110504454990920919030001e02400c00140c69032000060000c45402c03d902a40203285015070f100003041e06a040c2ea5003140d8041d0180b0382da4101c481a500300d94500110140c08103290000001c0d401002246a01100c5411816542100d4452414450000c00d40c010000103a10003400184c0505140c40390310020601410508a05050003e0241c251802242c41c0c10041885400420450505004503007160b9840009401e02c4031464000500002c465131400981d04400c510390389000d4001e5114000892034044001010f1401c00705903035690740300040303c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 50417216 1250 50415966 50415971
    0x15050412030902010c020402090a080303010609261902010e0a26060f0a0b030309040903050909061005070305090a030f03020307030809031204020f0109080106081b0d03050717040e0a050604 83
    0xc0e1500d1180c420711180c02d034140c40c1e110791100d1640900c4001d403c140250b13600200e01c0a40820300a50420145000348000c0d6104a02c20703027014050030440401d00d1030b40801210f0940707810041c4c82c0205090f90115802c0d5813900802c000c0b07000413a1140c0040c0d5116420150070312000c940c07070758036018020080702000824809000d98910301030b034840084590170048140100460f80e44d0a10f500b001700c0081c4002d0449081421440010341100c0200300d0440c0803903000109142c960802006096001101f00d0f4040f5020300c201a02812034800d4540080c1040310000c0c9040d10342c0ea51451030009541c1215107a0b8110300c0350700e4043e50302c2d40001000d40200303500300f00048031902d0020895541d440b03010704098643d221542440040c04421741980c1c10701c0b1201a01180942091041c000107050941c001c04070300c45456401704d0783c0848240d80c7c03800781d203202107484003294110003268a050381c0541303000120241854035048a00560700310400701c07a941018004098042e8002ea0301035507048608 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 50418466 1250 50417216 50417243
    0x6060905070e24031803040504050f07020d2f030403050312040b0a050c07020f03012a1202040f17070801140f01140a0b0c030405030618070b1c0f0603150504 69
    0x3031602c0d01a031010840307106104000082d2440c00703c030b038844400317000c2c0411a801c1540f80da0020381500e10485007424007024100c10811241d50401c440204030b515400e16008640d05d0f2480144080f8415804038400c00c1c44505000312000d0400440c1e004540000c1520b4482e400891100b504507401d407010b03140b40c07548a000c50103403140d5214850140c41140c2d18580f500300d5560a000b5407500d03041001d40c2c155a0f6a0300c0d0b1400e0b00d01c0f607031400000d856450380802054400314025004d1030340e0000034030b10305105007c00d1000a42d00381e4510142c44580e40a01011f013112032805240c103001345c000b5009542854640c3c107440c0ca14003440350040740200c0007046140c5e21511034060f81510110403590101c9084d038200041c1d5221001010380d544410180c2e460180c44802092600405943d401c000c09205001e1440c0e140e41846440701801542c0c10702c1d03140460802c0e0300d601255910f0b1100f0541039945a9841c1a0307200d03075002038010765001c40c09203001103e0f0040200102000c07101a680031a44440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 50419716 1250 50418466 50418499
    0xc0303030e03180d0f0605180d03150e0c13030b0702061602030304020910050307030f0605100302030a0b0702150108030d060905010501023f0a021b0a090906060905070e 74
    0x191000a1071440e00160001c1c603c008000407440c4140c02502c80405205034400400c840d40141031049804039240034800c541d0040552400d0200304200003010300d8111401c10442004490f04111410040c000c0c11544841801c1d00540c0700f1b41c1e03500014a19441000801c0012500790680b040e0134503025201c17a9524801100100d0a0140b00900141c00070800036006190070210300360002c1542c1c00c0c01c030380f0390f0715140402c2c640102a0801e03581e1840d88400ac504000042c000d65911109841c6c48603800c52861b80400e6440d0102e120040440d07000100090402c1e04c01c10000d0300e14408400d000704a965103800040d181d41c04085c2d140340450a1a102189446050144d20704950040e4020080318240182c081d051402502500000010f00141c0e08054a40074244548800d807042045a552186180281c90a6900503040010b11301903411203035599100b61950003183d2080c3d0002c107050015281050041c10527401802e2140d10340402c0c485041d500c806002e940070707010b40750307510315095181 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 50420966 1250 50419716 50419723
    0x90d17060105070618140c030601170606010807020f061501020f0622020f040606030506011d01020a0809011b05070801140c03070f110a0305090a09090b04030509010207030507030c0303030e 83
    0x3248107000c180100400c800003840c079400354203100b000031a12449181c1994038001180c01d010f61030580c6612030094088245018814180148842001032000980c41c5007545d440d07190080130541403103a51000a80254000d000c01d0784154100c00030303140355107003841d80c004803001c0290350140144030300445005006000103009008200701e4609a80c0444603013021b0f030b155aa00714040745c004e4200c1080a0142d203d5029850161249450200d46803901d2000188244100003044c2629408030f4880c0c00c280c1d8001c44c01c80320703040c0c100c031a45655400c203000582c6c1e01100f01c0100000c81c102040740605009001c1810702c10384044034024001800b40b001c06403015001520459102041040880c0c0130318000c03030003180c0c401e209042200080c0150041d85041c03001030401540411400602c20505140941c4900c01501100c8410000108140c94000c01d44030000c00043c2404000280c1c4081d42e03008001500040d0b0380a002c903003500d070b100e2408010381d0505120440110b410315142c3c0f4000300700031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 50422216 1250 50420966 50420971
    0x1602010c0905090c0409090501062111060a03021204030801182304030201060f080601030615150c0606080f1605030c010512040c121109010506030c040b1c0203090d17 73
    0x19901d14401d40d04001c00c00032941005070641280920800000882c0c0c00e040c01114880c50042000091652a200c45000403843c9414090741c00260524100001000074082c07454031641500da05481b802e800d001580240b0580343c481c0400d014640c00c100406070300908043c16182c0c02c00e900000410020074607825102000c2d1a00d001d40d5800c80c03d107806034020381515603c40c1c0248004180e035591240c4181170145903400200c41e5070005401032043c494180160203964060b1241122440c1c5403412503e142511114281d08002064001c10207100c43c5400c100c000d82098015104a240d564080703d9903201600c200140500d8003140015051601103040c0e1904503041c1c480c20700d421403640c480b000c01200200b04036144030070b8120114200f1080c00d0242c2e00c040c820000c102202c2c2500040208110050340111b00c2600200104a050381e0034000b56401c40d540d80c09a80e81b181d0082020001054020f0080c000003403000c03080200e03a0900041000101e2040d465841c4000301c04948031400d400704 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 50423466 1250 50422216 50422241
    0x240a0c050315010309081b0d02120717070204060f0605071b140907180f1806050114180d030302030615040e06010f0309020a09020c0118050d08060a030b040803160201 73
    0x10594001c0c8194066000403070b031030744134500b1b480c07803c50100c4064500100740b140c0c00c0032076440242800d620907010043c00306040030401c2a40e0800c1250740e1080003075060500d212491680104440c400c41d102c54108801400d641107415407003540b559801000e80e0840c0c0703c20350340c86c200381805081c20078141c0a482c040d145541d640c44450714054090104651b4003030012804c00c001e0071500400d444140c004178000c0c000305140010624501400500d02c03011100030403500c0b0389040820001750ba00715244140c4444207a02590300d65050760100300b9601c03000841c8940290150017000c0825605500071413140d43d04940320340f884100084949414000c40c05680c1c1c000c404000030940640c0140c29800d110240c1c1e00e400710700501d980d80480c1042c21190700589450343c01040b500914242802100080f1000b0060401120907076128150f658420f4200340041c404190041242512030b0b151040c040e5410600070203441c181441c0101003648211031100aa0b0b0844c01c00d4070215106014441c1c1000c507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 50424716 1250 50423466 50423491
    0xf060c060105040504080408030a0c02010e01030513030e060f0c0c1804050a030309140114060906040b1507080405091303030606050901120b03190501020c0106080a03050301140102240a0c0503 84
    0x2e0900748801413a0280c0181c405140c06d0000245aa20410041102c6811562107140362040340c40090800c0300200c40309814582000300b002000f4031504107130103000d40c0520f40702c202d1136500300110380584079600742c043c513040000602c800840f10025020034100c80c282c1d0714200150001142e10301c2124180d6000300b0f15001b6042c1400401d129400500038640640f0510032000c200c21112421030f4003408100c241506010200807287c83c08040b0954054401d0303174140300501d0000c000500c0381000e140003001c6a40d010030341f04280041c01d410f48002d00005041c201c0d050034440030540e5080c000302411000a03007000408907841d071240e07058602006060711200188503c0c4081b0030040d00000d403150f6003620644020182450410110303040780b90040000682c0c4035014030300700c0d080d1490358210325810350100d440e03a000a98800308590440720108900242141c041004074104035284803002c00c440c0e2a5003400c20342400121043d8011705140c102005101d55200c802d5070b16000071141c00d000d855 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 50425966 1250 50424716 50424719
    0xa0b030c040b03060a0e01030506060103050606130302151902060405071415070609020a0f08010605040203131203060506120a0c1805100203040e010e010312050304050c040c05070204090308060f060c0601 89
    0xb20300102550f0003801c0101044682d945601c01c1e05248502680140e446a00c41c000748011540c06200d0160071034000d03113a083c90300244028441c4261141c0c400240a1100d1802c040d001030b40d600151010710703813103804040c501480c440b8001c1d680c520076202955540104035001034014400340d800301000e00040d0150413100e16040c2910f82d10b41200e50107403a40ca07240c0d0b03500c0c00140d0350181544081c0c07407482c2400e044075003002a900d08440da6504040d0017127204005100c0f40c0d881c50f04080c0d180d01d51002c0c4c0428603112920088014110550280b038210202040c0050b030b1070140c1600030b1060140c1541049017060a100032500310303290300720b0304c6420300f81aa01807009040000742e00780d02e00c800f0300407245000da07980b03003030003213090241c0c0a1040d4940110060040002c8048402d040b1b80706031502c1800d608043e00c8482d141d0b520220410702c5941e4030001c02405e0b900500a40d0903842e002442000030000506000d00088401c8402e0382c03045203860101140c41c83c0c80c80680d0701d050b8100005001070fa = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 50427216 1250 50425966 50425979
    0x110d050105030f030a0906120e010f061503060b0304060e0a0606080d030b040b10080a060e010b0403050d05070b010902031b03102105030d020c07030804031407061103072301020d0b0a0b030c04 84
    0x61012300d0001001755110b001d01211100b013409401c131041c2c03032918000351942c0f4080c40c1802281200900c24201802c1072802c100e2038040710190b03074026801020014244001000c1149841d804800081c000c500305040041c0a00c17000ca5a1588034405031401e00c942ca8500c0d040208503110385440c00e0340700d610b08000186441c850720f10158404100840051095210383c641500c20409a008502d45400080d09100f0400e050162030030285181c1001d41c10980389950744145540305014003140e00b603012000442e0050b40120310b0910344400030307040e55a8284011051540030a50080c60302291294031414120703c2547c04480450743c000010b94180303400365040c20040e5000c095100030030702c2030180110100d20410300910086100d042001580c11b000c914050800c107455110106020940d001c00c0490b04002c4226001654003520040c00c0d80c8660741e103da4400d140c0c15400c601c135031000c5503a444080d032980c0b251046900846000300307060350f03c16901c3c0c0c69100480b802ca68296040c401088034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 50428466 1250 50427216 50427227
    0x30d08040203070528080c090c0702040b0a0b0714030901171f06020a0b0901110f03130602040906080616020d3c08100f05060706110d050105030f030a0906 68
    0x8a44002c080e5aa03266a420000300c20b00500085002c811400c900410303084079000002c0001400c00b00090020821610000341989030010220522600001403800841d540c952107040440f10003000d00c03011544400f074100b20380e044040120303070084880402080411002003074030320491050350740e0001c1100c1c006010b0010140a82200d100010500061203070441e4800c005000e010264001c20001039141000d40f8481c4010300f540c5101d07407602d11304030010500310b400c492030810100c00c0c0070350341d8465110642c4034421118018011500c08600403070ba00040345c2000084540c08011240c4c00c0d200d0303c8544c8031451594130a28050380c4140d0080005074025040315440c10116900b0380b0a00c42125000155900c4d0010084200101c101519440a401614103908203001041000d095428081180c0c0c0380b5001d130181c10320500001c640c05c002c01110f90889038aa4218580c401d4a070100103020360003408007070081501c42e00590380301020300000002940c002248aa8800c10003501c1c08a05a80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 50429716 1250 50428466 50428471
    0x305042604090f0b03010906021207080402091303020c030106090209010906031811010903050d0c0204061401020d0302030901020d0216060b01080405030f0a050f0c0607090501030204030308060613181a0a05030d08 93
    0x2201d03116501e03244c2998081c030030141c000e40960009a070b00c5020070340914482c5c0c40204001c0500011009010150b1269521281e2003001c005400c1007290160505901d07010024030002c0e810743c01c10001140b010b0080d00640502c83c02a220010410744810b000c2c1c05840c400e11038200c484c844510200081861900202d10340d000604000403025281d0f103616041601d01100b21002c10700402c0c0b100111704041c4103400040c00b0585820030400206e40000b5103400c0003661000c01c160f0048007081d8503040039070440c0e440e03040261045503280300142c0342d280c01304076060341590040e241107110007955000e600090b20481d80000a5442c100680c2c2c0c80c400141c120f89d0180c000c01000f84001a031500e03030b840040001008000040080f46440000100007800c2d40d000681054010b21040001a8102c20282d4000c40101c40068071507001d600d00c1021a00f0039400740d07050441d01d400d010090007180e844a0064a884000d52103d8413809050040040c03162140540560022110004c1176200b40c0c40c894 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 50430966 1250 50429716 50429741
    0x31c0305180c0d110a09020319050c0d0903090b12041202060c04090905070f1211030f0a020d1106190905040c0806100c08030109140a0615050f07050d030504260409 72
    0x130300800340d04011030741c4442d0940000b15481d50000500c01078440c84000c1c1c1d800600000000e01140ca801c07001245503002e080c02c507e500b40e0f151569101014080c42ca408041c210500300580c40f0f113014142c588a20f10241c03800c0d12540001c0121011031417011505603c0f8400c0000c046191500e400013103c001d000c280416503040c043c40d0030224503030001c40b00400c0200f90300c100c4102c0c20f11a0b42400840101c44400f0a4400c0c2c0c403402c26a01001c0c00030130900320203a0116886680100b0714101280e0316603100c80c00c5503000034009641e0103181c8158207840313155078043e41d4017003460340c0f11410300c01259001d40680e40420400d00010300c480c5044002c1f0384520020345000303040e0341c100c0d640d00744044c5c0081e04110815034494080c8801d07003e006042582c003102035841404000c0c07810300b040c081e05c0c0241d42e011307040240010300b4040100da440d040b9501180d05c0130841c0c24006500200400804081d6800c8455183d00a815104108051a501c151245c2c8102d07052800c9d161220000003000046a0074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 50432216 1250 50430966 50430983
    0x30f0203040504050a020d0f0b0135070f0f05070803010b1c0e0706020111040b03010b0304050313080a02090903030f010608070309050109061505062b0b031c0305180c0d 74
    0x401d030b5440d140a40c500440d240c103405070300c031840c0e074113148140c5065081c250b1200b860100410071036070748905000003010035a5006418445e5052025402504006a20300b00e089050240011142c1c80701840d80329910b00e03500d8449610b010b000440b01c9108044002d030a8a00620040c01402c007040000d08080c1d0241d40c0e41c1a403c0385042ca0341d000c0c0c603000c01f20704d559500405420041c1c181c0a00070900e0782c82010800c135107050708010300c1c07842602040c0503246000c500440042c040140804c216084a14408580c0c42e505607246500c51382c44032011001c0b0700130101400881c0000b6000803e49020f15564035102005a00700b5208075151031008003904e040640320b240d54400b140003842000c500d01d0041d50f022505000c452201d0b042d00066901060249200300040c90081018a041200004070b04e801800604120746800c009440800500d503814056580384204280c0c0c01c80003049001c00c161028405562548072800300c0c0f420f41115500c07590040c10761021680b4100e84000301080c80359010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 50433466 1250 50432216 50432219
    0xc020603130b040506010906170304030b04020102070e0a0b01030f0b010503070806011806020f060114030a0609020103060f08011d010b0a12150606090f05030304050d08070c0305061501080603010507020604030f020304 95
    0x20141030800548003904c5541051006211600d00c17030041340003401200030302803079060480b810a0303076920492201a042850708400f00d01103a2090000303200a0018900f45020703030400342070100003050001d000e00d0101c1e103085130b1203000380317890b004100202d441611005d080d0394821006607040c0c03100408aa04018070943e240320300085805650b8090a500d500800d084481402003078030b03160301a00020304041c402441e480141c3c2c3d0004400c6500c96004001085107030740c5100607409011140c01c020a80c0f0302c50030f00810050b0055008024104400000c658100c014002c042e080741c1d00c01046039048440194248200c4620b40344c00c4400d90b12030b0316210081d0240284400032103050b0340144000400b007034010040e848803048104007034031003200510314084c40c0c4400070307114440360740340200341d404082a510306116044440034025074111054888070310705401c0c0306440c40e0a82c00030f54042000140803650701e04052003183c0c071583c2d00d43c00400960b26075803000d80d0b2001844c040e500442c0b004010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 50434716 1250 50433466 50433473
    0x1403010506010e10021e010207020405061816020c03010c0f12140c180d0b07090806070f0c140105010303030506040f050103020a030611070f030f080a0b010c02010e01170f01030b06090103030c02060313 88
    0x581b00c50261000041c6c0b54003003441004269040030349945d105507480c00c1c0e40c07810511031507005074001200005a8105841079030741039080c406207850070707540b6528241c804540c0c44d4200030394008901e00c1d6661006111003000182d001c0391407441000319203400031000a60701c00e604800502600c0c004040e0081f582042c0b900140504001c0f210840e5a20440350a01c080140c00004d000d000e005107a01601007450950301c01400e91405204070b60401c4100f20102062200011107801c5602090000f80910740e120705025001d40010f498044c0928545054000c51080c944a12070599a004044400c014603545440000c1d0072000358104440108000c0c5100203808044c5400700c25100b0b03102d810752407020030009022900d00900034a038003804d2009500c151380c0d02402042d4080c0c1e09082c0a041901d03000012106100000541c0c3c10018008080c8200503200c1415a4100d03449236200740000e0b07030f940042c044040d80030f10006001c14006019440181b170036201441d0300c40c420100c640740040540e103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 50435966 1250 50434716 50434753
    0x30c0405040501090902090705070b1302060d020d0518010b091506091c0201080c160b0703020421021003020412110607020d0609060605040c09030b15030102040f1403010506010e1002 80
    0xa001401d000d0345c3d050301d4003c505240542551100c1c81d814554200030040c3c0320302d0100203009041d20811364030700820504543e40e1009840700d400160300115141d2011038107260051006a51440d02c0c640d085980040301c1c54140105102081c1c042c1030a50a0f40300d003a000c18401301d080d04d001d42e000c0000c0c807034034100ba00c451028110990880b0b0001c41600202d00000d0407115005e01308401c011420000e003150b541003000582000b07a40004150a5681da00300d0480c0240280c0d00441082c18800514020f40318a8030490040c446c021284504102d070110425812441680b0035002e040c0b5541102c3c40200e60040b03140e05e480308000e48924908030150703001544158810300c04030b40c0c8a5031204d00000b031090b64469040074000030360b802c200c0c2a8102c0000741910301345d484024644240c1d140003070312400d1144560070301038102034000d5485d84d0321050802000d060700e0180180c14251003108240300c1c501405980d0040d031043c0c460642448044060152606069410409620400b9044d014180a04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 50437216 1250 50435966 50435969
    0x1e071205070f051503040308040f0507060c0c05190b0a11010906060e10050f060a02010608010615021203010b040b0f1204080408072304090302190308160c050d05030c0405040501 78
    0x4038054103032030342400401e01c0102e01a07002036004068140302007440294079001ca0341c04c690182000049640c0303d10345003407101c9102c44024400c0c0a41400090400d40110700305d490079200b1242c0d00e490540329018040e2080d0f940b80c1107000c0d1840f82070100700102619000b0aa00c1d990b510b480c08490520269642c2034a050701c0086880d145c0d220300c00c010501c80e54440c150000c9a040343c2c503001902d8200001c00222990005038860f950008031144028000d5011000030711040700207110055840c0b442042c03031480134001d4000350180c070071000d050120110440341a1a131510500341454203003d40100290007a00305000010000c00c20031442d2070f0b4140c030ba14807541c410041c42c1d9807a400c10000c0d9007402000d81c010305201985610110b9101d03903004403400c0e210016200000d252099003000c0345001d6800500c808412041c00c1c122060503070142440d8840c14540051600b20000030204171001c6840840280c0103400c0603d07500171141c0301d0b100a540202c52070807d281050b45407800a02240d000b03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 50438466 1250 50437216 50437223
    0x1203040605030105120d0e011404050d0809010f23090d0605090c0a050f0a0e0a0b0d0f02240304020108041506080a05060705040b0301090905070b0a050309010b121e0712 74
    0x2c0b00400540c9008602c1036400403400303004d810360101d20070010f04103141f00303091301c0c0c180241c0d245400e0912080c0426a40205030081c01c201040b142d909042c109a03100d407000c05e001400e0711044024640c002c0300d4a035102080c01c111010340c119019541c40072504003c171f05903480301c1c12070340e143c0c0400c11303e0007282c2c0503403d00304c007401c40581140b003005001c5e5082d50004d03001b2001d01c1101c5800c2d64620b21842c0c1215461110a5525610550004000c040f81c82c5500d03400300d81070148605020034003081c40c81040c420342e1140c085141000800c80e0f0201d49000ca0351000c42d04000140040d440741c20305a800910481c04001a4081c4002c20300540300c00d40c118032000d41c070600d4410180034042195682042c018142145000d0410030034228501c0140181440c00780ca80502030200401000b04400034005e50b80c00b075480304025000141035500c10b8510600a6003042c1203000c59180a4540c001001001c00c020700c1d0350610900210f1301c1c18548100b2044501604400041107610000040c000610 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 50439716 1250 50438466 50438477
    0x190c0f08031e09072907060501080a060b030102070b0712060306180b0f0105030303071119060902030d0815040b0418230304080304030b0a02360402030405030706090212030406 77
    0x1a000d00c007650b101c010902840380d48414070400c9404c035880f00c952092002c011411690248403804a81e881c400c919008040c0c80c030705000040c3d11240030503c1100103100740414010071840701e04260a074015403074094200d40348000420f000324011a84040511510000401c01030b99948610044501c4122036001d924407940d0500f04011280c08020750207580c00340c20170100d5050030082541c0703000040954081c80700c0392500041081080049003050001c2c40c10041a02c0050300c0e203140034148450b0308a002c0d105102d50214a68000c00a41d840380300c3c20303510004142100820800544802c1050b1900580d880300300c0b1a80d0489545640328040c003404103103100689403502004080801d040c1800f05410901050254980120842d01220341000c2120819182d00003601c00034400d42c60070103001102c40182e401c124040c90811078802152024030709403105000144070686c8022200101140c00811410000844950001010780d0020b401e07500300c4000e40640307030325541c40b5030003000100343c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 50440966 1250 50439716 50439751
    0x506250503030105010e0d0512031b0a03020a120b010c020108060d1502030405070608010609091508010e070e090102070201080412090b030f04020916020307060b040b0a0303050c01060b190c0f0803 86
    0x51b08080d848582c202e045d0350a0701c030301200f601c905407a40300500003c19160400008601000c545100a4170180410071101c0c2d1342e50010036026009521000c49070000c110f4088848119040d00e1040b03144116044e10b0302d0754003503265401101c00b4040142015444014441480080b0320242450300101100420040c4c0d42e040c50300300796113000150b61001e41045101d00c01407060540c400482c4044401e4004041000345607168201780304542038000004940c038010210003880d0f80000d000b004c403180202508125114508418203030b03c00c800d0064081400c2001007400034480c01c3c203924000d111480c003c50950784031580100142d20a5801865020080050106510f4900e001e07035008080ea540070856000c80302030107034a074025010081d0a669850b106654180c03541d40203428401e0f0018038010f481a140d150103003e075084280c17181000d43c40c1c44004034001d90748604540110031406100380504503414011191450000c1c02140c0c8040d405941c0400540318001540c0900781003480c0815a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 50442216 1250 50440966 50440969
    0xc010b040605030a0c0e0a0209180a0e01050108030a0e040b030105100311010206070f030b030c09010b040602010e0a0f120216271a01030b0d1401020a080703150506250503030105 78
    0x441d05604064400d80200d10460b000800840100f0101c6101c00b040107195983c10401034001d008900c56075401048030801c900f1004c01200c3c001d441160300e0001001345111201d401c03801c0300c0c402d0050980c250f108011030b6901c01e014190300c142e43c0e400100040380c45005000424299882034600315280c1151176010b008101c1c1a00c0b081c4181c0700d082c40245181c2ca05650014000d02c040d203241002d00d5a5507100032000d450078011896440c0000d02000c03420350f917400246001ea8480d1003060010351034103007411441c080c00701d642c0324040c2e00b0030340d0288440300c02d440e0080e50101c520024400d500c15502401141160707a12044000c0444013441e62940040c50301b085d4003d4040a07001205514012a0030f50340210f010030301428150a19000400241880219185c0c00007a040503140800c0d8000419980005400500380a80c5a580b46000c58956a0043d01641c118120005200724410700034026814094040c10010344c1d060140b82c04c0c4050f401800c0d10100f614107056801d07410000c014041c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 50443466 1250 50442216 50442221
    0x1707050d0315060309081306020f0c0411070303020f040f03060b010f030506130e01091a100512030403061107120c020306100b0702040506030124031203050c030f06150c010b04 77
    0x900c11282414801100800300807984140c040c0502018191741d654090305005903042991441c800c05a0702d000c0540c0c9a0034040d540d000a0165440103104490b40c040d010306080c001c0b1072480300e68a00325030a00c0e0150743c0a8020790040d00402040040900000420782c0e1100c800c0401036004100000380d50700c5110004140889900080043c0350801c0103002c103a8035116440340650642110000d1108c1003e41e0043c00762654050181c0500005040c50240b4000c03e104240074030705c505810006a03035180c003408010440c1440680b401c0c0c100340410030100300d00340c0240c4055108905090300c1c10046031b0302d1140d03650701840039100251040d0a0798045040400600d504aa0700200d000c0381d680c600491210148140b403c024041e989401c049541c0b52025000507092001a46400740c0c1020909072501c81c1e02550b10083e81e410107406580080507000c2e208180c020220380c000c452955031800000b002c0341802030030380d580003003d111421041c0341c0d40d1400b400100c1301c00030001c1170401114081209 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 50444716 1250 50443466 50443483
    0xb030604110406020a140309040906020405040c020a02010c03030e1513051005060f0d060213030506160e09070e0a09020a030b0102100e03091909060b0c1c081b07170705 74
    0x181e000d4100030a01426800107112940190300040484218003c010450709500800c0c9001ea08a802c0a258000700a120303000381041d1407081e601002600d2030400201e9541c901c0d4840070380070400348405140032a120343c100c035071080c003247d00301e03940c81c4400031a940481c88100c4040e540d050030114040c04012051001324404840314406200c1e40c104413000a00c20018000900d2042e541424402c08105541d01039441c0745c20444d0b41c4512895580c20310580307565007102c001e00b2a40c51034002840f614001da40b07152803100043c04020a03540c0708c05040d00c0c00b41c0802100743c5c1c020f400034000280c0780c00710300040c00f401c031090703602180700707844070b0006032800c003070000d01d41c1c441d40c14601c0903800c540c0d00200342e5240c14400c44019014111600c00001d41100c503400c080c05060410740c000c10800d051500501100500c00d08448260120028005140d890021040c000413240c0020895030090316000145200c1c0300482c09180400c2a96500e0103c04014405e001d1910086840000d010061007840d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 50445966 1250 50444716 50444741
    0xb070201050c0f0c07050310060e0c1206090402010302070501091506061b0305090a0803040e01360b031009060902010206060604030c05040203270a0611180603130c0b030604 76
    0x840c82c2000300c5004258061100e42141c070707240c08518408401c2041000070700408014003541d86414410410070003600c460301641f100c00c0b010f003020601030f015a0b001c0b601142c409205000b51341d1a230104000315444041c105038101502071000702e010820a1090a440c10b1180305200c2c490741485002c1000d40d07200d90b100c00d05000b80d469680c0d0703e0b58100b1030152491941460403030707540c504503000106600c80c141c0141410303100c08200400c035008441d801d41e050300c00440209400b10294608066500c000d07070780355490340b001c42010103905070031500b0004141e1070060076512704034041c3d0401c00455035000350a86d486522216000250b58042c090039800480c180c0d4038a1620342076481d6000c43c81c1051103802d004560010010303400a003408144c8501c4641811071201c00d0354a00c42d404d0fa03455030303148140c3c0d10030700e000c03d00307003411501c001200e05400517140948580052501003203800d402c0144480581051801041d0010381c1039142e5501928006e81c45035220704080080c80700700e62244800c013 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 50447216 1250 50445966 50445971
    0x90601050303040e0a18050604080a0e060a02030d0f020d02070b0a0f0506060307180f0801020a080603012f120915240f01020709050a020702040b0303040311060c0a080708070b070201 80
    0x14860f44041300c001c0ca40c490000240407420018a204000140380030800141441c0594024013081105480c024448201203950b09002103032031004004184c807420103004050385c010081c1e001100d0103034004c00c0c002034510900504082c031800581040e60f1080c6422603c4140000c1004205900e51140c1d01c280d000d0401b00b00140e1519501140041c80f0241803401400b01400305a070301c09880750000da014080210420710520783d94005a800303034114450301d101140e45040001c1d0f1900301481141030b04d6441500c11011605628245001c851210010004001c0704100300f20304004a4100b181c059407034003009003d514408082c0288021002d00540e0421800074440000688016010f40c1841422100304001102c0703140140e1400a6030790048540307604020030001c461607168041e01d00503000355424005441180300301a220b1059000003003401c050041030b0600d6044c0301d8003600040b00581e044428000382c54642c608680c02510048483d100e000918108100522104e50f40105990009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 50448466 1250 50447216 50447219
    0x1020a09030c1a0304300c140a02090703020c0709020c06040c12020a0b0f070506010303020d0f170c13080f0a020f040b0102070b090103090b0103050609060c120103030c0609150509060105030304 85
    0xc0f030b01184000741001d0442c82e950301244542481a00c40d00d69140500880302d01000c0d4004400340602e4415182502c4441660026074070340c0070046032010b002c0d54005c08141840c0c0d03802000b03900070741011071228028414140c0200b5a00058401003114800440041800e4034161030f00b0114210aa000b0040500c2080785500c016112180d40c2d409540007000d50907203a00329103035601124010780c40060500d10882c0000403d00d80c0110380da084119090341c5002c00d1003400e10040e19203240880040002c0b1031424009031250304a940a027001100120b0341c00483c1c0d903291005880c1c900c440d40840801d030803810a100c2145003a12644130b0b1018150b505000905000380080d4890752039210700001c1420024801d10107a2190f4031024510b6030200d200b200c2540c507420700715902d4108840b400c7c9284540c002041d8001a01800d48028280840089600342e0035680c0488007904048800c9910685131185e110014a09040640541d0801d40001075a4030f40074109910700032341a4840303030003074008100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 50449716 1250 50448466 50448509
    0x807140607050c0d03020304082a0c10050417030403020303032526190c050306030105060613030f0201032d0b0a050109050d020d0804170606040c09090c030e01020a09030c 75
    0x41300b11009500342001a00c0e9a02ea040c9145a84503400e00356150f13001d0342481144509020f03010913501d00000080f0313078142410030288010404051111004118280010081225404520b01c40706808005690905942e680880d2440e001541c00102c21690400c11503000201043c208103210f04d1850000140751034114012440c840003620118000102ca0006114803030034102801c01004910080108440340da400412541042da80715103e5424400450610701d0481e0603200d040c0030b040c8032039500038910b6075001c1e5a00c0c80400224107141e25030360a46907a43c0020070340101c030b20034500100d003c0655094138000700c0703080c894002e01c5400c3c14041403113103907480300a003404d41d00203480a0a004215000003603009803580e00061190320300041c081820300282c82d09040441c031110880f4869101c1d0300801c810344500e8007001c40010101e40c401c001c0d0101982103040c4940b424180044c501c079072804003500366485505500c02299003040204100903a41c0301d80307001000090217486020000c000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 50450966 1250 50449716 50449723
    0x50c04120b0601030e07080c01030b04020705122203030305070f02010501080309120304030203060705040501120e030316030f06030c05181302060c030f0409060f050904022b0807140607050c 83
    0x40030704110041e200240d110f9019034000300d0b40602400840d05119a00da20055440301d8001109000138200440360740141028002c0d101907541c010042c103200c80190350b807651250000e101c0c21301400c0e05c880c01d01c4040040f9164a00256001e030f41d01081903d0640d00190000c80005003070400c41e03141500400601002106450341c002d000ca03010304002c0081000686140a547c2010b503050040b141070150f41508030008204031002a00e80105014600d820b0004442450071a00500d4004100003905010032030305c54107941ca0142000910304482d40c00175012100725070011101c89941344414840351030400590700341688200c0d00d00109141822000301c01d40d8100070020301821000c101400e0200d010f10503121220742c17112900b03071150790b121076000241040b0700c00ca82044005143c08207103030400c1c4224a111b10b40182182840c0362160403100c085d00900782c0f904084650340b0f90041c00040032000103003403d07802400b40280f84900302c1c081a08003200641003500340001009030743c80000380030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 50452216 1250 50450966 50450999
    0x1021e030403091e08010e07080c060f1909170c041506090e040606170115090c1d1306060201051608070c080f090604030303020705060f060d0f05100e0d03050c04 71
    0x81121344001c45101c0d042c8110b000d265000b40501d94200507440101c2800001d280c01114104011036030910203c0c07091045900c19021800400b4504010000d0400c031030311091030280c5041c1c40c0c084440c9a80704045801060702d03103040c00123504800c1284095250502606861000c04202c1c442420f150100c0a02907142a114064220318280009000d00c1801d03481030004212a5204d169401d540c410414000c00803100b284d128503200580100f4859642c1c4a0a050b080ea2074a80c0d01004024414001e01e081410985543c040c105c1c8030082042c41090280000804213500080340604149084681d1003030700402580070840c3c41420040d034154040c1081d0066a000078440d41d4401c00b69031007880d948685040b994226500143c00000c050b4164018003503a070041c403e441d8107407100c2035400f00c180001d50780135511101601e80400072540295011007018851821684200d03a0340c24020183e8142204070310503034000f0600c00100b0340e01406640c4e071240c2c03444400d500d02420705035500c092110380c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 50453466 1250 50452216 50452229
    0x80903041403010912020d02120415030518030f040306060902030708040b0c04030b07080f0f0708060f0103020d09060e0607020601120b0405011401031203060b03091519050901021e03040309 83
    0x3140078141d0394500303501010040303030000c0700d800843c030340542c01035554903900003003c0042c8036416442c1403044000003903030290380305855550181d1580440803006408003030121360040550f03544003101d441e010001024140c60703a91015440311310f142886001c550103a480b400760076004004002c2c03c00d42c0100a43d07030159001e030000f44a91103854024200c0c1c0074681006061780c07408000d202c22107803c10314480c42041c01c80e800c603001b40d840061907038070188282d48920101c0c01c1000468028502414040c0f6902010302d001400d03c82445101002d81740850000c3d1200f964070303503c128181800b8080d46034060128001461254036143c01c44000d0101030f0400350409024001103001c12600b0740004d41b44c1c0b40c0700c02c0070000321b5031682081c40ca0001c10340400c00c0880d18203200050000c42201c1a82d205150410251a401c02200f080202055004108a0a400541c04100c164101c0c6204250040040400060f1100125800682c0000241e8408004140e042c806c200011394004002d5068494 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 50454716 1250 50453466 50453489
    0x1a0a0501050703050f120f07020a0c030b090a0b0a020901110a050303040204050c041d070f020f0723030d1205010b090f040b04020405370302010c11030a0204060e09010c08090304 78
    0x441d00b02250719004010130317401400c00c00030341c403443c19001e44241d50051101524007202600e6208045c3c0c0e603403901c100000c08410a85004101182c20a21160b5010305000240c1e2501c02c90b40e40c0c1c02504400445554500030b0f8049440307149943d1002e090100d210540d4024114513045d500c51540c2d074080144001d1056446100256403040c4150644004020805901d08071000c031a00c2007030713400d004443c014001090f0b41ea07084011440000c440c081840c0440c080c090050030564440380794000900700c12400e01d03001d0250703180350310108050031000b001503594551001179400c0d14030581340183c4c09000d40c207109102101c81c0750369800c21407042c40411070f40040e0b101d0f507540c0420080d0045038400c0c0c0d444400c945520141002c1081c0e1803800800b80500c507030030320803099040800e401c1309000c044d0004614140b07000000340320f003040c2001854002d0498100d5016680002d040da01640c000c480160a50340a00a115009008502d2164080c2c2041c0d0304510b0144c041c3c950380e000304c3c45040a0410f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 50455966 1250 50454716 50454727
    0x1611010512010b0715020406020a1406061302070804051807090803040608010504091a01120506060a0e040f0516120b060a0501120b0402040306051f06020d020303070f020c0904151a0a050105 83
    0x103202045c10708011800c840941d00c8542d6100c02945a00c5145010b42d5101590000c2c41300509001c42e0351f51040400908064070f610100c24100020741205208440a01040001041c10b6440f925040d01642035400038204601c1c0070140181000202d912078009a031082c8424840d550b0808001c9040d140c0a0301d00049191060800c0900303603440c2d081c1050410074003000459030004081300080010b0040080390081c0c0c03221410b1000e00d003454030800380c1040c1490042000900c4000d0f0341807540e4002d401b11203c0a04901c44030707000400e240e200d101c000400740a0309040103101082c00b170f070112040b180300214502d0940081d1a01c01c1504040c08000d540304510340b082d50b100d506940183d500500300b082549069080031900040360250001c400c009400e001070034510008a000c4c0328003850740910305503100c0340c10a42c1e445549a42c400c0660041c8482c0c0805511454480e5204500425030845440c22100f00381e0308030ba1001c0070b001e282e20201589056152952200c00046410a207007850362036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 50457216 1250 50455966 50455973
    0x60f0609031e030301080c1804060510030b0906060f040b090412140705030409150f0b071403070303061703070515060a0b040e04030315081c0509061611010512010b07 73
    0x91440111250101c1102c0900300790700d0030000103181aa0030f02e00c01c503402605038004200800c0064285100d1846102c0009400922290003040d04100724624003011070352241d03980581e51204480142c7c4c1688940d04114491810751040801c0d0007096804122440c4284c1c0440c944c0c102c004d02c06020f80700612020701d01c060ac40c010001d0010180c288150b110a40392408544a0b84a84612030501e42010142d490f00c0ca0342507501c6045910101058118500d8800ca401050704550f01c01da03a4204807484200000006000808490b03209590000d0203509041038030300d5500018000d05008d5000703121100010f4000a140c41107541c46192440943d41c0e8175000031090b01c2941c005031001c500225000420002c80102540294400d031010b219521102c1c828102c00140c1340309002181d407026031300c00e081c543c0c03510031050b6180d410b00e0325528284440021684581c0490030f80c07800003c2c40c455400520802081c0c415018800b441c090340390080c0d0041540c3d00c0141030081c185c1c5510009542800c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 50458466 1250 50457216 50457223
    0xb120c040503010c18060912060c030204030f03051e0307020a02060c010e03040308130602030a0c020906011403090c03100504050601150903060c051b0a0302120f0906030109061d060f060903 83
    0x4200050007842420b584c1203004201350f54500c0c0d4015139103031450020903c0c4e4001d0482c0c805903141c805100a01d00203e44494010300f03150f43e680c5007410390801010011482544051001e140a0b40b5050780c0c0e903040f000b00081c06d00701c0103514505a0030074014003ca0b150b0105a80e00090380444010b138075060800481401042e140d603d0410500c4006000010042d0101c05055500b0071032580c0f040c41c0d5906c61082e622481f404070311100103080607820b04014a0282e001d507030405410b160a0341e044130019800a840e5000392180001688046800301d09481e0811100080805101080c0aa420541c0d20241d071640107004551801c00248034002a0300e200c1c94000c40250342103a4107001d041140b40000d40340781d00c5049182c0754031003a01d070122400e800024034140e007954994014500030f4111555500c89030070411060340c1c08c0c101004a1442e0380d031040044d41c040e101d0b200c00001c07024900301e805100c5803001c01c507070761031002c2031000c000940e9a0f146a80740d086900340e5219a07100803c0001904 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 50459716 1250 50458466 50458469
    0x180513060504090f230c01200105040327030819050c01020a05030106080601081603020c0a020d0602040e0f0c07060f0216050601050a080a1115040803040902030f0f010b120c04 77
    0x30410f1501c2002014003003802d400c02c401c44d019441c5080b0066241c011407000d00c0c0624105003491748002009290b41d4031403ca008000503c1d100c0000c204404810160b0070b5640a90741070380050018204890031030034002400703801d0880004503000003441c0d80c0c0d41d5152030048500340303011010b82c10300b4242420300a004036400c001c1d400f80215550700a05070081d1054100b800b6000c00940c01c000055915405650704900035001c1517990380c803421101d641100654808132048810740203542c0c60400580b180305109400c80c1c441c04000d40c07154202a62400820380041640254489400c03d2180310a4140212034405070400c10120b07001075400340c11806072040300c1030066844407c0904505204002c2201230503524102c40c170501241d034907800166101c02505025000c00b40748000042c091502c040c070f8040c1040041006e0341029a01d04085041d0780096021a5055800004002009900e114031640c09213280300110100d50405400079858000c101011400000351408103a110151409640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 50460966 1250 50459716 50459719
    0x6021b04110f0304060b0604081e0705100306080c040605010f0809280303061a1204050c06030103031808030a08011202150a0306061205060f13020408030f030103121805130605 77
    0xd41e1225030b003030b001c0450381c401c07036040c3e405601e800440011894203104540886440788014a0912903509000010700d049908108991240f4540000e084e10f0303c0101014500003910b00040e140d20b0540c940e82003c50200d04207200f5407130324105001030381e0011050b20b800d0340180f900d140c0036a21550202c0c07a00c82d02d6a4540c07c05a04100d00104103406440f0400ea03040c441e03a03007441600d03503901100c0c4ca0402440c58400c01141e05114201e181082280880e030b005002d0700c01c881d01c4a10100202c2c1c002d520a80054001a00000c488240f62a81c2c145c01401804510025450f20000800041003c28103024250b11018070354401780c299a03a608542c0c0b010030319003d02a036101c488400c05002818103100300300110b600440c035013004c50000e204040c0b140e04041d0800d03114802d0706007008000004c801c136403d00d85909000120b49800100040c0c1000c3d4030031b9032816038035415420203618020500141100b040380d00c280381c031240060514408112082583e60085442070407034450054a0309800c02d9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 50462216 1250 50460966 50461001
    0x5130218190216110108010308040b070804030f060212070c021302030601050d0e0616090f050906010c050105010909170720060d050406022805040510090909030c060c0906021b04 78
    0x30444800c3c403440d401c002c0e610801602e0111079040c0c1c0151407030903003440094a44082400708008018086000f0030032240300e11620303450242c503035a900700c20701a5503e0a4885580c0400d074540e000d114103426540119407800c102402003880d600245013a540c507030703080310303400c0c0c001c03010500a90180043d20906181d0b140140041c00100306030b81e0b50307100e0440e030b030301e00d81c1c1c3c44803030310a542e5801f9030b6004050710039800340b1074140c038144000d0200101c0d001e0101d41c1001b0101d550880415802c0c0b1416010340011240840c2001160501c180804103c07010041b40040c10040200050407650005d000c0140380a155154400b040c40010301c14040c10071002140da040c40100820011668010181e20280c19000500b140c1c080c070b018605500c02c0708010002caa001c02003170080f86499001c1400324840c0340380c040000c540b0340c90b4140c00d542c141d0700e04034080399644c141d4038104000c07030140303528016282c03500300c407110301c1d0007002991480101e40c4848005449240703510309403581d4002d00075496188544 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 50463466 1250 50462216 50462227
    0xc0c0203061602010f02130e0702160308030105030c010f0206060f12070303030e01060f0e071d040f050601030c050a0207170a1403040311090c0901030b030106050a090906051302181902 81
    0x200a10781c01002c54015440c10859000c40341103403094034413003446852503000003801d0070b80598a9040c0039103000c065200303164448086041c840034a00c05103202d810100e45030352412040c540350452000c540c03410b0010f002c610071f0b422980003407100c2c1d1101e02110075000b210070b10004114114502903010845009000d0041300b49605a0840d01c211400d00c00204881d0780d070741c5002030744ca2825000c1d0382140616100400c2c02c851264240c0d008044030101d80b04600c0a000e80054115158491000381042e11002040b01542e014800c0c825032901c02d003051450608c49400c000e480d4503c5020740d044d03120800030764891f40c06080001c200c4869214039244048501032001c1c40c0c1c2c07a0010310007110701040a12000c03035241403c1c0a0180600c101c20111070800d18040300543c00703080b291000030303019940c407000000c840d911548004001c16406c1000505503005051036001d031330f002000c078403101414075103510050b03c50341101c0d0340a103d103d0000701540c40b02c010818106111080d610410b0740003140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 50464716 1250 50463466 50463481
    0xd0c09030212030a09080628020f07200405041203022818120b13060e0a0b01090e03070803070305061201050907090c0215010306020a03060522050601020319030c0c020306 75
    0xa01c194001398480781c0955540710782072a03554008507464030840d40120100350060100c0800c1c090501c412030009400c00400e013003041323041e0700650401c3d540c110015120000c90222038907211984082070300c00b842140381070f49500c00700d285040b02d1842090303030014180901c0d40c407070035000e101c0c1500e1341140d9403d1150b0700d0005140031b00234202c003012040303400c400081888244a1641e44240e20903074498040d5145000300f40b111414120688115450740541100803070107101d00841c040c81540405140d50505818504842c10000703414201d034030412050010a0444050302c1c0c0c002d4940c90046050b5030b804020500781200c00d81811000d6081805115050002148460503503541c20010002c4072613901d41203984440c1d070074100d100040646d00500104400c0c0d0028078410100741000b00c2c416030340e42c01060348034540611880c4000d4160030542d500007428002c0720b030461000d100640c14007a1465003042007811041d8944d041c0341e41e48908228043c068603410401c560000c00395000c0c0d227000300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 50465966 1250 50464716 50464723
    0x10306060801110705070302090709030803091b0d0203030304080d090c030c080c09070c0b06060f0f0306030d050a1403090717010e0106060f02070302130f05010b19050403080d0c09030212 82
    0x5224510b50030450380d0101c5204000035149a56040790042110701d1541c0c0074483c081d070f405031940d01040f95400c0048007182d200801140624046070043c003c41c00700c50f04a058454080d4030aa20079122480040d0150380c0c0001680d40180d0450300745540c640d4051002d000408407540000c2804401c0340e000428040c0202e9190125503000d0291030239034000004000362500100d407803401007070901c90890b0105119840f500c1e8000c0c4080e083d14074052421103140d04a41003210b034540c80600000c2040054101884849003002c1c00b41003007030030a01c031902c001e0600c6404610f002d03411000400080e110715400c100700c0b8010070f40d180c03803841e2402058850501070140d070070680c01d03250309018000580a200c1c0c88900c401c6080c640c09003503564116402c11039021030000301c00351226240c000c2911001800d200b05802850b000030074560b1035400081c8040c400000790410014031405000800205015404860341c08465207000609248051002d81d845c08690300003a400c80b0304090298484103001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 50467216 1250 50465966 50465969
    0x1090c030311060609060a060305040215030a1a0a0305030a0c050111040e0402090f04030206060607060e07060522050a090207020310110903070f0b09060721020d1e20030403060501030606 82
    0x5043d941255214418000004002e8030100c1e0054400801000b260707120340d014a80080c030003001104c0d6000c03007081c21289600140c0304e080907280c1e61800010025a802400340d8094004e640c8072012907c1d47d102d0645a01035070381c0003001e215018500300c080207029030000f9940c000000324162205d450344555521800200c1d404c03401640b01001003000d18440580d06407140740d0581c000c1c40301c0ea13603210174004c0310b40158204840190b224400c04441030405c0c0042005042c00d0360314075403200c1018800b140300d030740400c01500c18103600c8102130099484405004040d40c0110341c0159581038a84013203840c14400313204008010345080d9009200e8001c000c000c000c5d08000b00c0440b071000781c07146001c000044051080d6101d1001c01c121041d4613003000b2015041650182d0130b2003e18480d200303041101c040529600030010380028851841407a0050800300f081c21024a5448600c49aa40c0c081d1190104000d440c1c1c1400036110b03078503000001002143d0246a012400f4000e40d6501e00e80003010b0b00c2c80303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 50468466 1250 50467216 50467247
    0x106030515010509091605040504050103080c01180f020d0c08060a0518030901050d110c0d030213090b060306041a120109050606030a0b0c070809040507050a0306050901052101090c0303 81
    0x1864107501c0c040d0320035410f0701c110403002401c10714a81c80311160030000805e426421400d01005000004d81036944d840349a000754024501d10b95103c01e62400c403403c44014509062102c100c1004140114070002d9020109590690b500e8950100608008804d82030951050240748107240070007008030400c1e0081409030901c0c01000c40c0c0d500f2004025601c03400782981080c001203090040131000b64403074002240c1c00b51a032051a107008111b00b81e85007060933256a04010a4000448400b00b44420040000600c64080200140850b0200081d854030011307141c24492034880421a88400c490708424070800401007080c8a03500341c1c949c08138080e1502c00001d07103c0d40680000103545c2d0a0100c0c11001c0c0710b030701010200480d0341d01c074207941f00d40d008800242c402c02005e007c101f0b0729031964811140511416201c0b03c1c1c5443d2584001070a44405420560080e182c3e20b00400083d19441c0f00c02015800d050703103c07850b10010304e164a004101d2414058268400c00100106040d0031003c1580d46085 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 50469716 1250 50468466 50468491
    0x70209090d020d03021c0f0207020d05033f070915020d020f0705010503070c0c03020301050c030402040b0d020102030307120e06010314100204030c033302090103060e040b01050409150501060305 85
    0x4821015000c900804913900c021b100c00401100340748001d944609210855808014240b0707889801154614111250486042d4400034070828444521000b00c03181084a0034140e501e0301c50700612030801c0d07491090044080b183c00300418600382c0a120394031f01501c01050202956803c2440080da58040b2070010f41c0903004100401204400208810080d1403041c2c48842c595110350200300c6034148092001c0c0c071195448032010005a8081c010079004540504445071a82821b00401040761611602184210481200e0000603600401a00d038495a54100200b000b409010084042d00901c1d14500407130045000201c00c005d01c0c1900e882100d84080100c60a000101c0900c00407481140000340507840e8408003000040d45840c02c0010300010f030648070a216040e411200801d0380e00c0b59101c024203401003540405964144a48001044200c03550b40300c504060f200c201c003662040c00f5590140703489906c4007060140b4404100b0f10308090100030401c0d0f40e9a10f40040042c002510310070600320 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 50470966 1250 50469716 50469733
    0x80604020903121c022106062101090c020d0c1716060c030612081c06170a02010f0c03080a090201020a02100c0302060c030c18010e0a0b040905060402040b07030311070209090d02 78
    0x35058406d03521191010800100041175a200c00c1c0220340e4010402a8484002c201a03088401c10f580c0c03017540c0c102841d44a0741c465051a42e40026650584041d1003198002c403c42280c0342c1c1d01c40000a082c0740c105031110324034a407000e0101c10500c14048040300c0c52844040802c100f110a0340500101260340c0c0d010011540c40b2114044035001d9590081c0090405110361902a840100402d10741c100007503001692071750300c400c80780022507040c01c0c00166800c80e098100a55170440050401c2c0e100f146030041e40c81c41c0390780c0c01414040000c2e1840e141c0903580d01b12501164000c0180310344031600100518044c18100e140100710b0204c1400480043c0544070100302031072203000a4900900c030503c041420034485d030407200c50a400d803100c058108440048841c5032501c50300c895074083c02e15185101e65031403c18480206540e009460b090055104000030008030f2200c4007a14003035603240c036000c41c0c0e84c1d40030740203201c0e907001321000a90300c8000036051202d071000000d0300000c241d4154003a64044d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 50472216 1250 50470966 50471017
    0x150102100608031b0d0504090b0a05040504030c0203010606081009020f120c040914040f031101110c0304090e0a03140a121103090c0f090601031d0a050312090703020a050108060402090312 82
    0x1780d00b50000d1a0104505000070704c07101c483e60308045162500500038a0721150b44c0e4000505444082d2030503004110203001c0b001c2517050a00500024002c14102000903080109000c0a0200284603003100b41d58003061000030800343c1c0040320012581c0711049010780c20182c051032110760040c49a810380030710340340300c0100034629401c1c550320407034200100000c4109261410f03518210864422412035507036100000c0a615800050b00d401490360000f1600c0ea42822a60021603004c00600300455205208400020380e21001c50340100740e0391003405071102c9580300e00b980c17801000b4241c2e0107014104000301102c428510095031042610f00212210301000b40188940745508100160b005040a80003c03a65406508441c803000d8000e01003c0d44406000321079800d19044c1c0c0e6048071150000100c40e2580c065042d041d0780c00c040d481e070180129600e594000360880d1224428103051001440014200baa01c550554180d25000b4091365034200384007010301400e41c00701c1644d034030405e000c21241c00c0c407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 50473466 1250 50472216 50472223
    0x70f02070f06081e07020307080f0d090b06010e0a05030309040e1504030c031220090a0305060f010f0f08060a110f120609010611060f1f03060b03070e040b150102100608031b 76
    0x895046d005140340c20a41c3d2580342c895406005a0265032070300300a40c080c0c103c1d1354490043c1050040d050740d1101d06208000500c10082251050701ca000b1900d0b003880b07965400f02c2119000c240071600020078590700e04040341040e4445207003449070700f1004200700078180c00141c1c000c0710b280f0039514200b036a0601d900c01801c446080c0103250114025405160254000764024000400010030014003159685d507001e2500342c0071030342c071110b9640c4100108080119a43c0d903402510a40207071810390760a110949541e024000d101034032194a40c814500c02e1549001141d91000c8105412940c0b40d141181c030164408059132254000e17602c80c00000781e007901c102012803405075244003600c85a01c82800344181800050504c05590787c8207541107240b581d80010b080025031003000701169202e1350300e041504004107544541503c4424004200000e225644000d90000d201c26482c00c264591900403440c7c51904020703804214038044004c0f8044070f001003d01502c2c11b0a0f0044242044406005510f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 50474716 1250 50473466 50473471
    0x3060c0910050c1c140a03060312050909040807021906080403080105220203041505010f150c080406080709171b0303041406031302040507030c0e09010e070f02070f06081e 75
    0x10355040341d80103034484e03d2225280414003801d803503c860098400c46a09150741c0c000110080030a81d100000c004000c0b0100f980389601b203490800600303000e00c0300082184108010b10040800e0b500007406000c5507100e8840030319103001540c00e0513140d40c0b51b2401034507568040d501600450001000060140350800d5000008680b00502040b260032001086e4040c1d00050401c0b07884241522003003c407144117200e0640207140d00104105c01c2c078980782c1290001c2038070f0200e80d01000090307030905d40812800e004885c111011450907280980c0ea002c1c2c12501140d0a400c0700c0707211928154961038059001581d1540032082011b1529450340e447c0c10140d42c0c2c03199100340b21060754401d2071180c0c245800806164050300b4009190b80f0045581d0001c0d0895104035500b0010079075450b81c4d900c01c0c59121196400700318003a114200e042d4144000f0703241205000342010b0410441c1010030310068420310001000300b40c2c1d100300c03151960b1569005050010304441c40d42248a08804010003280200513690 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 50475966 1250 50474716 50474737
    0x306090a0c020c13060503030f120c04030816020d0609060b011805030607050a110703080d0c0503041502030c0708030a0902010806060307120f0b030f010c03050109060305060114010201090203060c091005 89
    0xd103031a060020f000e16040e038130410700846680c91034000b8140c0c038140000d0a58040c958010340d075802d040005081d2940c00504030300e55000062009000052015003240e6140301b443d50072551484440c4001150b182171618020405820480c0c420100629038200d80d10902d0241c0b03c45c001620320030282c040300380d5607125190341075003e000401c100d207010b400200441e02151030030f04d0140c80901c3c2900c0c98004076a1040f101c3c030764000b40248a43c080f5100e020310a01e114a4241e18508003600e41c01c100a0040d602a910250300001207102240380c10100c1780740d140d200c0b40e229140e1911120200043c11400310503408140038400161541c07034128100c0e40f190045803108a02c40000b0400072000b01015070741516410342d510070394929541c04001001d88400140b002103841c00302c161006041d108180d1100000307904142050001031408140c050558002c101c116503070005150040380500300100000c1e4060240000748103d5a0910005014220702619054020040141c00f00c8082c40740e5410b24 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 50477216 1250 50475966 50475973
    0x60f06091413050109020d0308040b070c0807122007150309020105070b060a0906030503031504060501020a2a030b010608070822050a05010f020706060f08060c0705150a020306090a0c02 81
    0x14100d078040c40c2203482c01409580009142101680881d628001a203401d90104005800700000c00c4400824250711842600e8a0200c0307001540e510b040c5800b071500020001c00480003000c09a500c100c4141880c030f000504d65600d0000040041626401c103402070003c16851401d4040300540280120003010741e040e90364614010044d200c4800d9500050303c459804003a040000500c0b0110b0b000c0d4001440c0690080e42c0e4a080c9500e41880d5a803034180c0f0319010b80d0502000300000c0c0c1e008a5092841d9400455a8004040400000000d418001103280c1d0780c9510300c4012040c4190011020f050780c81c1611221207507103440205032200d00d4103c42c09900006030403088403103801c640380102da240340305a04940382a0038030356445094a45080e501085140e0100e040d4013400020300078600205a04a03c02c2a0a8204891207071030f0b00f00200201d100344000120a4100f1408100d003070a83c0c02318a5021f151400d201000d10003a600030b40e1090300c41d600307020114105980301e00c00c0d81d01809194004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 50478466 1250 50477216 50477221
    0x20f06060f120a02040c0e0f24090406090c09030203120c071a070c0303180506131403071e030b0a0b030a02040c030b0a08030d05090d02060c0d020f07060f060914 71
    0xb000079080c04846161218041d00b0402001038583c4c0c01144030303400003500c40182c41e0200105024040806500c6903124048400c44200711031a105011a025a0420324480e91020800c000c01d000d0700342d540c02a031911f860700c40106800c540c0a01c0d000141e0b48201c084d0341d42840003001c0c05900b0b0090305251002c0390042c0800300401400e640450807000f1101e00c0003810658036450b84264407203594002e4020890075200c0c00041c91001c510800075140c1218260304182c4110030200e035440d168040d221202030030946d15207a03540c040210b1b200070981c0721613414440650030011b20107001d0b14841100c1000d2100d01064401035180110010850058002d165003000c940801c4003a002c0360030b00c00c0c1459500e61030307071207151926074818020700641c00082d0342d2011130440507c200c480c0201011400d402a00441b00350f281e0114070190021801442c842e20ba0840e107500d04024880c0026000488500007490350412000c0d402248415440304c404100680d07070f89507d4000e079145080b04100385ca050703100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 50479716 1250 50478466 50478469
    0x605030115050a0905040f0c02010c0c0503030619080f030903060a020a050306240c061806010303020d180b0c0c010207150509010804050c0901080307060b1c020d050f030409020a020f06060f 83
    0x40d00c210001131810400c1c0d04c1d55040460100c6591031116510a44ca80844c042c0d0070b602406071404200e100d20300000302181c262202030300c80c0805030a0074400d0141c65503040c0003c841c000210080c2800800381c074162182c03c0300e4159a40d10407203056000b801407038005aa18001442590020002922443c3c510303940c0b07804000080454036040f0418001051400c4030480381c103406440c00300c801c0c40013400301d420545100001c50b940c4c81800102980514014400254045490325a2550b1030600c003420170074000704101c442a95411450004401044501c4c142d54002a07134940001c0a8082c0c8184a40310300c04441749802e40e08103040030a00410090481d540700e00134aaa229010780141c84260500d8000109000c07802e0b4081d5015920100c1c0040520420b8400c0300c00d080001c071200f00ca00107400450b40341e650b11020300a40f049400e100030034103100083c800518005c8035481500d0391141c90f40041c0000750410000307000148a41d0346942c4510703000084407030092100a0001040304400c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 50480966 1250 50479716 50479727
    0x18070f050117070c120903060f05010b040308030c0c03120708060118051c120503190501030b04081812030408011a090103080912010906020306121b0415030b100806010605030115 78
    0x1011001004200c41400d004290514029145c000c4540d60710203c092660910109036104611060709241c500030040100d07598401c00c03103049a900c006455181c0c0d07914240310f0f00e00d014680c08902c841c00300081c80c0440703850480201d0707c10782491b190f0446e1500d0358401110202e041118400601c400c214044c0700c2490b01c040081d243e80820440c24008a2007580c550089805101100010440200c14064040e40c6070203000082e44c1015810019980b441d101c8e040c0d900800342010300b4903980012104c211242c50f03040c1040080d405002905400c4043d903104d641c035480780c89401005e51138036486a072a600c500744019510303100102030034090390070b6450306411035010300d052650085802c40000580f00d03007030203240010f500402d00141c072407500006022000c680c0c00b1098aa5400075400620381c664140300d05081014181d80009020141c00c42000e1072507030315000036216100c0003081004c1821680c5242090783c075410151401640c4e41c0c0b40980f101e000a0249010703110310260038020891140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 50482216 1250 50480966 50480971
    0x12006071107051503010f050d03020304060e0a0306021b010b060705071505070b1824130606170610080c060a05071e030c0215030105130207061418070f050117 70
    0x4029210308560300c0c8005070850400109a130203068000c0010444c143c446002c900080c181070f2035498031580c01e030b60000d481e84118002c400610400488510f560345801840c00095035115000319510501280781c4240d00011702c192008943c2894100500740c01c2c80d0041e2200383e58010010100c80741015284600c481300030015030100300b802d11580001c280d040034194011402d80c54140480e0140d02c5090341040c02010411402c00f50180b10b030700841596494040d0320030821100d80044240c546410006000c1942c050355482200710060030540c2004220b4034001c0e42d80f00c0e000c440295840c07000755250b5442c0c0590710391241092089081040c010700c000e1180034800d0880ea00c00103a034498100c886084100240e00107808444900c046040031012000d49400d0a4549403d540c500800121050208548501c0e01a004240c0408004682c3c0256070318500443d10614541b810300b08201c0c03400700d8015613000c28425120009000030a400402d41540d006949908515195405204911802 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 50483466 1250 50482216 50482247
    0x40207020301021213121404120f020301111b010b0603070810030b0103121805060412140106090510090203010501050a031802100f110304050f04090201170a0b01200607 74
    0x7041020340204c0707040090340c0300d09035082c1e101940c14510b080c0540d2040c90315400e0400e019100140d5100b11040700250b0b800c540601962400154841c900040a00c0c10700f10001e402d50b00b0156100c00c8011031070090103135820700f800810711101710360a070b450076203000400d03445c0c04c140100040b400740ca1007420364030746c00205001c60b140c180b640d95071035044406003644141c92907001c0c00c4104250f01e50000031a254280c105208480b00390070400095603c1c4907603c5520703041d00c6c85001d440d041040207454000c0c40001a0002c02c43ca940e0345074800050101218404114481c940d404280c52215100340c905a41060799940c0c00d2482040c42600108000b5409080552580d401000140d5814210741c80c40101680c0f04001c880c044100a0402d8520ba1510092608140014401d0380c6580000e002840300888000c9a40035480c0010b0b02d0380c9011447d126003480d0050200320b0181810781110020400c01c1c4d9811000480404401c1c42c600c0e20056040043c0d080000030074012403095103109a9542c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 50484716 1250 50483466 50483471
    0x402060408071d060105070309060e0d0602030c18030d0504061407060207050a0201030b040903020c061b060106020705010f0c02130f020d1805010e0a0c0308030a091e0b0105040e0c040207020301 85
    0x110340700350310b190941c10307440120710340801c0e07850f08807120300075048036003008003800c182e82090701035034019287c003105004400c02c1200c0051001c1160b901c0000d6030f10482e4110804550b01c0c00c11032200402648601614803141000e160424002c0c00c3c0002e0f151800c10700c684d6411705080c01c2c820100c6c0c10396407461a00000000910408000c1880d51004268032486440240001003651002500307840880c0c1301b0501c140e20b00105035000c6a004100c0007003210701220140e6581010007800c1e4950448110950264440c5400210340ba035000501d5405a0300d00b40c031540444440324130700316464100d1020094001ca40c01d03076035640380b00941d001020252140b120250601c14241d01c004c0403120030071b05502651842c3d2003e4024001c080c4202c2e00702100344c101510910015803941044040548002400e551001002030310001c40c81c1e0214413131960005424000740d4402c144030b150040180400d880c5e00700710b0800000d440ca81881456402c40c0000f0141c00d203581e42e10f00704002900003810aa80554 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 50485966 1250 50484716 50484719
    0x50307080d0f050c0307050a0e130606122d0905010f02030a02130b03060306060909010905060403031a040509100c0e060d0606080a0b0604050405040206070f080405040c0c02060f0304020604 83
    0x8280360040c011040d10000001001c90b207640a01040d10409008552003a00070010700501d158804102d0b00c9070050303401d00040020f80c04020403160340d500800a0110b2f440c02c003020544a5014410400f20319001d0b00034070581c00701807142c003203101030a001d05c03601c41c0c02c00340400c00405080d00100c1c0228054000081d004480c041440140d03481100c0401c241c550001e42420515005510300000d055031801c0c070750452030b110021941e150000742142c0d218900d0b01d80020702c1c62100350080342146a109054442c24101840c0141c040c107058a0030b59440440f0010298407420f2610030030384201d004800a0031040114020f0702c000703101c80c0191034104585a00078140340d07110f010041c210001c405030001817041c9420b070010f1135100054413403882c440c1440160011030f51008183c4040d114200e50010306902c65100150304c1703101d01a801403c4013512003010041c494200007074000c8403400c0e02c0078805403084400450348041c003084000d502400901400b0841030903d0095940144003606143c80c0030b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 50487216 1250 50485966 50485973
    0x90d08070813050708030901090e0f0f0402120f100c1706041a0d1101080c031e071b050a0b090f06041e140f0c0a0e061315060e03070501020703051207050307 69
    0xa1580c001d8181071b0300000f0300515550b8001002c81c000c1050320070b52006402c0c0001d03030702240741016061004005484d0041415580c8440842c02c030b9000d8a812590000241c84042c0d80f030740311528140300010301e029140d030030041c064551624200179414010040e41c0e00e0400300401000c04140c0c0342d45045662041d01001e40b20301c04541000c80c01847ca81c00c1c0000250001405070388000c22500c0035003801c0c01071000004441e03080c0e401030001607514500540e5191802c644c03103d1141600d15651481200c6542031100125910100501034148a401990707889452a40d8501c00f03070f0002172941c000000100451940c201e00050640004c200e41b0a1802c540c4829181000445c014446030300300c0c2e0640307107103014208036504c0345000940e00441450b11301031a80c042514018200c600655012055601c000000d0f40900340c80349080344480319003526070400078001d0000d0384200d1300910800301d011506600001d03000d02101d43c460005c00600342c018020005036040100e04803410b12090210742e002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 50488466 1250 50487216 50487223
    0x41404051c091208070c06090f090b1c0602070501050c0406120209030c19060206090109020105070204050a2a030509031612020f060a0c03180206041419030503090306090d0807081305 80
    0x11507018403085a2280417a08007030b030361014241d010405002c21840b003003055050499185003150301401c0001500d082d841c001c120f0080302101d1001608421011100400c1815030203440780c03074020070007000b06940e580c021945c284035034003929000c10107511005400c60f0040c1c00520010070080e082e81c00c5003034018041002c01c0008216050402c1c1d0400d418050541e04000841c1c0c841a20300003440600e0440d00082e0861150460103406140c0b20800142c4d8041141c00c00c4088600c07045002001d00f00d001240c0841c5041201a034000906007004a050ba00700041515840400c1d41500d40d0794480d50751f1034080b0791054942d40c0b1309501601300d80b1011080b042c40060f124411030fa40100f0001c1c8140c030000c0c02c98517101c0340d661509114106001c09612480252415034100012150003c168040007800c403041700c5d26104980c124820021042000c080081e228008094084410984403001c0036911250f40505480019070804001100c0303d20406003280c000000043e01108898076449103405d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 50489716 1250 50488466 50488499
    0x60302030f060609070305040f0206030a140108070f0605031005040c090305010e070f05061c050702010b060711040c080f06040b01140304050703050705190e040201110706030605041404051c09 84
    0x550032000420203039042512241c0e52000d00c46c0380420141c40c04c0e6440701c00240c600740f0042d000b00c0c008000182c810820f036201d030000e24165105c52487e0b40c0e4070076141e5560403d82c080c80402c41c2c4411400104980a0410360b80035150800d005080d4508250070310000303145c000c3d07074082040226800040422000c0c407032064225000405440310038244141e030030242441d988030601400d01001058005110410020002c40c00000003148544501904a001d400c1c81c01d991544604005464010440c40001e032800026054070b080c842900c0a0320156040d01c400c44180000310b49200c001441071600307911108280c0c805041c10141c138041500c150a140e0400c550485440d8880842032003800010014003008040464075440c081100c031460800c043d40c644150b0340d960b00c454012604680c0a940b441c24105042011a030185507202d200401600091098601a6280402446280c42902526031049403c50000d00c00c581c0200d001040d140501d05666041018001b400b29884081401e0800b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 50490966 1250 50489716 50489743
    0x60708071104050c090d061d0f01060f0f03030203160f08030405010b04050a0209060426030a08160207030201080f06040b060a020a030810080703021003022203051005190f06030203 79
    0x807071159070703200380800c6a00140c58155000c0d400d020354041c5907191051510003035417000c004150358180044501407003035032100044140c007510550a010403815402002280ca00044800e00940c1d00c001c8a01b6503d41400046c006030000c010008114046000503030455205042104080c10303183c44044107a001500c049400d41d448007082802841c3c14000c41d5008a8400011807505071194001040d501c298841c0c2c002d00310981d03074821503c1c1d060135141100000c01d40b01b43ca503074074107100c0c0c000c3c41004110f603071080c2d085400780051012440010003c00350b907810385464003a912006402c50386440000c8c0307200d9005031185040c20b44ad8842e18091301d8000c480e038004044040d010316001d85504001001d00414200c589001c01011000060340e4040b80e4054580701140020843d01300c02030302c80d44209221007204551b0070b02c5400e088102d0744048a00400503901d0b4940817a20990587c0e1003660720014234a402d080345251440c942d844040044481c81c00003980641c1e070f0f40406d007840403040c4100d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 50492216 1250 50490966 50490983
    0x60103060902270a0e0705090705040302010f230f090301060e060a0e0f01030b090f0303090d0e030312010b030903090a030503030703150f06030b01170f0115030b01020309040b06070807 81
    0x94046091a4206a05115641d034010084100f0015440b050101c0103101c0340901e521980740103803c1900340850009410003a11700c96951130004c00c0036189134000c0c0300c208d000668800381841841e2103005289003460b0880c0b858030742e00d0b0f10782c1070f016810f400090794242056420050300241d5603091003004003d1081810b89041454084104030620f0003030707070014103840c61400812403000c1c84100500d065235030004c2d00c8402070700e44510080c9056040104004688000018814131050000e01e02c03032400020b0751000c90300100d10080c181c8030f0003000c910800d100b0340d5800501051a1041c091355011000d8402c49060603040340000d1040d0001d07038000c1d142904004181300c00c8a038540940480c0b00c0c4410317155a209842c02e165900941d050b84105402c250b547c07039010b4443c1e8458211503140c000b24900480040c14100341081e100c8101b0700c44d20b06140c1030500c140d18043c0c0280034003600750360705801440c180b85040342807001902e0045205c0754061420082e0340c0006240c01c001d843c0703080c00b45901 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 50493466 1250 50492216 50492231
    0x3030a150503030a121802060d051506032401140703030b13020708031b0a050703120908030f0708060306060a050f0a090e06150303041202010c050106150c030206010504050601020a0308150306010306 87
    0x100170071540f40034000b00960728240c180101586410089511a500c1603000107246e580d620a1740f5600104c6041c050341c0f08000000340414005100d102d100c4282c02004003640c5e00641d11700660340903080c0307c100b080c24030b0140981030119008e0f0740000d40044015268440b8844000c1c2408102d03407001c6406c8078020743c08130501c42214003080024102c0e07604081200c1c07070240454406020350140d04030040401c51004100c410110403508045400c6038040c0c680da88904058101d100e0166080303a1050004503403000045c0c031481d0010710326018180180c80d240d1914246010b01000b01d05000140e44c010101c5030b000a202c00c594403a2008c14000c400261185082c4030114045c00c03505070000340d100780d20600c424800301455100c58101c55a0900342642c1c0030b441072600758007500030740c0d0001182c1d8007a0205c07400e4041d08161440340044c407a03406c1d03800580e00c0700c003000121807007503c3d03140c0107902000020000900540a0382d4126160f030810b8000c2c03000b2000000c1c6401400d030011900103865900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 50494716 1250 50493466 50493497
    0xc1507030e0913150b13020d0c0c08032205030d091406040b0a050601030f0c08220f030804050f0706050909090606010e1009030f0605160c030203030a150503030a 71
    0x101c0000001200c0307890031418800842016180c51a8000d0140e820989546444161540c080b001108010340500101c0590440c02c0d070081d0000d000c0504000d040c032076500d0072188038040b0900c969603c502454196125240362030a41040301080c0b0811b04031100c41c10000c11010005422210141d0708040b271075150510740b41e8122080d0800b50f800076480303032050200003a900c0f50a40d0384800105000200da98440004801500c50800d07210b44039440e040c5030000c81c56105850b18441d4250314041051515601c4d0424480f1030082000b60510700540304170030000b0300c07079a0041d40090040e0220b85440e5000c0301103c0c104000ca40c003900115900080030165800d12600782e5030302c43c4040018000514148001030908031007600054815503100b0308102c14035006e03680020203160010400c04800c4200d241540007404160b43c2501c0030701d16443d018400d07900c038061202071f29505902842c1145c17143c40030f5001400d5154484114011381c443c0108407510108003501b001c000c43d907550003e402070a403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 50495966 1250 50494716 50494727
    0xc06110c040203011511030a080a15030812070f1407080306040b09010b07030806010c1109070207170303060a050d12111504061d01060501051606061a04060207050402030124020c150703 81
    0x100c4206c03981e0001c2c400d6032541a002054603034085c1c40c55030041402903070000344803c0c140081e000207003c640080341d40355001a50324001845a12961031b980f260561110b82540c0020020645524a6804003c103000060710341019542100c00600082400740300040041c031840800d8014152100380461401d040c1030703021b00384170340050081c01c150240240d40c0e02d41c10450f96500c5000c6020300d403220301140425100300030031001401c108a101074040c0d1896403141e2131b94000d484031807042c0113400c03000c6424039004082103170aa921041c0c009010340c2500b02900e449460480c9000a400303100c1caa00860400124200d10a030300c1a400011900b41c0c0c02d0340444100103c24410300281c1c9800301c07c2c006a43c008085880300801c0740311050325100d19141001c0a496590086c40d030340140302c2d00d04101103400324081c3c82981ca254084e59021030b250001d00040380030074410781d0031182605103000c6002d081540c1c2c2074246d1039244180ca120f80502c2004c140c0003617230046416610080054160249035000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 50497216 1250 50495966 50495987
    0x3031b0c06080915061528030605130203010e18030415080105040e0601030201021b03030912070f06020c09040204090305070203150a0e010513061d0f060406050a05040c06110c0402030115 82
    0x100880841405c044020410424020304000c0441c00009140c15640b0360f5142c8101081125101e02a180011604014094003a612510780680741002410f68240b09900a490594015190b1005560b44a0980c5000101110006550741c0001c00010031359104686403038840e8040d9485030b8080354505806c0c4402c6403409007410341e007078104400510040c1e07401700b11141990050302c840028030709040c4c00a4114440c01d01d1890b0b02000702c0449420052021072820220382c00c2c503900782c2025a60348404e070b0700c50000d084e0b195445848030300003600501d003a81c070103c0c3d854003e10703041c0d00b020400d601092504000d5265140a03500c414204111440f0780d000c2d600c04812218000e06c80740c106400b5045101c0c60306400140300e00c2c0c0710520b48803004405028029900d020074100d8801c0c4585600c01511800e094605031401414a0001170010b000380c0566401a41d21030401c5804500e028812a0301c520500c012011501039600001d620303984900265001e00307000c2ca17110303080e0101a1000317401c20490 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 50498466 1250 50497216 50497243
    0x10e040236090a050901050601020a1101051c020a0c020f030d02070b030903070804060503040b0f0105061902030c01020a11060a060e0f060103020906070506070f05040f03031b0c060809 81
    0x4000710284651454100700c61158100500310a070441d16a00c04201c07408030561540181e400c00400442c01c40941100d40200701843c002c000350303260800120380b140200413020700030202031200340c500381d44294002e05003c02d404e10915002d200f45c40c449d2040e603000e10702d2800000e881e02c80540c154a4a02803c0400c0c4404500410f010802404080e440c3d440c1803103031403c04c2c0c0307010001400784903040c002c40d1300d0755500c20100c03903690741c4460014080f600141c0301600c071711081d440054944991060900d0680d48028026410b041800b44101010300d040d001300821800203004804078103d00740081d02100322a52030f0f81e01e2415010003c5450100c000b013000300b58604161041059549801d1010340111404595092a54038600168082c1c8201351200340c200700001001b0341402004900e01d4081e4600790ba0b05110301040460403146402140240c6001c1310801c9000c10000b4000c0c00140e01880c580d240e51034000c0c40545070315036903114943c400c002103046030b002c1082c0440140b040c0400081d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 50499716 1250 50498466 50498471
    0xb100302040f05040b060706180303050105030304061d0f1e01021b0901050d030903080d050420010509060d06051306060f050309071404140405010f18120c170c060105010e04 76
    0xa0031200c500c0c0b0010b5440303454042c540d9041c00070320f6034490b030040b00c0320315070011803e02004508003500c18181c442c81c030080d000280b4200001c40c0c5490003100b02c1c1c04481380d03030b60388081140c58281e04e405103501c2c80d08620751249034451210401d8a849045025985c5039000ca240750618000000e03080c4011501e0708143c0d0000fa42c210102603540c6800b617419100280c07001d00b490541d030b00d402e441b90107285d08042c02c6d4000101d50000c8401c200d400c03151083c0d20440031070300c0d285040420301c120002900c4140c0c3c003083c1c042c09016103e00f401c00140484403030242e0085017441daa4030115406050640010141d247c903208188603281e084489205403000918042e40b0310324016940c191682c061b80200a6000e05c1186048500d984541080040d445c1c10001e140740c90030f0030300c0c00c2c5008080d01f4403000a01800c001440365500e03100d816100c0d0080c4c0164900c0e1401c1070003501110a1032810078212000c061042201090150b20806004584218001800c3d81e5041000260603191403c40542c40340f030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 50500966 1250 50499716 50499719
    0x250e0103140115050307021002042301020a020f09060d08180a0f06021009030e09071106100b1801020718050a060e040201050d0c0201021b0106090612081804020706090302010b10030204 81
    0x10001c280315a003c09881c0340c801e8807a140d80c10201e082c40d00140003407407654000300d000318494404030112507908014031024186030108400580c1c481d407528101039171110540e00c6a864078240004811f520140c01008841002070a54403041035820450400c60f103441c61030310000c91414660100d030054028000010103d40c60038000070741d6580c1803241516a213448001c142d0070103025084803010180300801f18101ca180803480149405c0c40d10351121018840c000c0450428404400038000b41c403804a00c640c603007280e200314041c003442040d5000341103101e0000000b50300c1d101403001c05c4a48080200200d69800c1c103c1e0910280c4800f1340180d034840d0a010184401071ba08507044039801d001f64030001c52016600d50702a40280103140b01c540c01c542403103079081064001940311034150b0382c48a40c1042003549460002e060310400340e00040510008002100da17000c07061191b03012081008001525148640c4d41390000e5500001c02200035139112141c0354441e10b01501801941c4840740382c21802c09 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 50502216 1250 50500966 50500979
    0xa0b09040b07030213051206190501080a0813030f150c02070b070209090715090602120406020705090901090f060c0815100c02030f06010308030907150801030803250e01031401 77
    0x8401410301400e15074001000c00c170740c0010410410003040002c010450880c2121402600c40030b0484100c1d092140e040d0450b00c050150b44038071410380741c1d0400145010b035141d40d0342c100203910000490000109412000001580b0303a100c1d000d215110f4003500791000e104203609400c0e594034000581c10b6401c108002e0000a1180094031501c64045911400e1511070401c080d04006188d00408000d444041c101e8406a0304150082c3c201d45003039003114140300e4980d003d5441d6000e107005000040e00710b104c0c100501c7c42e010315403582240b80917000240001e215a10460303200755464080783c1e4191a9150103c0740c41e0409400307580505201d9035240c0803400000000d1030152a44070f43d00074409100303070311029500c040105152211120007140d0141d42c5078100755181e50000ca03500f60140c41140c0000c620b848910780c6000308a20341381c0b40c00000b40d00b141e481185640008110307a4902400c1c4201051150815a8918400c2032139194100e14091290006042c0e0300e51540f00e4454100810040108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 50503466 1250 50502216 50502233
    0x3180b0421151a09070e1c150e030c0601080a0201080105040c20011d0f06010b0f0301060318081303030f030911120c060304030e0307270507110f03030a0b0904 70
    0x210b0511020002d602140c2034064208000c000341c55940101c640b0080115098000d19038408800c0121006459144410105079211049542c014130b01500b001d040213a110381a0031147d01e10442c0d00a40f0704103180b58603102d1030984268421003e56200003055015560413402484c00350600b82c0d014000908145070140c00c074450120b080441d151000800b91400c0001e40c031841c0c120541c0440313460512000500c90781e0310790300160300c505580903080000401c807041ca421182060114040c0c2400c583c81c11f05d0940081c000302c4c2c0550404c0121010120010b94000020305402030724020309498182941030042c10b201411400c1003d051401c030300200801d034a10502c012020048481d106468200300b04030b410511413100441e0400c101005100426030810140078141d001907044610341542c0e250040c00c003e80d200b07005003242c0c0601482c41c03c840c400b9084507031311000e40e040c114030207011000828504014101c028009800200a011074490980108407a50004494a0398903043c9602c0b1401d2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 50504716 1250 50503466 50503493
    0xf1a07030501141e04020a05090405070c0b040b0403090302090c190306051302030606070804030b01031403131514040b040f090b010e10110109060504060507021c050703180b0421 78
    0x130940481d0308500e409010050521000a8040d2065440b90700d03410024007160418421140b1942c10f140010308070342c0c41007110102d0903400804e00482c03600ca075214950b000c8009881a003c1101540b80400943c0350250914000c51403811542d944401d482c0040051103550f40701c0c4020503040c203600700b00326550450f0a00003103640300c80050b5a07803a4500014000c3c4141100142071300000304001051024262499049038007516194034603080c21420203840c0e214540c900c80d82c880e01088148040b032032604401c203c0c8803190403c104006200d942d1a0400d0f0803036401804d41990016090040c001100990002010544000d001003c01c240000c0c203031105c900700c804c1c0107001245201c40c3d6140300b40351401020b00d007503008100440082c01c001002d0481194107685260811300420100c3d0300c0080c030164001001131402ca08125a280b041300e20b50f000700c0b0103504114100e07040d40044044000310b0002032005050f410759071031810300341c41d0260340e100d031080036204460115103010503104505481d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 50505966 1250 50504716 50504719
    0x30506011802120408090a08010209010507060507120e1b0a0b030a02090102071d0a0b060903060109050a1415010e030f0c0105090a0305030703020a0309090b0a120206070f1a0703050114 81
    0x304000760100a02009006204824102d2282d0000744018040e03820010104210280e42070118240c0725200d1601340d200c0c4403c61400141c041100c01d0125845501c0250001864542303602c0100d21282c070b4005407201c00559403c5a08250303030651a00b0a035811070440390800b9110003a05514180b11305082d800700812a04801c0e400241d04111130307209104200c003400c5101d05100d44214900d2050b4000034048604d48180f43c40d181e07105d4000d140010070750310b0a410040007451a6070800c1070610240c40081d00d001702d03640e20742e200c103040c50004070481e178811181c1e00d0002d000c1601c82c1000415481c0035003860b9000703410004521103111408200e02c02502d000303080280d5240076000124220b19104d62000c4e000e4080480e5400405a01240c0e5a003ca4002c0d40c50340e071926281c6601d83d00302c804d042441a4001b0605401f00000240203000300152400102203070b0400b409074440740306c80d0941e5941140c4540c0c00401c0304000d80607019a1a0300071005103001c0161790304019200c1c645c070708801281c3c1d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 50507216 1250 50505966 50505989
    0xc050123070306180b0a080601060302030103050607080402031e031e0c0c0603040807030e0d0b1e061c031206170708010c0503162001020a0905030106080d02030906030417030c0d140103050601 84
    0x6644a44034045410011f201540c2203560340d60356800014000d40080c00200c1c5e443c0501c1d0007194080b80704100e21400385130000c020b82398602c440c15815420802d4110020720501042c4001c000c0342040a5a85020b0080352420660700c0e0715145c10141071808009040e44220400d00602000c41c030208169415142d142c10a000c3c032080e00c200145120003a614000c0224510360b0800c0b2a202540e0300f0440701a1441036004669150281044000c802c81d1248503108443d90300f4520229100e24444001c00070300da40c000581c40d403030700745540341c208442101c403000f0b1b44500820480c900091180c02505410b500d0200e045003021400d03040c0d6601115009020050b0088600e106a8410302520502280030002103644440403c0d01816006440c030400d4425460082d000417014804105046254196400b031850700480c0c03402c00800d600b002d04203075000e90400c2c0c00c08050055540c0218025010406665207555545038500207661001c28401c9000c2c21035801000000c20000d016415110481c03c513 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 50508466 1250 50507216 50507231
    0x5060705010605041a03010b0a03030f050a11070f081005040506060105180907020607141e03070c0c120c08030901021011070b0f0103050f07060f0509010c05012307030618 75
    0x9800741c4140d0f0401d591051a10f4000402c0135202e09051036480020350003404002400402c2100c12001c1d880060042200110700c1540c25105074018405e80c0c0c2141069804011040146407510700b0300d4000c0c600b00d0b1200941808009420000384000d01840c1c4800c1c82146007568919803200009003081c0d05000010030007440c0c0540c60216032049a0010307107071044a10b0180002580ea5500345c604101054000c94600d0910050b00221201e025000d80c4504081c07025080c1c5002c0c5a1009280e1820003d4035201e00002481843c0600000d107265164402c00034007a080035060101c0e594000003860780100680b1035980d8012901210074100700000082000d00b000315200703248112100240050303500001c004240000d8101103042c0ea00410499145441c0040c0665490f0300c2c0b40181d6012807511000074042034407034030051031945010724142840d900655030382400d40c0d40841424121220b400c428880b000c03c001c070080e0b40118940740c24440b080c9050203405d182208400380c01101a1546013 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 50509716 1250 50508466 50508473
    0x30708030c0d0218010806030f0a0f03020a0f050607090f0303080402010c06110406030203011a040f0b0702030a240b040b060a0305040501061212030b0102210c0708120c0c090f01050607 81
    0x141c07802620b0900d0159a02c0458540c4054540b0100010f81d02150b520b90100c0d141d4180001c00c00340954000c0b0007807070024a60788030700452a8119104800f14400e4400380760020703629883c16584107225000030503041c10014405040b071131840d0441004010f018404001281d40b00e404039400540a0034a0045102d050521030050f01180d500681001c0c400500003400340e906d58011812100f4045811075448013025030f1035440e1296205080501e1144102800032a1412005200c050310080c1100c40401280d903c445c10b4400b1000311841c00040601427000c103050034001d07030507140402c550030444c3c9a0210009815070042d082c49108059507000000c040100950080018000036a03a00070410058034000d048028240d08020020303091902e03c04965000152812221100d00c102c50203004500904c202c0d550440b50344142d00d03108001c0005802007051219181c4490b0070103d50f50760307200c950800b40c80c10b038900c080b450190518104013b1102d46480c112819194121445981e42d6180c1c103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 50510966 1250 50509716 50509741
    0x190201140d0605040e07050108010b07050304180905060a091a040803070c060902090916090b030309040507030207060516022b03090201050f1c0b091512070f0902041a0c03070803 78
    0x204041d0b0000d20f0200d004908100020b1b8502c12260b0907a10b200150b030f20f070704181c04607020b40030000340706900602050042c810038214034a29444001e0000815009a40b5100e1500d1000c2d5118000159200000400d000c4902080455103500c64140441c50400c0d99888519100041c600401c005001005204002068025041d10360b001000d80740c05007070282c0801c0e01c540e081c00e03000902840b00710001810980c54001c805001c500203015501f040544000e0001901d00240f200041580c01c0003035100040440c410341d4000d254a01031500c2060b1014006841c00d20142e1800700c1c00071003020f00e003607217126000b07119402c188540f03008907800b202071005075014003a129614080d90004100a440d10b646500c03120040848a0300070310104c444001441001c00c001e40311507a00c03100f05400d425940c07c101e621a5820391390402124607c680c0c80b01241c000c8103190b000b0121041d000502007100096894103244100e0740552864605601c0e608201c0c0d407442443e00060140c040030000030781191059 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 50512216 1250 50510966 50510969
    0x6050a080a0b130204030813050d03020703021e030f0c030105070c0506011203140d0b031006060507110f0a031103010b01090b03010e0705090918070e01051c050118030f02190201140d06 81
    0x11003056459503140c0c0350241f02600969905404070b1000200003e1074645911015050380c0c254001c0c000950a5800748510307000220a0700100748281d12504051303840800c01e4007000c2102001600705200c40310205800c1d140007801c031904022a66440c01d0101d04d0100392a81164603e20000c0b03007890b01458240c5000901070350014020350007050441c205409a0406005110124203658400212100c8a0211050b80c089e0b00c0004106021001c002000d092440f51004401495454800050000501d009020b6002141c1c407a039003000800071800c0902601c2d2610b136003400c01f00b030a10b0610194500c81e001c144038401048140c2800304405900486c100c41c04c440d0090100945840c10349402d0300c6119040d40ca181c110b1041080000740a4411860f2905035000240203000c10b00100102c074800e0b030310314001071b5407955803680036101150a0492000e480c6109032150050030406408c06424002040d80b00c26555040703400000040c3e03881280b0030f4130601d100341c4203a201c0c0e50503c102001807006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 50513466 1250 50512216 50512249
    0x2040204030b0403020d080106090504021305060406020309041409060610120924110d0e16030b0103020909030f0306040513050708030d0b03010204120206030c0f040e010f06050a080a0b 81
    0x103404814020360812407440369010750200d8507150291036040b41c020800344a0b810008203004411b2020703240a40043c014210f44007000c08075039031200000b030b00550259000d1000341c0c2c80002c1180050515001b190459107920800702e00d9442e01d0f550040d1a028020305440c0302d1038881360030074100c9020308000081440c074000304100070140c9103461216a890500c11a5500601052440420311030f8021505161249140799003008140c42e00807024241c0300110481502918554041100e10300c01c415000f580119010b101030b502d98014803c01100c0134100500741c4d0400c11004003200d10810440760030140c00d9030001080ea03210b00c00b031490100c040300020001e0064040001d15401c0010260a210704800c40400281050f101050300303e1017188900c041e414000c501e0300025140000c01345d40d1058a1248039482d004070000380314420b030311540104000028900c0140803c1c950417a40300090450360a08500c0c0c1980400041c0c403204c001004c40010030b0b02c4007000013842e12500106900c0c03809 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 50514716 1250 50513466 50513471
    0xd0c0c08030c1b011a01050a02071a07060c1103040308090a05040203190c090302030c100203190203120709120212010f020a110f0303100303030e070b0c1c1404090203060301090204 79
    0x420b03a4042c9025400958036283c2050081d008036900e20041c4511188400101841320104040301c0064440d6040408002d0540c012000005100d80d9003141c00e42084001c4820390f60789102625203a01292814055102002004611a9480c0000100711001d5a40100c0c06980702d050300c13400100540394903004550454008828000021080343c40d4083c0d9151003501804030701903460f42250708409601c4080d6041c0d120031502e414501f40080e440c21100283d01c143ea152400120031150149440d81800005900020b100055242151907140e005055031400c121040d143c411801c0000a031840080e11031390403611041104c100940c818244442050800c2d501c642d41c8140c05840d024030111003c005d4001d0000b003004000e000f0044900c5121201c103405003640c25500e04400418800644105501c070b00c082c0400ca00311800003804401d003031100140686991a4540e01e007440c0200d604100340900c640c0030000c0e80700240706581c1070325031252005881c0d540f4800001c1c05031a0400003c2d410a2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 50515966 1250 50514716 50514721
    0x110403060b040509120a080a0222150906050a030c030b0301150915030305030c0d090c240f091202030a0f05010c080c0702011b02060d05010f050a08120d0c0c0803 71
    0xe03940180340d0031082100c0810055850259842d00c0c1e18908607814856081004420812401660050b410000d02d0100506240362848040d614050881c0ca548505160020400c241030415014213510905850140d860901d0094090810b0049591038000e0646a00d44d03040007900c41e6001c1d000ca800000d00a00c00584600c1c001d000200c03481c09101e8429041640303009410015140d610200d03a4169949441d55445810802c2c2c560048840d03030030520b450345002400b040d1074403d0300d00940b920188015031286140d82c02c89502400c130b410031041c4103010122007141a00310101c2001c45219110043c6003880920002e814400c0c0b50030000c12140100b85c1c0081401815482050914402e458001d50758035090480c00c024014208001e0014003080500c03280c5540241550b00702c3e92018011600b000344110840090700c1098000f0141c10310022020055840c020311000000c1401c20003030640e8104425560a80c2c1c456400c00000082c0c4030344101d20040d20030b40100c3c00045e0082400c03605c90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 50517216 1250 50515966 50515973
    0x30f03020f07170c031507051c11030a1802030a14070801020301120209060603100513020d091b0b1e030705090d0b040b07030608191103070909150203040302060109090204110403 78
    0x842a48a983d24821010051150b04000552032030900e104481c03d9103503555100120780d00e81c0701e40c000090300014280403070400090340c0140f80540e02005810394803842e01402520445a4a081c41c4400200321100706026860114030f2164294004014500c00ca070400281c91078103000703a000c070001d5880000000f82104040041484a9108840c942c10075107404040201130302056540c1e800008508400b0417851030700141c0e200e03824400b080d0146c08c10801810040c00c0b90300c01c28041e47c80c0310200d4501d039513002c030440c118006007050030613450401c3c609290045c0b05d0300000c0d06c3c0c1c1a52450000115401704d000c0c209442a001000b4143d10120201f445c2ca80300460701918101c030152890400300d51101e0084c003442c019202d00c0300080544607800081c1c0d0ba45100142d40030b4800c00206850600da903101801b03180060400f5a402141031107091420070b50a11030b0001d40c051039071040c400c2c0000a0303404a68070f0304503610440081072450607400024003c28010305040e00c0c0c040e00060000c00c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 50518466 1250 50517216 50517239
    0x12051e070606080c0a121703010b0d0f1109010e031908070606050109060507020f040b04050c0714030906040608090f010f0b03010e0f0705100302040b03040f1202070501020601030f03020f07 83
    0x1003510420061103400c0d0b0b00d18205582e040c10305081a8007041c00c0000f402451150f500e100c20260081c1d04141e48152101034007a6642d20a820800b5002c0000811080b00c0711603004040101e802d070b01c0f0411090030500b0f4810b4140c004d90740400e04000e900800d00c0001c2d6001c02c00c58102681e6904901034000031442d000d216a403000030100d03445410240001103c1d03003d0101c8000700c528035181c107450120740c0e40c2003003418035000d540c560380559128401d151075211889010b114807007400c800e668420490070003442405070414142d600b54810460000303507448101c00d4404644090030203808c039031079210140f070424a5001000c1c000e503181010340250a0241d8020210541081c0e00810480e44899642a2030700021008850380c0d9002640402c000e04140f500e00c03410103905d290042c141034540011949170b1780107540944082c000c030181c05040c0407180e91042d034280003900040458919040010351074180c1444080c025022602c03409091600030312222020900c81001c1e03800d5240c070344108418 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 50519716 1250 50518466 50518477
    0x270702010209030d02070302090105090406020d0516350601050409050a0203160206060d03050c0309040204080304080601050a03200d0204090303150f0303020316030309050a0b041703010e0412051e 86
    0xc24440e06640d052001e0006c40c003101900d4004d003164005a0a1070309014017158080c10403942581d0800c03096104004078451240121144031410540040c0e11800800c12000255804403440d04808800c0f5100c8134884100c181e214000c00400700c554a21005907201d00540d4085d504682c24002088520345890f0b0066101300850013904a80c40205103049a552104545c41c94216124603502400b00b0300a501030074ac4c1d501240202d038a8003080401240590300140d11100980d4004a01800200000e000701c9024100a440101e082c51540d00c1e006032407948030000d43c03220440032114080070b4031108281120070360080c00c00e1200424510f0001e00405510403100c070003070400301000c00e04540c4504007600b00d83d0164011810002c20000f44103541d68404011003d0658508e20710b00095010b01101480c14003a03201c2040f180f40508041b209543c0c2c01c01c48121603c000c10060005800c6862025080303500003440001c40715048206a44500c5030641e03220000c20340c80c07905503004a64100501 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 50520966 1250 50519716 50519719
    0x20d080f040906170d0c060608071d06091b07020103020702041d01110a020c0108100503150a0b0a03030801090221010f03030e030316030c050106180b03150c0405270702010209 77
    0x2c0002d561306140204001c41c00001d2003c0c1d000000c07940c0c40d142c41910300032440780c011440064a03030f9070340648a1a000d4943d01c6041c018052101c40c0e140ca1480e8021300394049000c1e40c0c00792040ca406810103011503041c41d0030200700b007000309416055912907819030380020b03400f41007041221082013002909071110200c10f0050341c00c110702c5030070100540042d6000c10b030041c2c005080c200e1420300103503040600103180c43e0715050302460002e8599000c100086c2a00c0300c8041c4d04849003007040e61641503460480c0c100b0702900c842c0030308100107503000c03401a0441c4c040b282e0058403025030076015019201920305a8418a1044e000411813002d5460240c040344d2003a01c80d100e0b113001d10014591280100b00c051111124009032030710203c1d000f401c0e0b11010510407400005c005440703c803140170b440580b82e690010181c3e143c4991550b41810400541c0c4401920030400407071a0003424042c1a116134002d903800b65101520301180303841c0341e20790f0080c24110349004c10070901c1e0100d0b000303000750015480345 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 50522216 1250 50520966 50520971
    0x30c06030709080d0c02030d02010c050d020706020d02030c0a1106010f06050a02030c2b1d01030b0d0c0801060611161502030702030709090c12050a02040b0607020904150f1e09020d080f0409 83
    0x1002703005105000256119840c1d0b81e04204503940b542000303410241050b505c4903007c009400d4a040640700071882070000c2d80206459101c2000010305590340181c00725105e501000041c00409516500ea00444403640b5215642d054421022805c500600010a90500c0380c0000c03100c40c1d0f0648114944040f50f4590000350305550500d0488610440c2c0f00300030f41120851a28100d0b95119400401c49440098500f180354101035944000784019a03000800c0d0365502d0f40240f0159074011000124060803100600300303125101c015032000803040c4241c505030034415154501d03550090080d80d008940007400e0fa06100d5407000c9400107130000078406c80d09468102008145102000700c00032410b60020000c0c24501c2172542404000c000c80c0ca0707600d40c00070061101d43d0040c5d450500030351007648105030100b000c0520000d46402d5640c4513040d120881d0030300c207101c16a0310744402c000d0503c03e03240002141d40300e002d0000c00c142802900000d042d100c130008242d906400140014412a150380f03004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 50523466 1250 50522216 50522233
    0xa03020d0c03120504020a170f12071208060f04020d02090901060314040602030a0f06031406070e030c09040206191d10050703050c070e0a0c031a030c06030709080d0c0203 75
    0x1c550310300c001100103020500b00400e1030500040b0358040341d072040c0301616082c0c22a841e18811700340890074111021035039200b6141c0304020042400303903d542405461645050001d1f03640c03500e0b840c440780da0401d0204010500040c4030380d0307168801581d80c100041c0007190790352850366411010754000d8420f503002d02d0700c8800009840c0c0c130070300c18070441c85100e4004101540b92556514080c0d80301403e40206991145989825014a03104a000951107030258002400480404a041280003803050382800700068446407581ca01241d01c0c00902c100712855130b003a07511031000408a00500240c440c05913100307044415620340001c001c09900400c1603118000d000000c5c200a00c5c91491007055000490a00000000074020006402d84882e0581504c6120f501c5040d80d0507000701c01c403450700340c00c0e48525003405020f805100c1c1540200e050051130b41110540c0011030340e00d47c4a0004c17140611000400210190b1182d080c04c1c01502142c1c0030b45906200d400c0d002130486e0300d040401e83c80790080d41413 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 50524716 1250 50523466 50523493
    0x911040302031203040c1e050301020409020a0e04050f070c020613030f02030f010203160e0609040c030f0609020c030901050f04090501060c03080115080703021606050408030108010501081504020607020a03140a0302 94
    0x58a1013941d210200820040c02c0000412402000c040c102c1641f925071a0081000c0d40c080c0040c0c0040c000c50040140c60b01c1d0b059078005c080c0282e0060b43d90050780703880d0034000408550140164410000c1c1840c241c2c03820b440c40400e64921541c046c90b84007155421010040244003200d400000d80200c04440040c00c040c9041800c0348000e540347e98100d8074000000c100c042c09000d00c0d440d030103401409107042005e940c0110303050701c031007000c5480000d54a2281d2038407102c492040c035000e0068110704605100c841c1d607c05070760b4420304000314184440820b514443c2c080160444001c0d04043c032080c0440d59403500060411510380c0703822400708800b10b002044003001c0a0300404a072030f40e944d46242503101d0071000d5009501980c020080315280d00e600c0400b0413210302520f400340380310b014800c0c1d496240c442000d0860b5410780120441340c06c518840c0d6403003550207068642007074041301c849550382d210740b0004000342040d41c0002c04140442c200d0100034100032400c009110b0081c0c00b0355809004001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 50525966 1250 50524716 50524753
    0xf0310081203040b100b0a02060f160909020904020f040306090302120306010e0927160503030a0212031f080604020109060806010c03031d010e0a03020c0901050a0e0907091104030203 80
    0x96800054800c20b100140c046a0b1842c0041d4001030b0101c40800d4454407000e03000030035800902d81c0d00260340b0030418480582c1d4180441544a004034040c40e850802d1b003074000300381c1c10f0383d841a21030035170300030035845c03d02e641d141d049558450402c6141c96440e5903034034019000d080c0050307045d07000d4000c400710b442548800504803841003c05a5075a000000300790100110840d0180096110800940d03440b0001034241d00d18201038018100280300d04d40f0f00b400e2906150300243c2086000e50011b108541c0d0352a000105050b03800c4641c070100c0c2c2c4a6503070740851540038141507100c41304103080041c0000e1188000c90b8130780c0698001e03030f60407001c103880716070680c1c0310b64041e41d141d80041c4801d000344000c2031083d44904040f030510f04d052101501c800741020300307441d48600611b03250780144540504042e01000030040c418015100c01c03100750301d01400138110302c80501c540d400c2004c0310b1001400709101800302401814201e00200885900034001040030303041030000304e02900c65040d4800344500d016 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 50527216 1250 50525966 50525983
    0x7120506010e04110913061d06060301020703020705011b02030a0303090201030b090105010801060c050a020a080303011509051f020109050d0801140102072301140a021b010309050c0909070b0f031008 87
    0x2041207040c124103c144400317980001d104d03103588801c030510000040c60394012000040d03440c1209501c44800d200f8480e0802c4005041a03102c0ea10411010000a4020480780d04a0f023090a120081487d12180600e000002c814000d41c0760191030320321340801d41c159010f8240d0134001e80c2d0406c40c811540c418054602c00038080c403404552241c0042010340c1c0301e0300620304014403c2d42550101d26080d4045142c1c182d02c1e401900c103a410200040c081d1040c4500348104101a0307140c17090400d0b14140200c0e861200b2446256014241882404c41886c001d4100b02c04082e840811150400705108009040700002e000d209551034000045a4442d8800a1060143c640032161410b400060700e099162120a4483c11030500504c680c9103024100c0140141c035401d41e180e00500355040c41403144034000c42000d0101814503103811000c030003046000031035091005059501e060641c03204401c01d450b0882652107100198800a081c907820324000000d903000d101c80400760388c50b1586070700f80c441e260840c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 50528466 1250 50527216 50527223
    0xb01050c0a1209030506040b06011103031b070f0b15040b04021e0d0b0904050a031b050d030515060a03021b0601030201050d020d0204050d12181a0f090307120506010e04 74
    0xc0394072010440c040c4208a01000728148101107660f0380e519542085404c4905491100d125010004070307580040352520286a0000039525600d0000b442200054158086d4015000c020035100c04000003280e081102c182c01a0301002e1524200001d0010301d503254080501403402e1480240c200d0609000744d40e1501841a61200c6135541c40d9001090394200020345008a88c036203603442c03103d49031004130743c1c0202d0045000e012062518140681080300c1104645400840c0c0b008c48008280049a052484589071501180d01e4844070503042900440c5d05a06ea44030a000520024160f0941e0041c84071031035030080f511960f0280e44001e6200c80003403101a010400402220020009603802840e0254410000509080d00d841c04906010344c58001254560b00c11b07051501d5807070300f10340b199200d0084148958000347c10018140e8070000480010041e1002c003040da00c080101420545883e05d001070100c0d41c01c40e07a9070000d0030b0714804031a41546e5a0280b00c001040701000742d00d20701d104541 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 50529716 1250 50528466 50528473
    0x1503070203040501210516030e0c01050901081005030607171501020a0f06020d090305030414011b030903031103090a1a0103020102030a0c0302160b0a14070c150504150801090b01050c 80
    0x6480010b41703414507500c144942c1a44c10032100028000180704080c007e0141004441c0e142d0541316020b000c40e915440111190341c060710315680c041e0ba01c84c0845510b0a001c3c600301c5010740320340740d00f2140c3c640e258019a92500404080050300c9901c426426001c4818124001a0b61200000c1e001c1401040d081da42c0103801000244000c02e07505850450090701ca501e0043c5403c074100d071144115062590308a00180e0008284001e00031010014034002c00201d000704144030020a40d031141030709841820303007415111010601414020390004c0700c1c03184516402a038a10b01445402e4032080083c0088820a4025071141c00300341c1d4440c8201d0690f82c0c180c0095241c040c0c8500161500e01004808070210720a0340c80032001610000120801010408030701c0341c50f400440700140420b2941e25400517100380601c00e0b980130500c0c02400b80200e442c00188000424100d01c01191984501e80000d600301a10310040c105040e804480d2038101c0d0105803003000081018001160148545d8260070807550 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 50530966 1250 50529716 50529719
    0x1b150403170f0c03160c08030a0c0b13020a090b01090e040c090207210c050c030c06030103060b0402190206041b05010206041b1a13120b15030a06090b06150307020304 73
    0xc11440082c51600c02122002e424907100410680c9554061402e60001c0b8030b0400c0d00000300a144c41d0030602030143c260255091a2000c8002800702e038110300c4c05440030f00c00b4808600c05002400356292144e8000d0000c0724290b8450242501525031041d5550000b50942000142d130b5804030403441c044c1d54000128111245031001042c0070b50400c0005440c541015900a00300041c4030002802e040d5158954510315040313401d2290900041a0416000303800c15001d001300c940d00d000480c0d042d294446400a0984400400700c1c00900440007848030b2206000d0554a509400180c56886280705510303c00c0806588402d40030b14200b00d2082d240582d2000012030005166035000710b80140d03886494401440c2e55942c00161040c8041080801200000e64a8541020351301d4202c0541084595500b810f602969110411300b4000c0550940b000d500180114036a8244400e0318181d41025080c81800c9450a04200740078044e2440361141000540e101c07103d14249040d0b905c240c01c190003550405 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 50532216 1250 50530966 50531003
    0xa090c020d1409091602060c0f1c060504050408030f0c120a05130209100f0b03060a0b0703020c0607060c0e030a0b060f031903050307090603060f05010507141b150403 73
    0x5442030742c800a4598024803949000c2d03290070108a20800c80d09801ca81c08084610000c1d091400240070301c00c284c1403c11480710010134690403650081c01c5900400c60070340510f11103000402441c1c00103076101e8108000c1c041802100c44c0a940902214140340302c1640343e103102084180300d0750410380300b91440d11002a0f148031442d84000da2203000030b071540c055400355600040c42d60341c0031120107001d04010782060201070030060408010300b01080101d4078509004001541c110103d02c600c048040700000c001080620a1088100307140f000380c41c550701c65a480c0351410152000c07000240010701713110504000b52400081420501f1f8211018a000391a28801d01890302d407100303490358040c45601802d0090202e03401030480790a020350740307080d1030f410032280041c07d601080d840b400c209800c24400b400380b00147c1c086041150402d08105a0f560014a4842c80f02d099146200030301c0c0c000d58151000004401101b90081e5101302e07107507204511050311001240c01280006080b1500d00424041c00e03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 50533466 1250 50532216 50532227
    0x2010c02130b1002011505010804020a0b070302031c06051503100b090a030506040803071412220609030801050406050103060f0e090307020619021c020607030f02041a0403020a090c020d 81
    0x5400300600e01240c41d8003008041140d001440740c0603c0180e41d10040411920399001040000e040300f4607010000c0e08090b00000c41030145070240b0000b403003000a40304d041500800803a030468403079540090b11211401d9594004000c00c1c480c0e24010070400300c0040b4000d092004030781c480c285000c07014a40901b02100e01c2500d42040c00000e070000b664202c0170021800400c00b46102d1403203800d5680d070303074542071900510500105115142c140c4c000e200d204007403009080a140d000c0d1307100e01b11040700324010140e00d4003801110f40c09820355151210b020241644070541d0750603100c1c19103040c0b04c841e40e038100444c11924540719400303005090540078003450041c1d580f1590010768000450b4206a10f580005141d030b44100381d15182c038400d16210b0b9078061b8043c030031000385d4000c070041100880c5c0c1240c000713911803100400d80030400d43e8880080d0440702081d03060360003600c0500002400817844200f203606640c004d0100b039209264402d00020818018081d020701122180d020700061414118103403039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 50534716 1250 50533466 50533489
    0xa020307060e030f0f041703040e040605070e0a0b031812090d15020c03040305010e0111160312051612060308040501180902030f041119170102041d041203050402010c02 74
    0x1003e00007000450301402501000e00b128003000f40300c450780e640c50919003404190010202e00515001880308121803050300141720f1f4403c0d0028000b1038581c1c3d640c8812a4a01d007540312042c0d0104c00980b01095403c0c0108c00307184030750482c020b4480d05100340320040c1e41d54004203182c1d600c0a030307013046010883e0800c6d0000d80e514500c0346481c0444034580386102402c0c5c0c2c005400482d0035a001103420818820240074001800350790200820044070140c0b00c4103c1e921030030100c500d0000c3c0300e07074040c0308240c4500002c00031008030642c104000c0c1080191a4011189400d000c40000c0200ca00704903030300780a114007030843c1e41c014009803504d440e00300103461849480340120303514554184001026141400210310803840c590032160586802d00d4085038018052811501030104d08c05015803600c40201c00005540000c100308211803801480940a407007140c00090001c03c0e41242c0030040c020f4112400c0c083d83c410001c2051000c0c00140c00c0b42180c408860103400150215918005410b06c0040712a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 50535966 1250 50534716 50534741
    0xc080c0a110102060a060803220801050405010c090b1215060c011103070f020c1305070504081903031a0312030c0d0e0a0203060c250c050303030702070f1502070b030a0b0306041103070603020a02030706 88
    0x2440c9da65140e4025013110303c100ea00f41d600c3d0351103034886011181e104070424003400c14030311001d0804010360311001d0050b03801010714000c2c40c030080e56914903964060560f401c4000160082c4a600c030105642c04041d0010755402c00442c0007081000b2a00d4000b2072460f040042c0a13001103848001001110007900019118a0034003404002c0810988401c0c001c071541210b00c00200650f452462400404580740d138450001507200c0c0b030f5540b400075034000ca198030320702c035424482c0341c0c6903120040740d52014424150083c11003031500b1203040111101060040301c00b4000c034251021a0341c0d00190944c9442000503407030321002c0c42e2511904500285842c140c0c801d00500316460400c5d19400401d107154001c0e5a200e015078402c80e8200800041190703104040c00180b005007000c222000400f80d030b207880340d001c0c0601140c00480065001c4086030301c90030329060018111034403824142403002800c0240c4680324004c0c01145030101d030302402802140d44030055a4002c520b0620503440e00d0004242541448 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 50537216 1250 50535966 50536027
    0xc0c011206030f031101150e04080d0908070303060609050108060609010e0301110c0705090109020708030a090302070f061211040b071509020d120e0d0b01050907120609060603060e04120c080c0a110102060a060803 93
    0xcc00210300014040c200c410300c40e44001802c00e08028002d880c600302513024504010300403042105544034007007501c540520a0038844081d07014980040c0c05461820355249069101281c8000202030000d9070404554061710408c40c01c0e609c441c0e0381405c5c0c1c07207044805081c1e03220420106102c1052580711554880c000c0c4181e030349407034a400c121710002445600c04e0001485002300203294000034406d44840f40d02d0744c0d06d8940fa01c4e24142c181c1c51903000d400e0000e0304124203004414041e1034a5040041d00b141d00070403441e0b8156461800c0c40c0940420500b40c03001400d034800f246200d00b003404500706010b800503003800c00341c1c0c41e06d001c0100c0d8041c000c08104c10400d10115030b4109086074003030308014041c41003001c00c1550400c1002030848600c0c0e4001400805100c040c4004600c0181003030740640031780e1802103401d1140e4140918507208410b201c000303512800300180203000016402088210090342070b900079490300c0c2c1700d56055130454098082d598104000c1e01c881010b030b00c0c99a01006010620b40c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 50538466 1250 50537216 50537231
    0xc040b03090a12080106020607080613020c10020a05030906012313140708091213060e01021908120f072007120c080607050c0c011206030f031101150e04080d 69
    0x10071030031040302c0f40b00c0d40c0400c00540041c0300d0700741c060104075030150b00b524041809181038800942c0c0c01003001941041e0541c00121908050804d000041070140364280c19943c51041100040181d40b088540000c980920340000c502d070003e80c00300007507444601c88500d4103e111001000700c12541d80120000c92686c4091541e084400512094418079554031408500c4c540140d442e8180441a121229942c004100d0b00c1503181d8018a007000343d83c62803034010b1241280ea001070749412000010300012408200d0040204000c640c000c11316a0240601e660307041c0c4607908810340b4070380155503200100c0d5081d41d06d0296a0003489140c0016881482114142a910005244500d05210041c0d83d42101801c003400001420491290803460030701e0414641900581c84039112088c00c8951410003010b45c029250042d0903400400146420038403110285040b8500030f810f0041410030351980d5400c2042c0c0e000d1825150220b10f048640612480704256070303507541c1340900d50200c50a0245195590b01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 50539572 1106 50538466 50538473
    0x106020c060d051f08030a090f150f0e0418050d020604030912030203040306050702030c1e0a06090f06020a0507030e1f0305150303030a0f050f0c040b03090a 69
    0x1001a054036843c9185208603c5600600441c04c118940800c5808002c0000c151411380c0d6160b241e041c039a02c140005030080380307215035480e0203603009007290107600505180c170400380245004e0713021102d448000780854064a05500030b00002e21614400c000c0104550385d90621180020700407442c09039801016a10103005074a0f0080b10700804004142c003c1041d03402171680524203000500c2c02150007541c98001030740000943c071441d51060549196030b074810011404160182c1035808207a21104003410a80030b0880d5484c003030f40d169501192052010705440f10710b03075651a6481c00d441c20003d090f01d40c80e08207184200c001980000841e4100e481d0303946a0421420046400c0d50f405400d0004140b1241000f03406000000420903291400d50042580140110081025417540c00a144000b001220880d080c088108001e002000c1110702440e80100c0a1007200e03020241075a = true := by decide +kernel

theorem cover : BRFrame.Cov 50359716 50539572 := by
  have h0 := BRFrame.cov_init 50359716
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50359716 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 50359716 ≤ n) (h2 : n < 50539572) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
