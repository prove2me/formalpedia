-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4482
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:46:03.471954+00:00
-- url     : https://prove2.me/submissions/ee3b15f5-f6db-4d26-b9e1-f5804991d0a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 805935251 ≤ n < 806115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 805936501 1250 805935251 805935329
    0x504020f130b0426120c0d0206060603090d080703090807080307031a011d060405100203090316060c08310602011104030b010e06060c0d08010302121b060c0c0307 71
    0x100071300003841c030380b00c045101000e850320030101ea02d10345000b240382004603000c045856802080d142d9030410082089030311b00c0350644c01c460454071942c04221061106945114903a482085901200d90080100503840300c2e140c1000a00f120640d01c40c1e2000d41c3c4400780071501c0c0d4500004100101d41c043c400c100790b900034090002a500180030010380074185490703c9005401054180e858140d03500c0080317601500700540b503074103484100003019503240c020320503561081c0210401280c009242d032002e1011100c0c9941d030241d2031205a102c06c0810b51241d8440743e884041c02d114190250708070f040462005a01d07620b820b07007481c40d014009007110740000c12100d0410f0100010004a42000b4446055850303502c9880c520ba1600000074110b40715003030000496000e102a80d0201c1034200750494100c4c0e0080e00c7d000700c8180ba554115444c0c2d08868020340c1c3c81c420001c0d104c5140e040c80e00142c8036441e4540103c424030800040001e1604074568404c904002d102c10807442403a040e5040e44800800c00310b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 805937751 1250 805936501 805936507
    0xb0703031e14011e08010f020405121c030f020919140a0e06040e2415150d0f0b0319061802092d190c1b02060c070504020f130b 56
    0x1580c01a102c41031090704040c8880300318000000c50b10089040c0201303030140082050b2004011100d010390082c3c4521442002d0260025410760404a0f41890100030704002002d2020312802c142c00400e140c42008900070b03801d010148154941c0c8084501d0704811814917000c02e4a0714461080019605000702d001e41e1046a0411803e084108820f401281c201c0d40420b010b600d10090038904203909244c00d4071580590111a10f12072590b0f00d40307004000e0581008409503041c001d1148949840e091205010030401800320f9103a01684844c44171910501d003c148489404002898150b000b80004403420700a00342408015251150601101e01800a1680b02c1c9142d00011540217000300039168a40d0b4042c4042c0104d4060303a5403106412040c5962095030511400109240703500c0501d00721028070380003001c50071070b0241d180c40420721800081000e001c030203542440303415009a01c4035195881484804a416662070010301008600f83c040030f0b0b10307840c08202000705203009a01104002e2010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 805939001 1250 805937751 805937771
    0xf0b0601031503031d18010e0906060f0118050a090c11010c020706300203060306100e0118021c05040c09090309170a050709023414070b0703031e 64
    0x103401802c11260581081c04036890f40881d040c96500b5640d00d00c50740521070711030000340c4034003030300242e410b8440320305100c0c0495450301a810380d00c0340d0540d42554090340801400c2001c0d84910050a44000340c0e100a82040340e680c130201e40300000341e400000074a40c5611100c58190780c0000300aa20001c080004d01855641e14000382d01c807409402010100036070180c5204a10281072103800500307401c600c0210054000030484030007908241c6180380700b4019100030400b1441802031070b809640e0109441280d913441e0101d003501e81e000a00754082e1068003032041c100e1041c1040d03030034030120300800e03008102032405141114000030306400c00c88001c0e180c01c031440042640820f2032000d4540103c0c04180941c0703610642c0d440c00d40041c0d0010480d22907544042541aa01e4000e403403d010070303c103502030320340343c0b11100c8404072905803c402c0c000c4c1c0c5103c8140042407628075041c02c64201041a00c00305a1903200003001170740f1520703064011079190401c03401b004803480070404600382303203803001c0000f8400703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 805940251 1250 805939001 805939031
    0x70614090c0a050907110f0703030302211009050612061006170c030a020706060e0412090b16061d070b0a02060c09030a120219030e0f04020304020d0813120f0b060103 73
    0x1002c2c0581d0200403a950006d00000c8040020020745800340e41140c41441d52860018044d62000b0310403041000f5040821400f081d10781495401011100090041941030a44a074001c0030024070855016a204140b0000034000b03110443c00b45800c2c2038a544c40700c0c10082d0141040d0707042032811300c400410300100407007815420140c9410803068180540d0b40c1c1418207000014100c25002090b080b00c0c0b0606200810144689004100501c0e4864240d49555807201003a58004d034001c0303540800c42d100c1d0704000203919502203c0080440d81e00f8007021002071031600e1030000311380c110030b030707820000102c00c0d0543e43c041080503402a51818041e103445220b00200b03840d00d81140340140315105603150b0650681c001d00c81d03080a040301d107680700141032440c01e000304100003000c503d80c000d221030456940541050f000322071041e9005401c055100c1056030b555034641d800300300798443c250b84401c0041114a900c01c5c00081540c0a08409401102c003401d01c400401d40140949050518041001c160240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 805941501 1250 805940251 805940269
    0x60b0a0608070f23030f0f0903130b0d18030503010611031801080a1d0706090905010302101110051302100215130606050402030903071208070504150302070614090c0a05 74
    0x126440e0040261603022080141391507901081c00d05400701204000700e0305d910f0380030140b082490700707a00405502d0b83c410140d124400c0d0800d9041003101808280b05041d840d00050070811860007000440401c001014041c1341c114200407000170740c0000040009d15441045640c4c618200400f85161409001000b003090740b1f402c0c00641032000100c00a0301d00300a542c889940e107603d90f230890b031810307110340702094985d0040d01a4802040c25000c0100d01d002c0c2c14495117050740d502a05c80000c5414a41094810800c4a0820710035841030540b0202007860310b000c0c981c001c81d460b0340802d4401d411481000314001020140c030045602c0012241c500004038070f82140c00c540603204100d01d071441428001c02800403504102e400c14000000d00103003020020003003071024040c021406442c450540d04a40d1001e0695468000820a000911000a2004803450f01201a080041c03401044c1d5440505513100c660721940642e08038010020354110900c019640c0d41c4044488442c001e023840300281042e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 805942751 1250 805941501 805941527
    0x603151107030f031e05090d0305042a0801090305030118140402011b140d032f0d06150c05160e0a02031f08030415030b100c0816060b0a060807 63
    0x25030780c550f240e034000c2e407050400f44110617021691043d10071000d03020300802c3d10081c403280304009042c0c44040c424070406005903882000c41c5280750041612240003a624001c48050f03440d00000010702903000d10a042e40f4620a841d001d4a03036241540901203a69050f807180c080301d04000a4000c2d0703502c9408002c0c1c3c4540e09090404000c2d02032005100c942c804004000d0900e03c1d21911014000c90005206582d952641c0d018003e03c0d09204030001c2e004c44601042c407100101c550a075081a07043d030003414903041c00a000203846580d8504450300c00e20300d5050603011078040c0300700c8400c3c40010700000070f40120001441c11035078903040a41109000082030500d89039408030104016500c015011031854480f0121441156166915507860784e00c0f601c103102c00890380d8490070346e4050003409640b5a0381d50040078210040510402035461841186045910850420072600d045100c1c0c40c02180c01402518006810090b10090060307102c03a5402140c14807072000b081228a5501001603500c0c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 805944001 1250 805942751 805942757
    0x105030f040303020d18060b01020705090739020f0603061023030f070f0f090915271505151b03030c210601230c01020d060315110703 59
    0x340d07541d0074114024050750700312000312400d0408010407051580d4100c00d22a00810b81041008030302c0d001a680e0f0f0700d2a1044a4100e619840001c50507401000792050390401c004100400140c40c01e100f5041c045180d030827420500307019103c070003035090102c45e0001400065540302c3c80d41c181140010b8080992141240410101ea03013000001c40b24801d01c00b40c1c06a02d16801a1a8100306075850340000003100c1c40c50010700c0c05100c0c00c9840344a140c51400e0640d858881884403130801302d01001820503001c00300f03201120040c001403400e6135081e002840d56102c101c03100004180031429000c1e40c07104034a00c40c0c902c0c0b800d481072040f50386561840510189600a060f5030390407010708154660303c0014100c00a00004c41041a540c805000503c0400510f00d00da0032228250368103102c06000c140c44440c00074a990102c1d102180d0b510700020300d03013706074002c40d083c000504002400d81e40301600c001d1646845071420070812180542a0a010300350138814400725100310b40042072401050005010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 805945251 1250 805944001 805944031
    0x1050d031701090507080c043002120d0f0305090c22020d02090f01020102071a07360501021f2003040507050f03010e0a060c090e01090e0c060405010503 67
    0x105402210700c11492051000c2440c030a40e0345048100080408072210404078074074000085810321800b088038141c8991391240200c240003031011120740859902c01800902410000c2009a681ca0004607198100c0c1da00402140301c40036801080c0300c0e0103216003001c1c14104014049000c1010850b10700108080e6516a10301880c4074148800d943c082c00349021540c0300040c183c03517113507d5400410401c0d0056405000c1200e11100480c200d2150660280440f1411003007071007980854410140c01c008035142481d00704821504030302896040c44402c1c20500459107106100d071125020b00001002d09002420004085c0c0e017034502e1980040360741000040d900c3c020728042600c14500083d000109001c02c03900c07850b01c0d01c2e20a81d01c0b01c290090511030495410403542500d414000c06140c0b40786c500283c500d2050581c0c03800060451402d104050010f04400443e10040300761006000342000c05001ca024561402030b40c0c1000c038001c00b040c0c00f03401300300003c1c003030b50341c01100700c070703003004a142d08488 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 805946501 1250 805945251 805945253
    0x5041101260a110a020102040503010614010804020d02031002180f2205100f080a021513090f0204050d08040611191e05011d24011505120a1a0d0b01050d 67
    0x100f00107402c40c0d44800c0c0c0031070710b1900e0f0b540c1540a0420345600b40c008011868852614a00920100070085d001402090020f80103041c051044804140b0103402c4409500c1e01d6440c00061f600320f510011704994480c0a0071542e8a0b013911444242c000c2036562038200080714510421111100c0c40106907142c0300e8ac04102035490381c03942d49000304032800d6144181500c89032401d8440c651200709a22076031324004240540b807102d6084a071010080e0383e40c030320f08030328200c42040545100038241d03240300e0703003400001955110346007400d0280b88908543c0e541e40741001400b42101c02008100840799015003852100c4080130707100c0a01c2c03d5008a010044007203001882c500480101e00010115420f00761200350ac1001c01c0b0000f40a02101011703242d6100040300c07048200c070a2000f201202c0d4220600411001d4107812a07601610b0103450100c0c540302812031420019001030300c0040700d03ea507800c6102e0201d00c212a4034210754000715400c90701d41380325480d45480d94406000d914850340c00030301404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 805947751 1250 805946501 805946521
    0x6030a031d04050f0108160605031303020304080a0804030506100b03060d11030d1e050c0d0f09030c120204050108010203041a0907050a0312030509070609121a0a0504110126 76
    0x3071a0100300030410700040c64903503042c8400d00428880c1c0d444910a80d141d420705290b803814241c0594155564030340c15541c40002509100c40000e9050303043d40010480032030483c00a01000b40d0841c018a1807d43d11032a45c80c149107020740052a0800001002000340403001300b031011030381c100604451b4004800094200b25140444030042180e040c401d49030483c40b02c3c0c0d00003440c0c440d019078440d21120022401001a14036101e0055410030325040000c103416041e00034240e680001c611403400d906450340f81e40e02d843c1802565044000005c2118043e0400c511300b071f0007854050081c9000035405c5051568800d042c1c40220036862480c0d010140014041040c1004500020000284220503496407800c0558004041703418100000341400002122000005620811126969900c103145440c1c03404113008900301c5c05d001c59078030500a41303000742410900c013000e000d800c410600107114103061412440000b981c5003443c2c180420b01c480500302c184000c0d804642001c511503658070f942c0c0c1e964000703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 805949001 1250 805947751 805947797
    0x9031602132a0f0221090603010b04050301050109060e060f0f030a11100c0515060a15020f1b03030a03021612020708060603120306040c0c05030423040506030a03 71
    0x18250300d06000110b080514200c0c146a080300400d82c0c40781d02d0302c0502d08031400141c44440303c0c050703400310a8018005101c07803482518400351030340b40390921240100089842c5c2c0281e00000f40e200020900303212503c1d0038410180141140d8104010140c9000b60700c0c00300f02e1008240521841c40b0212580543c0c44515001550341d10084c10b803080003110381b501d050180c401666060141c03410101514a842c0124000601d00d604900144210300f540d100f240b0b080c0134005c0c40c207030700100310352030000384150203040c091140580c503009054500350a1510340d141200b00090018040c00c00041e210b810303140402198213109080c42d001d61341d0050182c24280e240c0c0a4400104101c4480400d20150340e0301041403015108590180d03020707501c2e40000c1582e81d420492034201c280750100003144030361030704e80c0c40801354900c58102940724039071588403241140c00c40d078843c7c0d016104c18800c0d900100c08a082c030002210b2700300c50810090a052010036034a18001d0f0004050010310360901d03030408010711103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 805950251 1250 805949001 805949029
    0x1020c0913050f0d210e0a08280e1e0a03080403020102190330050a0b010f03060b0403030804170415030f0b0f0114220311010809031602 60
    0xa09106800c01c1c9840800d50149400140c0b240c1c00340b000c03500f90040307001c100301180301c020b42c3c1c60f008241c003092010007912820300e1450031501c1c1d43c1c84600560000030300200c2001400740604a40790048085c0c0c003011460800010b42c2882d146034001072903150041801c468044095501810226001240c0300c8a485407215a80d40401002000070030881c41da801442607074400c1c0d003500c483c0310f041800340300e00711103584005022a172001c1e60001d030340707a180c0b080c0c03500700403110a101c80a01485011000300d50b42a10340401482d00c1e1300c0030b17074040d50700140c1015400c3c1c21440c00300700c0c16140a1881420340207601008042000030f40218043c01080c1406d85405c2d50240d5055550311b0b510401c2c80c8000c060160340c00040b07400c040030461140e4a0340f240b10b000140180c82c0a80c0320780070100440b03540c001040e100c0241c40041c0402c050b603140510303284200c8603016101075080c908505104240001c42d401050402862004008901d1400b20940c0c0e2055894860b183c008600d52000a51503549030b0300d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 805951501 1250 805950251 805950259
    0x140f0403031508011b09051c08070c0b0a022b2a0213090201030c0516030c1e051605150d0c17070309060509030901050703080a0e070b030a0e010b0f04090201020c 71
    0x41d140c2201c0751504c107071489100c0030f6100c125580d51f64070217000a118050aa8001400c28900e00c84082036604000341541403040403000310540c7c5680340004150030180d40300f0016440b5100d03000c40f03d401c000740c149003c00c11607000c4141003000c10300207041a03d401c00300c00031000c000c22250144100c05010b09641d03a8014083c588254038050709070000d081d40c09040e03000078103040c0016a600d0140040380d0245c0d481e0100c1921200031900c05075a20000c20004a803030920740c108018407036a00100e05030182d0b129501808260315000301d4a00d41c0070060b000580b14030806510000c110a62500303e8122500f00c12001c03500c68800b4400303454090410f898200174102d444100900d0540c1640250043d03131160004110307544559034903980d2405900d440c140454410000103000c0b9000308082e65000c1f409840200d41400003032451400c240a990201d5032450f0080180014003d550283c1404164410002c01480404900142a402010300c800380199520f50300c150559200303214103205810090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 805952751 1250 805951501 805951511
    0xb0a08040c0504060b070809010207090f0b04050f13031b060f0605090a06030b010501051614060f22021314070207080c030610060305100e070e0103140f040303150801 73
    0x4058444141294201c03038101d852040420700d46094032460090310001c02e4020300345480d5981c2d1056507072114003401c1c154451000c0c0054440c02c1800b4a034681307901c0300c03400310300860008148400e50798050082c0d100c0c04c054008100d8400503042c031030110b107901881c2ca1004155002c4a0000e50405840080e155a0900c00c0409901c20150821011140c082e5a04500f0350b07034400b10b05040712000e00006254071941e1004010940c4184c01400070403020010769035040d68030740c0c0e8040c2c00c82c18180e40c0e40050b402540c1080119880c2101255000240028410704000040c00c4245420f9001400a109589409521245007000d07071040d40801030900d6401441d0900308006075446e4800d01c84c0c0d1045101e50790314860241004100f45002c0c146084030350101c80e081120982c06054002c200c04081c0403040c60000d021340135200400e002ea50030783c4030030f0a1140d20200050540726042d14881101c00941d061000f002c4840e215207600039054500010840059071010f40001282d5210b400d80358280303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 805954001 1250 805952751 805952767
    0x6050d110613080a06020a0e01080637080d0801120f150b1201060f1a0301091113140109051008060d0503041e090507020609030a050c0a1703040c140609010e0a0b 71
    0x46c1d1700810f00d0041540300d1160700802e00c001103514a80032508180c0001e1004010984488285031112101c000c0303460341600409004c50401c0d4a4200b54081c583c507900000d0380410b031075040601c181c0504a01c1c00c51002c1541544c4440e034006500050003003180e07820300d60065038082150b000541860000b4501100d03a00740a4405018044070b0140220740100120001a15000d45441c2074001907600c0403907046a10740720050340101820000c2d020a410700f0400130100360b01e000c0d031030400342c09000080301c1004900400182030031203a400490141070340c84050800c03183c004050591007501180c12002400340f071300c0c000703003180a5a4820908030f0007151f041148460035000e200240c0b14010300401280d660b2040490f5108010740320507015420401c18a03030010b102c1e400500c000b5200c141103c2d049201d6903100340d00d00441d04c8620f41903484c0401403208000803421a440200f1000702400b0301151000c0020b0501e200f110821818030850350a01d2045031104002600104802a503540c1c4038144 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 805955251 1250 805954001 805954013
    0xe0105310c0803090102010c020c0315340323150d060e010f0e2805030408120301090b0906060306040b0a05031923030d05070e090a0c020106050d110613080a 69
    0x12a401c1303405542010380d8001c84031b10024402c082c440d4000d00403d078160701c0c9141004002005881c2c203c81c1c062074080c8148500d0581e00e590358400c49800c6c2e5405140c000c030002811200d0380d00550031b0904c2c515100f29850500d10364415000040c2c40100b46c034040719071000651050712200002d2a160a103000d4010010042d4000c010398201d6aa040c002914000c82141d00d0301a81d001041e80120f030441c9039005034030360607592403116120b1000c682ca010b40f161001454545c0054111035000f100000520064010780200c44800c0410b60340c4100608007880020170a02000785043d010382c8d80d860f0100026911280440004c01d4040c040d00e40707803e000b40008901c100c45000c2542c0c42e204650149000c54050311400f03d0403d210005103080c00f5443c4e903044003420014061a0030030017030015000150f50703900416405800040000940480251006804c0d262182e0015100d44d180070010008039800d409800e028000c2251115650084090206d421f100144c020294900c0f41c00354041c10004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 805956501 1250 805955251 805955257
    0x10060c03140d0e06010906170d0f05120f041a0f010b0a050d09050604170301060207060305040c090e060105150a021209010c05100221090319030e1204090e0105310c0803 74
    0x4000702c024010148c656420305280704041c0d00340ca000c1d50120182100e10317403290702c0800702921036207000d070701d414000011507074150419610075044000207410302c4100111b00381501401c40500d1040e055034500503c0d010000c107414414031041e4900002e14a1449108000b1585000d085450420004109082440e41c0d034008990440302c02046d480420742400d09082500d04075000da50080ca129800e1480c102c019050140045a0210039200045101c20640c0655000042e03640c001303003031a42c035042c20400011311007031011020200c1082620011640452071640703841d00d00d010956203550350300048404024a0308040c000340900002d84560803601d170020b05090502c800783c101115140d040183e07a44609a561035041d5000300208400128034030f038107446582c2035003030000302c00d800d0420745401d01c61102007017000e0210014044c8284140d40c40b61b55120190800200824641400035520f400444002c2400584100f40e045212581c0100f500400c42d40c852031040881713a58110f0185c0d030303030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 805957751 1250 805956501 805956509
    0x180b0403020712060e0d0e060a030f06031e02011d01170c0c011e2403030c1a090f06091212040c051519030c1218170c0610060c03140d0e0601 62
    0x1b0080c191403031000e0f03105809500c0c1584008140610380401e400040d001451410360ba41e074100e0300c60700300001041c800742d29004d09180f0200c4050522544e0300c0010b00520700070044d414070703148282c1515040c5e6845070114501071211811442d8680305c2d050f407030780d0502680203c0551503081000348200b2055148801981c1e1220100501c00c041844064904c0440000c0444200c2070b500002003011034482e18038040d606000301030b08905c680c0d4980001010352401c80300044142d01c00508000da49104000309030f8401010b0001d0141843e4090910031940b1131100e030046a40c1c00900806c06001c3d2489111004103801021aa01c2c0a000305040003541c02c030800810509040c1034031501e81d24003c1c0580c0680041c0c0b665100d02c41841c6c142040300520510401c0076003540c00c25190000520500140110070302100c0009407a84003050b44c581c80e2980c01015a0401c441c50381007001b2007600102c0d1400410f5060034403030007058040320303402024050080c520040b58144201000c180c0c01c0802c0c170718162 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 805959001 1250 805957751 805957753
    0x61014031f080a050607050a0507120e2b1202071e0e150904061a1c0b07090e190e100905010c140904020706060509160909180b0403020712060e 63
    0x16035510410b880d02c0b030071103c4000e030540d0085000140388170711400c0105580f90b070354148141841c0c0a6100c40320070514003109440072030240d01d1010f0b1186045a0100c86800344000700410104050040d841050751084000704a01000300c03940444900a224001c040d003245041080c419172151081c46d000f113624440c103010310002c1804100300203120150404005c4001e01000c017a515130380d031003070003c1c1400707051425040e0b003094200d2299559030501a28500f058a54a540440d190a14000441c1c1c050426014410f0112007040241164901c290b80801490300a59100701d0040b406400760200d1150380e4281d009903030016002c018990300018580c0d0280008115480c65201c00faa5070424505c0351103641e000c00e1010038901d00c6d25800030030308288108804070b00b042e40e41c0c01141000c80c0a41d2410b0352840320b901c80c0407013140d015100d04024090803500780000c076101490495408d08908002d49040c00480005060500070045032000340f4681e860049070920900b81392000b08100f002c00581 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 805960251 1250 805959001 805959061
    0x50f01090b10080607080a020415020106080706020a0f150f0903081006020106050d0204020705070b1b150103020603010504090501110c0f0f030f12091c0e030606120606101403 77
    0xb032500d0072010b03081910b114100408161301d80d01c4041d9401a001400c510b540da8080001160b04518010104000411500086041c03030801c440581000c6542c1c00900465003c2c01d4100003050440c0520050366070004c04116103081d541c0343c05000740c44080c00030f17600b0500344840002059807004039244281c201620480d901c1d81c032100708a091750541c0c072410340c3c0f180399400c0880161420341e004104d10741c07190b41145d04955540d83d040840384c0042d02c0802c4504c4520303c4040160380d040c04080a140c02c02000b0f02055070440d400125a8001802820b0003181d0722440003007005825400840c01441c18408151600ca02414141d41e88202c1a81040070b40108030000020b40b5000045c1e80030b1000171070419043c103c9000c000943d100000303040c50301600c00d845d09400f0702d0054546c104141c4089540350001c0000350350505282081c050f09086c040d00c6c0503252040210f0703000c0b5901b80c0201c4111458072004000740130484002406c0020400000000401e205444000c00640700c0005078a01070320340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 805961501 1250 805960251 805960261
    0xc062403060e0f06150d02031b0111160611010216112e03200a050301090b0f130c0507020913021c031e26010e011a0904020a0c050f01090b 61
    0x1894855560700a071260380a8008117440394800e01c2008030107240034201340e804ea191600007a103400e03040d80c0e20440d03161a20010250b2564400c860329a8040380d2001003449402e14600768003a41958800c070800c2000c081e0036040c42d02001e404507010720000c50784800154070f03079041480b80c98842125080c03090454101c01c0504030b491040c0c40303056034032181c1c0d40c0e00300503180c050640181c5603c803a003800c00c7c1203940d4440d1003045900042c00074100303140d81d11b607202c0d810400183e00b1035406040351486507407806883c20155644481c18003a264600740c0208100401210543c1c0d030380600c1900075400301c200010850400603480358407203910b00844400002484485010302440c14059000e00003600c1c1c0030303000d900e10b00e01d20300c0300c1900c910614100e12a0300c43c04d04845002c0104581213601ca101540040008000b0700360075034098904407404d404201c0341e40d260f41e009403041108180c029034010441c60035040c0150b100e0000c0035041b0003640c240c0014000d0b035074002c041d50740084981104800201d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 805962751 1250 805961501 805961503
    0x7090305151017070519050d08070c1a030604111312120306031a100914160f21020d14090610050a06080411040e0c0108010e10060c062403060e 63
    0x3905000c080c004e81103603800d01003031188840e044032030900c0400c1e042c01e0000d4070f51105010000d900c0d000340000c2c0d48500052900c403c044050f036001c500a404009051040211403600b201c0d00000102c40008100044160001c1c09006408519a503082060340010703900286001c5040b641c1c2c4640d0707030f505240c0c100340000d504640c41030001030021941852000c40d20920044c003075070440ba03d003c8510040d9034401e04a410394451503d0300394a0a0000140079400702c00200950810000741050041864900320081074440482c00e01d11030345a003460b003060032203041c1e41140c0c100b1000b00e0082c444c00741d4140c2c1e00c2c2600d8400f42e13054002c0384940000203040340b40c0c000060041c2c403001894055098a8100100c6003003070080e00030340311007102189615003036445100c0c0001d010f41c00405400d500746900000f40c540c900581c0f02c442222044c3c4100250204146c10500c140c03002e50420f50072080341410010020706040c0d800004803100c0c158070000c0ca0409044800449128510502c01071850100003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 805964001 1250 805962751 805962779
    0xb09030c061b070f080d0c030507080a02250803011e0f06140d29090f06090405030d0903120f0924020c030f0d0509030a0c0b070903051510 61
    0x4032154001c440800c0b0b0280903842584540102e100110741006510380703c1503416031480e0350413224018005041c01c2650324601030a4548083c5040402980c070b405070000d8011076004064034101e9500143c5010090301c4000d904801c42100c103410750000383d8616002c80640d101380217442c1c001100c20b031070801c0311140150300000d48400c640d100411502d0314805403001d0458100a070f0b00703607000788081800b503000e61042498507007640c0703010b00031294070701101d040d0102c003550054007892603501086400c2e0400c44245404c141d0a8030900744994850420728203501600c40004240360501c0d80301c1c802e040e4001c40513030000d54504020480007230080b01c104121861054000d02078242d6420b41d494000c0389089090009061400240c5882602d850040c256804068800c0346580046544800c0025610032580d109101b00c00442c602910f0102c041c0407032049050041c590412980000c002d140300f4060b034001141d0281c1200c1c0070203a103071607032002c440341124900350090035607900061485480b036030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 805965251 1250 805964001 805964017
    0x1e0e15060a0807060c23010f0b01090515070f020616020306060904051506030106090204060305010f0501030905191a1311010f0f0806030c0307080a03030f060e010605090f04060b04030b0903 83
    0x9050700c03890400f0951701c4a603240801d40745101070340400040c3c0702c400d0740da402c80c0c0c2401c0800028003105103140c0c0011500f581644c1410460314440070300c026140d50400c83d8584141801d00da444801d2494000d4034012070100003504104081200031020442071007402c03416208800b034410320340c0c500c0c06000c0b07480340844002d0165440808081e00700343d80309400d43d030880710240c0081070343c80d1517a0a010580c1d000b64410030001c0d0b41d40004005940020030000702a00d4240380a01450416440741076a9204007c1c6030720841c801c80415900f0402074600980300b01c0310384181c4400514002c0c5401d65140b100080940b10f080c0c4541c0120380760340c403484400b20b40c00c0e85503c40c1c2c41d58030070700041150220740007450290180b28041c200d034901d560030800e4078000d0696038010b14401c10385140060507241003458640100e810b0404c20302407400703040d0f4118150303070940c070f0b006031109980310008401c00c1c1c8055030a50014640027002c60101c0828000b402a42e000d8603400103681c4030401100ea8a10503013072 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 805966501 1250 805965251 805965253
    0xd090f080123061503160201060803030408090603070e09151014031303020c0d081e0a080406110d060806160504080c0f121911090412031e0e15060a08 66
    0x24200b04440020016a803c2a000f60660342010141101d0444650065640c00d40c03418400c2618031581e40d09018110181145601650650403d0b69902e41a4050f490f03405102d50300200005141d54460001e1b0081001c00408440080c100724803d52400e480311003011b4080c98101702c060503510b00550001da203011701c2c00c1c2107070b145695450491703c001403000c90482c00c5004095402c2116071341c4154540400d0f004161265031900e5000c00208601450058495210024440740524940050700c26034001e80080005c43c2d1751660b030702c944035617100340c0d0000d0041a2900c100440d0741e81000a6a6110300800c45426221a9a484040c1e0b0b06004511601c0c0030317541307c4c070300301a41e904241444132102100074010482c050180c001203410080d03814500d1480490707041c4070505000030020240340240d02a54042d4681c1420b46a20709079402c10b5801c03405150300c502d00409140c4503100c90399221482d00c2c0c801c101183c5141c92403600c49140c03100c2c8000c0101010007003200c6d071818000300c1080b500400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 805967751 1250 805966501 805966541
    0xb1903060b0d02120106090510060f0e060417060411011103092421132001121503110406120b090313060809010f021801120b030d090f0801 61
    0x39841002500c841079000d40c100c41d06030101e00042c2c03a607126514a100210001180403424001c01404644c0020f00109104000d07c030b0400c1010381100e107412107100700d843d015a010301c5920210f111032103642d02c00141102104100948600041001400703240710b003030f000e00d03000c0104004440c0d01e60040710148242c0c0082100c03100a103010510300d0b290202c610070400e5410b000d0000e07078203642c20060010700c03445200484494949402c0d81980e500621271104207064583c83e898003056458400e850203000314401c040e40209038000d43c05d00140c2c880c0c00d407050256450a103030f2031800c6141d5120446082080044010440c80d15000f00300644000030030b0300301004116290400c100d0009440c40040307001c1007210071024501c1c20401005043c16443c1c04c505402c2c040d5410303084441c1d07031b885541b540340305000028a03040b01c00d00c0e00c07800e44001d180100710007580380703103103001030400700d00483d4544034180245404c290462001c400700c90401c485080800d41c0c458015082c0c40031541601390b600040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 805969001 1250 805967751 805967753
    0xe0604080c010e0315090f0106081513020a050a080c0f061e031b12090f0c01141b1606110706050406050d0e060c0d0c0c1101050a170109090201030b1903 67
    0x76a00302e0b00c480d800404517001d5404c032101c002c0044c40c00fa0740000c0550040211252940024015900100036502c01449401c00d400004040c401d0003400210b40360455070b03510010341d0780d1010104064030000b4030010119594040450f0340c1d45d00f5a1740b0380d00a0100c800c00c286140362100a1700c481e0090702030a48000420f041c0300d850751343d1008120210205c0e550640100324900701c005080c02e8508103a080a1900b041303023045141282c842c8908a10354007401224056903845089600c1d2540c040c0151078403908c0d0502e42c491a1034800e913140c805071140a844408101c45902980100e440300d48500c054050001c80047d00d13100c0c80d000e5a404a00108008c0049911a00c01003d0700e014000c0c00061b4501480d08160500105451001500c0310204000000c081d5502c11044c1c80000c03801c100d41e18031015035039000d15070540300205040c84004515000300c58024071201c504840d216083d0724240da11011200003c1180c500280d00007403a0213000815401c000040c040c0107848030178200c0005181d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 805970251 1250 805969001 805969007
    0x60c02031c09030f1b0b070c06050d14040b07140703080f062205010f050301020903070506030915070207030b0a0e0c10053007021f0e0114090303070e0604080c01 71
    0x40007180300104002c8290000c040361012801665081c49900d060044031302603400760b4030304940340c0c01060201c1c1c020130600d800903a055403501c1c11502907042c096103942241202c0c20081c8031039a070440400560310200030402100c0c240c09440b841040c0c40310891038024502c58242c07400f4205009000c0b035119030108800c0c110802000d0303400300008151070564150702c566000101c0088a5907540c19450b103005101d007003022501c01001d0102680210305140100d80040e0f501d0384184a081e00035440000484c01340c140901803240c440c80203403a40c2905041c2504000e545601d079100c1540c0c0b06c02c044020904290190080c01034511aa0300206a400c1519041124160b841d044090901c60b0400c00c0c1c660f041c00001c6100c10a800000c202c0b803400e02c4151204012140c001c00407002c641056500c01c0401c289500c0182200303041840024200d48006613141c014202007010307001428800d820441c003500000300852046c500c40e52503088002411007801554050b0b4003c5803c9504085424445544 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 805971501 1250 805970251 805970293
    0x3030c05120a05030f0105030c010c0627080d0b031501050f120142033507050c0a030809040221040f051507090b180301051f060c0203 59
    0x100820079a860018000c08410031640007002e0280450400b2003000344440d903001126004000540241c400b41081c94002003103208a400d0092085540d203401c1d80448900311f8401031100a684440b428060700e0382000c0b8460742083d02040f0713816040240c88402402c1c0415040c1c03402e554165507110076400c100820800a211140140c0c003c12034000c80c01040b1401d00803021441d0014803040c1402000d01131005021803900b0054510250a100d103059615808110400b220b40203111604505100341452441c15440320b4004d4444841c1203901c0d0310860102c00a082d0240700c2e8080747c3c0e1520005042c00100c8000d4803010f040880103012228503410640c0040082c2030811200d040a015044400624403205550958441034031901541c2000381c1044aa0300e5140b04035101c050610348100010036820390741c091900e00080116425650b98140c1240c4000418018020b11052402c9114113001460a840c07403150f11050030400134455010301c0e034a40141350050054440c00d020030300304035a415 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 805972751 1250 805971501 805971503
    0x30b1c08070204151401091518030b0a020405120c030a080306010302130314060903031012080408030a030e0705060901080604020a0e151909080d031a28060503090703030c 75
    0xc60420001c001642e0702c0c45201002070b01c0d5290303107a0a50a03d80c10102c0d422070113030343e2814020040001d002c02050016908080a01c1d450804540d40c1014070340b41150907a03a000616041c0780301c040c0300680f1502d8014009581003910b1b0035014506944159a0303400000000135015080045a5030114000034015a404a0181405481c001c0307070852024420903903a00030741d84103618803981103141000b4441c140d0440c180382d00850079410042c2900341003007450f2203003c0d02d41070f1803954101000316400941d00209040410b0300d0300c4021050740503002d021003401904441c06a500c012071a07180c44803c0ea100e042040e0341c6c10794a59514010300000703500440088040c841810340107130140e0346e0f240501e40c083c05503012031520784020f0310001c2c16100504a0300b00c1484034001c0240f00210000585000951851030049181e2000901d0142803500501c1126001120315404042c03489040d601040c9004460411540c0c8030740e14081120540016580c02403290172110080000c03903c141c241c11041c0e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 805974001 1250 805972751 805972763
    0x140109150807031d0a150b10180e07050a0906022109040f0e030a020715080a0c18471b06070804060b090402090a0218061201030c06030b1c 61
    0x11410141156000c40450ba131000b5243c0c0940c450108003e0035052030007003a00e0410060020503c010001280c00c0644607842040102855581403103181040d9001e0050200054005e1942044c880081c03585c2e1104110300c001c40c01540e4002280703480080c000d01c44c80c02500840d01c0c91240001050403a81c086030701154856180d00d43d4020080c428800c503010710f0001d0005546d50702078684040e080050310f5118600300c3e104020045800b64100ba800d5500a6980030002000d181022054601d10100c00441c4010a604440032900c3d6600005501002011003c45001c4c8482c003481c030039031200c00740d00300e122203008829045a00040348000e000035800130040c042604404441d1245842d070100c83c0c5000050501301030106000c2148241250f0361030a450031002441c00e80c0105026440240c01c010310554000b81d4801110415020a42c484000071b118036506d02c86281c074081014000c0c0015070b00c0c1c8101030400074945000e4031816100140c0900b1400700e81c00401c60b900381500014000350380c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 805975251 1250 805974001 805974011
    0x190305040801060807170a05060a0e011503080912031c20070605011d0403020a140c09181e0c040b18040501050f01060212090f03070e090714010915080703 68
    0x1041c4020700031080540a010010308040b40380c2a60390002c1d890480790420746411a90280d004a100402c4156214404500101d4607548000c886401805c0e000c800c070503500c114050100404c1402e400070103001c40708a03154040721000001594aa00c50200fa5500d64140c910a80c03095815540000b080c0d81e2451140c40703648071161400101c02d038041e04013150394950fa04d0040c0540c008400103160011300300d0584c2440c0740b6299034041d40d5503250540107004014405510034000e00100071110642c031000e040c6600303070b042120380602408481c9050203041c0c09404c40f1000d41c5011b41e0000032002240c40d00902c100850310042c800102507000710365800030004141003412142e40c680041c0918071030000098035140c0000192880030040c2c0001d0304541050007180b00c0e2000207020f65084601c11600403261481c5030000070310f0010742d0f501c9150070030104001c0244044010403210102c4440c42c00242b9445400401100c9018460080c5264164070140c080b41c0c0901c00c150741030303020100b4100096 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 805976501 1250 805975251 805975259
    0x210204081504021e03030a2304120506060f0307060f020309060a0f02010b010207050d1b080a081308061015030617010902010905090c040303080919030f020609070819030504 76
    0x1042528901c20560050800e01c1804114144441d0308010200386400502c04259400000b0382c5034442c0840107400c11202d60103102c03c090121030140100541084044e5541d40d41c0c400c44500d4007043c0402380c4241c0110b00c001403443c185031980c0610a14001c01801d8a0360030802c0a642100700c0601c0c11045200a0094098540f01c0c00000d0010803007544404408101e00600203080d0386c841014a411500100d40c10446c41d25256141c0e06000d600034048419803074a140599503098a03030b400480715105610b480303024040c003080189400400d512402a040ea110790480d907880798151031500303004400c01810808902e0414152510394001c0c5400f041c3c2d0f44d03441185c0040c0d600d0a0203106156550380808604640e085031900c402041c0a54092841d4036107141d1030292030150384070207070501621000050106c18140720b00542d051400300395013424050b81c10020654001088010003500c11803001c680307031040001e0b8800846803404010040c0f0f0913190051003c00b05195011418000140070200e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 805977751 1250 805976501 805976503
    0xb0439050a0f090f0b030f091b040915020d0b091e15030a0b090106061b0c0509040c0f0b130501021f11041a1305010906230f0a110f070621020408 64
    0x40003084400d14454072803c0a85031015036582c080c194448c90350049940c203402c07030f501c0d0302030002d12202210001401015401c0240c44151500e5032809841c0c8000b440754180e42c0c09031700c04001c10341e05650b885039940c1c54a04000d4450741d84880d908014481d500000e0000c03016503240703154200080c09858003090180c0e00c1d407056402c15140e050003030351166000c1c040756134030a815448010807041340d07000007203203a11032040400d0b29000e000d00810075038000500348a060701c0c0350401040001d581401d916581d4101c072501c0c2e003000410f6440c3c2c1c800707480d00080030740c0b001440040880442c8980071030aa00405004014004040c0d4901d40c0d43c400e200c000b60303286540343c46003000561500360582c1c03610b240f03035041e103401d00d5600605e0501160200c1801030b50303407002056036a40d1659500b00e200d500404a13910450084080b141c1811a00051005000742c3c0000d0300d0061074080411a660f80c180c2a0645455040d10b02030000000d114800800071704868842c4e61040d06000c040041c135083d02d0f54944d03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 805979001 1250 805977751 805977779
    0x7230918010c0806010315121209080f0106060806062b0e01020708090f090417090d06020d09150e03390703031101021206040b03010b0439050a0f09 65
    0x4400880c518004204e2107503010b01078103200e1a280d0100e9a01903050030070740b00d0400d0b515980503200b4007266a043c40d02e18000c68441e0060002d034021140500902564a4080c2045019480000e20300fa004908076091020030b94006081d40b0b4038015680700311041c0130190f001e015940c1c01c409a100c00141c0005502880200344890181c801c1c0c43d079808404061240380486e8240080c001c0c0034030004c000228103008010314070510584005507507010984009800104080d20203058144001070710484150103601400b00148201e0417282171704001e00321801101c0032443c904965800400c4071240d2081c0d010000318064000c00340c059000943c41e01c920110610310303441e94850b0307408a1014418590840d54034200d4810031002980f406100a4034640d10402c05450640101d440d80c0760207800350313002e401540d01903031301420400184a00d0600b0702ca00c10b848000d82c0b00305c0c0e010b03464240c0c130030195002d5101d001102503c41741e14108040e07100f00d078155440c085500030051030607404a41c0d0440c2c02e4403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 805980251 1250 805979001 805979021
    0x60609130b19030218090d05220b0d0c020601080c040c020a081207090b03060a03060b120f06010f050a15080615031e0a05070c080c03071505090723091801 68
    0xb900d24030758214410300c026401080c4100300101180001c000340c0000026003448140710340d26186490308503030000c22108a81c12003042200c00300c05100424011544e0f4044c00d048254100244820310800b5810ba0301c4200c04c0c0510342c0c4980129002c165141004e42006c00c0f034691610458082200b00d8603441080c6d0003103c110005242c0d500300b8840501c2c3d0241d8a02d020300550000c552a6042c17020001d80c00d00d800d0f00c002010307143c40b40f446403500e42c0c60040c981e0b95040111309580840d2a03c00010f40c0b80c6000b401000d01d201c520601c04a124201300c0c84080641d1000f001c142d0240c04188016108880300500981d84180f2071103840a10480040107980691b40c44004110720300a00444278610540090821000c2c0b0301c0e00d010803d90682c00140d140c0810303007150290b5524001d20314900d046108089002c1d10190b44807c0e0104200c06070b52110384140142c4050300c42580d141c01d1901b4001c038500b151035680b0400759024480f24900788035501d8001c0f00b0800c40c0c0e42c180c144004803070700f0b4034003000c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 805981501 1250 805980251 805980289
    0xf071b1b0b030408041518050907050f130e15130e07030c09270b07030e011104080c09181203070e0d080304060608013b0a080301170105060609130b 65
    0x541040041e403020070f2141b03003070414100000d61101121100c100071030148a0b15108480e0741020401450003681100d03001d002d51548956030391208204181c10000520070109154070613800900d10002c2003a40c00044000142028141000e802c8004041e011a080e92600fa00034103030000300041020100d5001480d490002180810b201e1032400024003181a11544200c00f40c0e01070400642c212180950120080c00c0c000340500d01c1c44501801016100d54241400f1000100440d0108001032800c1050304116080b881c180e40d10a01035021070306120364080301e54408a02805400d000c00e000c2c5030300c0480c3d4a03003006a004848005402c80c2d042c54400d6421200000c20700061007810700403d006812500000c1c0240402c00c00d01582c041c490990f004401501e0310710f0303100c10101001c21444082100700c00c460701c1d180b0f24208049194005c4c4160040c1080f040c0c01d441c82440c0c18009c244c89090000c0c030041c18004120240045a12221007560001c1d54031180940c04d650b6103402038000040c006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 805982751 1250 805981501 805981507
    0x6020a03030b040b010e060a0e041d0105060d02060415180f411503010f05011e0e0108040201021f051603021305040b03070f030303050f071b1b0b030408 67
    0x20030003400312252640d44600072801c1144202c00c90f6044402481402400d8032038a944664400003202d100c0020401c0c0e075131040c2007a201500105132400ca58a9091401c0f00800c01f5440d60b01c01c00244608103180203402450038441044240e082c50501c4a000c442800c00050070b1500c41000c0e8181d629a81084a26580399101071240280c2c0001500c5845848065406821100008101da0600c9900c0d64000d03800014042502da80f9004492461400da605680e5101e58403542010f109600b1401000c2c00142d803800d4415044001c51180e6a0310700854a500ca185800c0100440e40000024001c0c3e044d40b0034403a520300b550b903201520140010303048600042c07a060001e085142c171201c80c07012130105401808041c1143c0450801c25080311011200040c1e04001c0c4804a0305240340c0d51322a00a000c00b0850001c14140c01d074105038400c001c14007030b0710a1907440140a40e10510701ea02401d44400d1840c0b0801c0c0010300c0e5880c91040d8503450300900005c1d5a035244080700d158001c031001c540101000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 805984001 1250 805982751 805982753
    0x6060c0307060f11070308011802040b0f04060212040b0304030509010e030a1208010b0703080105061b0303010803030103170a120902121f060b0c0a0303020904110327030f072a06020a 80
    0x744610680242d404c010f00740b8001c40b54030002c01044060299884078241c04400700c0003c2403c2d030441d0f001b002d5149500d0707202e1005800101c42030301700740b103804003601407140000c1d4171021840883d0141e406c4104000d0440d205c03610120303015000821080d062089014264040740d4041000119462140e030540e0800e00b558880203019900603400104038040902000d0002900070800c207040d10320070b0302c01603180d031861104000c00c00d9120310703030400901002001150310180400198141c82c012102042920314140040c541380c42840d01c0280001c4403280076041c86200784c0c00400c44c0500041c01ea0b1102161030f8011401c05880707402d08124141c00d0101e0005003c0d080c01410010320f452025a410b01a0216545803a420400002800c260740096110f1241e0390b1580b01d00c808240003a00c41c0c3d100c0c500b022032400001c3e603d208100040d491391b0411042ca00c0000121110440640c3c029400c01c56240c0d0b94988400c0c0c0700351000d0740030a1841002c003040205014000052407981d004120203441 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 805985251 1250 805984001 805984031
    0xe190801020a0e01020c0315150a0f060305130b040803071e03060e15010e0118090606030501140a06021218030d0302030610020c010215330f061e0306060c030706 71
    0xf0300c10036040d50013481800030150740100c0c1e110541d112002000d01c6955841102081d00c6c0c4541d00003c1c0e019141c004003180500c02c980c040400d4560030303201040240c8950740c105483c010f146000400148581e07001800190041c1c01554010040b400c02151b0b1032a0803027803111100101c1400d000095035070300c3c104840104a00b030305802040c460308408070785d00c02500090904202e000041d041c0050f10081100b120300c81c0303000e00001c1a8941081054644504004000c4c14082c4074080d60103014070340b0111a40360103410300b41110720030b030003c0026040c0705a0b1264250490603280500080c0203010342450b881c2400340c99103000071560b0040c3c6c1e0349441c808019508280c80c0f002804c5601c0b000c4800342ea81d800090b512002c90006e2040e204c00da961040318001000d901c005c901c118240f032403a50401c0d500c41d46c8104c04032802280c00c084114035110500c4190702076403240f029440c0040ea6071000044900004640010b0054442d80c030380081a40741a155070701480c03044030b00503030703d0500c0300f55905 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 805986501 1250 805985251 805985267
    0x10219020d031a100305071b1109070206070914060c03040f0e13080d0209060415020d03061409060f15030f0906010905160305181f0c03110a0e190801020a 68
    0x1500f2070750058441d210030110380e980741001d000009040d52a00455181b038000e540c22000310a00f4610815808000e00d002c0e1000e41e6801c40c190b0041614602254899002242c05845100d09503a54514513280844c850401c080744c58a1030703044241001100d0341040213100a001a00003c8100f0044520300102d00110103c001c0c51107109500002c004800984050201da040c8001c03040096140d00c607240c000341c028031440e842034041101080741c11005035000f0840c801102004d480420000c2d03030f00e80e0181d0088402d100f080b6409150800040c60b140b07041c8918048490300986122111200c602c6000ca1a0340f050b14200c105030a6001041202901001071601414460001b03000509100360406403220030782c9184001d00d80c032140007401742a000185048030303008003401c56001d040c1d402c039040780d20300c84800300d280c4250a00006100c100d01900071607001c84000c4280500c0c05200e00c0007260101d103c528266808801c4910005520f00d10560010103001103400069403105c1107840905514 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 805987751 1250 805986501 805986521
    0x3060f04033b0a050901030b070e10031a01030e210c07060503160306120206070f020406090c1209030e060c0f10020c06060109051c02180a0c0908030c070306020903010219020d03 78
    0x40c0f0300442400940c0310400c0c030504490307020b81412580e4543c0f40d4140c41303110b99000e149403c0701c03100483c00d05140c1d00d81c1000c038074946954030200507409040011000d60b00e4141c102c001c1c91744001c4800b1560301c481c81d01049040a000703030b1709003046158070300380c3c0c20301e0104d0b4080f0000400201c248040b48503130a02d00110082c1070300f0200582e41c0b03402d0010524840d03d03080680b01c1c00011805400744405100d5480d090b40e4002d00400960740c8640952004020403408100003514038411003d11107010302c01e6010482d050380b21030003101000c1c01006850717804607814440c00d00400e001d64191440421004c411540c001002607124140c1c11103c030300e496402403980e8100082c00710300700113545480341004800d07108284d036002c182e951800840d030007124055488081002d44010070034255040e0780050510400ca0740ea50400580d500903050f92409040010700598210b03a50820000d46c0d20b9000303040020b8060005030600d014244d00002c00343c07043c103000000d40c204900c0900784983c18425000c01c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 805989001 1250 805987751 805987759
    0x203060c190806060706060b1c0b030c040b1f0207090c0f08011a0f1803150103080a1b053004060504030816080309010c0314040203060f04033b 63
    0xd003004006141e55070400d0682414400e480300840e103180c4031003084070007841e002441408002e9442c000f207000c590148450600020702c3c49403038841d0164030302541824074070080c0101082003400080100038035200707020030707400851041e0002848402c1e1184502d14035080e000784c2680d500c4e2203e480d0654603084610030400801d03441074800d0940102d20981598403004103110a1440380891540340d11075060624031002d40440c1c0010700f1030400c40d14425a4401358140e8842035080c03580740032004020700000b4841002400803c9005114034402140004195000742181c481c644589051204103050400c3c8800c81c04412101c259401c1c0d454004003603034400d40b928207032a02030b0013483e6003e54040140484c0d00028003642540300a08041000c0d6041200d603992401c120a55600900c0c0168000000c02e050480c5c0d8241022510304052049030041c0107052a903032103100c46014103000500403004e12440c2c10104501840f070540f48a001004001c0052081010240c5a0346c2c0d0950f4298880c41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 805990251 1250 805989001 805989007
    0x302060f0412111609090203100b031510052205011a0d0e010e030406050c07050406030314130b1809090d1707030b030a0303062909120c060a0305040203060c 69
    0x4050324002c80d01000030745803122440301410343c0c2c03e080500300d50000c00c007101c0000000c150800264480d042d514400c90490388100211400e007400d490000c8002c0c1c0e8541c1000d500100ca1491200c141a40140b070032442071b0320507858000148450303000d000741684100c2e00d800e1024404101d8401c00d409404c03010908842c1030f102c504050000d00c91042511046a10754450122080c001d4200c8805058030900340c94130f40d0740350140103010741c01c010940036040c410540d00040a041030320444040d00d405683c0d051075400d030a0081007180e030102c082603085000c2c0e21000107101114070040c0030100d4040182d118000b075114104080014040c2607041190040400380314095081211041d01481a5402c0300c12950341d24001d5004020304e0705030a8160080380c1c8104105541580900d00b42c40b01b110708900d0b103801d2145841403040080c01c2d2130400c20010400700070b81380b404154a0300010008401c80d503100524002184141d0050004040032944a209010441c0340a000c031907842380400d450142 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 805991501 1250 805990251 805990253
    0x12120f040206031807030f110117010f090c180b0c010c03140a0903020a0f0b010611010203070f050319090803060906063c03070906030b01050703091e120f0302060f04 73
    0x26034400504040200550a5a400844c41c0d040c010400195003007000420140c41c941002c6910b03840d400102400a03d401070142c0c107550b1500f4225040e110040c40889c0d80701e040c803405400401c0c1c404507402c18444000c4041c181854114541400ba00282d01d07001e40712401c0403c9a420344d540011284117050814410340007083c2c50031130617a407040440c240032544030b00f6400d080c0d062a90901e4090b0198056505810910480c84a038604903401c0d5a02c040c1044405145c00e0308078002642c4510000d081d020b1207030000c3c0e01c1000515003002c041305042582030b000821480072150700b4407080352810b0012040000b5071405998850340a8070640c1d0300c0b4a4448200380c140f035009410044104420f241e81c614512400c00c24a42ea4200c02580c07a00665038245a00d015103507807204e1040d4800282840e050900552042064400d52903142e02d4501202d41480d141c0002d0b00344042c64021195460b02000a1600325080c00c400c6044c003c0003024041205428024148030006250154132068102400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 805992751 1250 805991501 805991509
    0x10c061d0c040c0c0b040804030804080604020f1c030c080408070305011b03180813030605090c03010510050120031905180a1203050903120d2406080c180312120f0402 73
    0x4489217a22000e4507a103641e0b21b140c10340103402903400c0900541c00100f80414400c00004080707010380c2c0201c618442c114035032070030481402c1c0380002c042510045c5008200000b8001d107030700710501e4401c4250508043d2900012441d01009500613aa5a074654911408040c12405d03071005200036460180080440034000790103081e600c00c40106071050000307502d00040080c21444c1c01440c0d00c02818003603420815845642d8640c003001c510320a52a01000c100e42112003e0014200e50044c2c507500031404c842119a0030352007014254001c14001040100b4440c02c409610001100d56034607215100c0407604030000212650a0007507008603102e503414810f82040105c00c80e051685460580e540b45800b030013180c10500300e5440308890030000305412030309560b1500132520b0000740240b02005070076090004401281d00b881560040303861100841e80e1441c0d40c1c1c0c000c0010b240354541c085000015840424034026217074089011704080881d11160f0f604084e00c0454102580b140c140c3c0c043c2c1000e40000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 805994001 1250 805992751 805992767
    0x90e0d0806120c03060a1e09230a0b01120c060e0a091109090a06170a02090621060f160c02100818061302010206070215060906010c061d0c040c 63
    0x28601c00d1819032480901c10740b040103d010342c0d16015094803041e050045914001d0300c0300803010a0106d01c0e41300b140c0c40c0791020b0302c10a07110a402461914007080320070705401020320705480c2c001041c06050840f00100d10000b0155009004180442c0d000f49004c0c24800c03008100e07a003240301000b2050545442d06c3c0e542050070400c1d103842c001c000414000c4900350304280d00c250078103190403004420411175180740c680c0c0810221425600c4c4105450034103040e903030310307075401e110f0080d03000719084042081424040b800c001041c0328900c04e51003840e19a44180e181450460350704071070400d1302d000c100704031010000d41342c840005400e003102e8102c4585d0004201c0100020868108404400000c0010f8005403210050115000030341e207480c1005000b00300243e403420400c0e800361048001080e01c031880012000e4401c0d290020403510303501d4020801c0011070b0081d00381c50400c8403c6030004081050b41c422150800d03d0414070880f2405401c21160034552504e0441c0d10840c40d005580710b80580040b14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 805995251 1250 805994001 805994011
    0x106090b03010b181f0906030606170403031e27050a060b0f0411030a0b06030105090a091a0f0601020f0607171003050f03030703110306100c060e16090e0d08 69
    0x40d1940b281503605942c1180b100d140540c0705c80210428141d0411a0315041420081640c032900c50a4032102d080c1c050703608074031070b08000840b034114029400340a1201a50807520914000c20300b681c01e080004410258507100301d6000c0d55442503074104604a0040300e26011a200f042ca003820702c1c03500c84a451b1854440040c050644800b00f64600d6528118074100e5004001c00811056a4160204186410841321030f000e4514141c2102694603120056034100e480050682c281541c94903c94005021911800c032134000d1591125400140c40c9241c95100c0c00718081421481e151040c0020714003c40e016445000360005010b001405030310003808d45002d181503160032581e468850b0280485507195001403c10301900c1110201c200010004501582d815941402210f11880c030002c02c0d440255034039030388a902003501c8000c2502a030044495030740a610005100012400300f00e041518088007019810300c0c0d000117102c82000c41c410180a885220300901600055440152060a0140c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 805996501 1250 805995251 805995269
    0xb0402012d0309050f0303060a03080c0a080706230411010c030509030604140f0c06070312090f0501050105120102040f0e180d030b011713021306080714090106090b0301 74
    0x50110010003540d0240440c00300d412101078041c0045407004008000c6030404a072540a000c60314115851300000b5680100310042c00c441d145840c41d03499252591040c251400d040c000d076920107004c684420040c001060040802044a2400d0100180c0094620600c0741000310107005000100359014400c003891030080c2400074003200c1d24102907485008a0040c95418032800040204220012031804104400d03075080350308041018030000d4460400402081d0020030030b0080001007485a0010f00480f10324050002d0505d503d601c685050400802e803e84650791540010001e60510300c075800d07600b5241c8070085013014140703804484285464420156030078541c1c00456028110090820558400c0c58111984151029009406060461003032408a5040c003100c0304080076040b50700e0300c903401d41c188101d0000c10030ba0810122201b0308000d5540f4940d10000401c5090007001440082c00c00b03461000d0b440c485082c200220302005801c0402000f1603203004002950100c425681540c600309 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 805997751 1250 805996501 805996517
    0x70e04020a0201060b0d14180a0312020403050a14060106110718020f16030f030c20010204120309261c1713050d020c0303090607060f02031e01120b040201 68
    0x41c01c102e02421080e04a5440c5080c000b0300d44140c214075030300200180b8080345481d081c59032203c0d1600500344076000715141c00c2e002054130f00000ba00c60048031080740e50a5a006040a4890315002d20b000451242203410500d1805448007070541003011500502d26450700100c2e544104012a403591240c1c0320b040300681c804220b40c01c0386949501070790700798070300c1c1015540c40d40b03040306040c8200d0310808000e602203a102103000d07035070b20300ca030040c15401912a00c41051401015100c0c0140b1850500f42075019542404041400e101214401240c2c80c000d40d00e980b40c81d420180e50340b81d40c4070144000c3c00807044203840d10071220004590070b420860345801c5611103036080c07041941c0359100c00c4501280c061000c010803501707020b00e001400c0400d0040c000c940c05c048981d40d041c0d03500c50021070865403591082c0a05030051034000024001140304a402060110300030f52410f05076042070341d01550682d8421240d03c0c850b540c2c00551360061002c98042508419103440d45420310750040e00c06410824a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 805999001 1250 805997751 805997767
    0x120b0a030b0903090d081c05130f0f0c090209011206151d0d0f030f0221070206040e09071e050604061d03151909021c151a100206070e0402 61
    0x500c00d030b9607200c01c040d180e403649003040e10305041b40d07030311101d2914466243c114004105131b1017440b885208000c2c0300419000c00300c0740e0716081c460295001c8102d0711102c404106070000b84e19902c8041c0181401a009611503440304009092103071210071660707100b8a0140d0070002d007825481c02d02c01004003801c019107100c2032441a400c00894442d40207420040f45085401008080880000818066500c009000131039040c12a16540c900c81d0903118210388040c84103006448800416400e84001c11a9140650703e40d140403c0140c1100d07148059008004100144c07001c6010440d0080c00040720042c5480c1800001070f1140a0f9006060400c40300440c890b0200c0d04081c8141001c06d002001c658015500c0c0c0344028404004844005070720503180c80c1244e65018034018803000c1a4010003605400f021010031904043c030046003540c901ca200c0d200e28003d0320561003060000380800140025403103061080c041c10902c200c02c0710046503c40d100308903400341d1120401c03007110000c44000d6034500c1c070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 806000251 1250 805999001 805999003
    0x280f050d050a03181508042f09090a0606080607020c03030310061202040b0706090212070e010506031e04050705011d03030a0e060d020f0c010605180a0c2d120b0a030b09 74
    0x10503005449004400600200d100760132041b860710992150b020381090351403484c3d40c821200c00c5440040d10b5026502e9040b50340e40751916115500c044c5170070880740304803429261b0a050ba2007030361040c01c254001806004020b81c0c180301d281003801080d0700452960402e58150780031510141300303500070888550b10081002066404450003014070256150721003c2a0030610300900940100724420701e43e000c012103c4400c0454144112150070f003501d00c0c5a0300e86406d004840d0310081640340c070200c0e81d007403d0b00c5520140020b00d001c2e601400003000c2c100e09000000d444600c0d01441005210f07001c8140401310b030360000880e10b450310140f402e0300e9280c0b240340104810f4042c070150f51112900104010038205050f60244c100303407410100901086581e0300522004100c0c4d0070700c001005603004005002c0352071681010b66030b003080c1c1c900308c1c900007107078103e0b00400b84524035040e080101055020303200540c003081c501446014540f0800200e290840018003101d0107200c01004e0100707040010b0000300c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 806001501 1250 806000251 806000297
    0x50907020307080307300f0c02010e07030f0f05010c02061b04050a050126090f0c040204030506010506030c13090b01020c03010e061b04050a150909091e02280f050d050a03 75
    0xca11076010005003c0251186d018110100d02007601e9842c200301340c09200d00c140980f8140c440010701801ea00c81c155114078203d020306480c20b6541c00c4038100f00740c0014400740b2801401d40d01c15800b4081c1800c0c00f00503075885081444507821300b0a410301c002e20081d50740c032008000721003003405e0010442803404064052025004140c0000c01079120800007680d4001c520480b20140090954244005c030204010482c0503501010740340340d01440c014026403d151005580001e440340c15a0304000002e0300700e5983c98400c0d08100c45050319a540d02480e0358040006090002c8114000e0204d0100240c4803555842c00426890548406001101203102440102d80103000043d004a03141c5445d0005050001c0184010100241c0c0c180350016480217240b04080025a211001c00c105501014031036040ca61a08010ba9104051016001c1d1004081107010000600801801180c5e86421354a070042ca00f140c1c880760046010a606100240780880da20b1241581420501c89003880d044d42c1501240c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 806002751 1250 806001501 806001557
    0xf0a1101050103140705030105221505310f030f050403060e060f07090b07020105070201030e0a0b040b01080d120c0c120503090106060c020609091b13050907020307080307 75
    0x9480c01e03001000b0701c140d03c4040c400540c9407800700c4450564900915080300c0f0300b11282c0040b0014004000740e12004103240c0401ca900411082c1003258058001e141101e0084e60700103085005268441030040700718140303c18249081e600c0301038940d1162901c100c40c012003800102000b45c0f001818040b58080c0090f01d000d960020400c0096458043c51940d6444060720b20742c0307503440820300080000e0b10880380f60082d2022109403500380700c56070740159410703046080201d05050701c0d1104103c2da00300400611025901511402c1d8640c10a418900e101742c0c0180c0003885250404092107080320380203c90300403218500840040d10301c224090848841d1228003008050300b02004080c4282903001c400346010303800f0b000c001c1140c00e55901064a00d0544036100a40004080c404d0b28560700d0550a0203510008401c4c0c0400c1118000701156071950000d022124581e4403400140301c1d5003050303500700d5480140c0d400190f1500140c1d40f40c401450000509003001c0106824014034240c0c50300220704521 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 806004001 1250 806002751 806002753
    0x30f030914030f3f070215091b01110c06090d0602030c1206100c03051c0e030703080604050f0f0c28030513020108010b0c0106150906120209060f0a11 66
    0x143c140307911201050740700b290040d041c2c1e1200f00f00040d01c00c0c010018542d80b450350786442c0801c11421602031484040060410301903028071005040203030341240d20b540c4540d606074054550900003d04081c0c08882a003105810012140031941c013190b4001400c0c1c41080040b0707541a140c409210026040c0f07624920000d142d41c0c0080b040c04100d40000000e08255008089051025601c202c2440510b109004e155400110901402c4011034011001031074040c4105072104801f40410280e84140c5000600900e000d600000341a030926a211403050b410640407a000e020b5800e114080341c403103840251242020069560105250200c40300403564036640c040040b905c101c05800740320b00b0585080d200c110209040c5000510f84072007044001d06001d5058682c40800d9081480040613900401000003080d03699050104000381c41030209442c0b041c10b0b540d551551810040300170b200828900c4946c0003d4014000e04d55a44d441c801911110b01c2e40c0401030f84c840c0250907040761000f198442050b12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 806005251 1250 806004001 806004007
    0x150702060a0804231009081608090a23060f0415030207141515030c060c0f0f06010f030b06010912060b0901050f061207090503070e070318030f03091403 67
    0x1e080c0d00040803521803070040c0f2000364010240e010401254410300c10f85400e540241420500000302e40e07004096241c055507080e410555000985404850400c0707041e180d66401041f001c0b607501e4a1450100038015041240120640442c480003107074441c03802c1c40e0f01c05c21011441064005914080d1070040c1020100480031512914019000750300504040d00c2042c42060605900240006c0b081913450030303101e107101143c0e28500f01d5984e100d800002d00344d045c011100d80700720b5551807602030440084200043c155990740806000e10b04000340415031307120780040004000c2c1840c082c08040489400070010307501030740e4840040783d0038045500b11161403200385003130b10140300e1a5405481c00d182d00b075030390b0034441e40c807001000540c1c06000705466100c0400c101650007400d00d40c0015030030900d0b500b004805251241c001a003002c0303844e000f02400740c0200301041282c2d030b4103029001c0100010000400000641d4070014000b2174120313000d00c28581c039022000100a10b034124030800400741001e90b40c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 806006501 1250 806005251 806005267
    0x303021b041103070f0207121a0c0c3a0807030e0309090103050a0512040f052e08100b040b030f07020708031602090a020c03120417070f1401150515070206 68
    0x105c80d40010720080018403c004011605094648419100301d0f004200046e01904d10031654083d01d00c0200f22030104042809409a903680c200213140c10a86030a0300c0b14440c00d511816198080d2243e103489000c5004844503040c01600400e03681e0b0000828540400c019079151661455441018920f0340c00a4280000105002e00411101c01880c8a6400e94082c5480310900341c11038021402411004030302c4241c00c100a1604003076401c20100c0110b904500d14980300c564204d400d84451414020602c070500b04240364040190190140445400740f605141c140028500035000c01001058100d00d0b00c008909541d00811504000700401c00803250f0382c4c1c51038084e0050100310b0100c2240244100d40200c1c80c002d01600036141c04e180024007d6090000c8041c01d001680b201400940d0340c0c6412050f4010f0780810300d401007d2a60040c3d48407120031190341380103c0100b018440090083c0d2510381140141c04c01150060100c910440b40c18140f241c4400c0e501d155449501d200a42c40240041c00b12 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 806007751 1250 806006501 806006507
    0x140616080d0e0d0906020d1e03021305040507080105130c020a0f05010e0723010c1a07051c0b0f09060d11030309280503070f031205210105090903040303021b04110307 73
    0x80241d83e007580c25184c800c1f10000e8240c41d83c3c05c0050ba5402d10844400203605802d100785e0180800d01c000c1d00b078007986259a04081011503405890340300004440500500039401d215280f0684840d01920400c2071200d030000003900d075191074070700404503050341202609011094000150301000041920412941c500500607502c180140c0000c01c10045101c4450310340c080c071a040720213508208c05460040340542c20004000000300690180101406a00d00d0800d0600d50003505201507a4001004a1010200f10701c1103c10400389219221010401116440c0c050b1401e0381e0790350020400c2001405000040e040d03010f0450410f070010035204c894020361001140703140714901d0710b241103004951640e05040c0c94451b24012182e150551050410000d900240583c8000c0c04624290381403a1040c6422691000c9200035440c2ca2180b5000520061515094554021464a00a5140c60300d5a50041c0d1035403142e444407004101980d150740300a4956800181420001d0510150f8a00d8809005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 806009001 1250 806007751 806007767
    0x170c0d020607030f0b0f04050403140f120a05040809040b060d0e07050a0b0703050a1101020915070b181b03030c0a030903032303060909070506040f140616080d0e0d 72
    0x8800000c4c2440c1040d81c0d06010b0344204804075a000d0140540c0384080003c0c07101602c80940100c0410a500c400410b00704001c101030a45180c10490543e600c012510600e0b0784094003504038500d8520303242c14040056203020489050210503500494082e80300c50000384d0301d0060350320301a1104c1c01e01820401c0c40d04085000810707a03d08851005c2c009854203165202ca018010f0000c0101e00b0812111400300c1c00b4402c030544503584440007500d4400c0d01e1b4003095a1660070348004003082030201e801c1e010014084d120740d9000945501268000b1051f44c4516590034141c2c1c2400b009241044802c00291001d00849000d81962000c03181b048a60740713001008444184425070004002030404c0131610004c9070322002468180b0030700703070454503400d04124003014058094205403003001c0c0002181d4403507001510040c0384860588102500e05500b002c09200c2c900c0140d07114240401c001001c1d61036040c0c000502da80c0010ba102d446178200e030040402082c99010800c194031410714132400700c40d400400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 806010251 1250 806009001 806009011
    0x1d0718050a020406050702060c01090c150813111216030b040c060804020609040b03150106030e1905060c0304021203040312030f02030906071101110c01021801110307170c0d0206 78
    0x30422aa01c041c1160202d0003203000301000100d04001440c050300c1d10030060500c0070070500002654442966400041c12102c3c0d0009901d1002c20484144494019a03000e6104aa1181c0d24080c00c5c40d41d900e5001071422880e0300380c03054420300003100800300308019860014841d20b0a4402450300c1e0b090031400360760308503001c03070328007150320404681d1a105020040c01246d0284c403041c10883c1080400000e403010300f91054051180c0c11941d150000510b0a40e4001c00c1d00d0780b80000e8011147d003a00f800c00d440c08014042e40f0400c0b000d03120001342c0000b030050f44259810061520b80c1c03500d03c005021941b0500d40c0c0f03841444080381c040709220100f10760200030849610104008039101141c0416070004482c10b401300d8210000003404c1030f010b000003411807120000002025440017038404850b4020100c83e50003694082101d66418240740e070f0500c020308090806c2490148100400c1d43d49100e141001000484207180b040181940c090075540003e10100c00c0d0703041d01204a2009550fa00203c83c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 806011501 1250 806010251 806010299
    0x309040b100c060209061204030c060c14030109020a020c190f050405370f0b0a0b0c070b07020118080a020f100905011d0d030206160f0804061d07 64
    0x1a4100d80c918180592030144401c54498800091850711001c0094100703002041d0480c06c20001007103101001542c851080b0700c84d40b50101380410038102142290003640004050008840c04252144200720070380b81103811034107000d030352030f00200c02c12420811140700300ca070841421080300164504131042101a503010480c10008195580108010707268142c841d40300e05001903500c0c02214240000000e0703c440a103044800c40314062003501c04030343c2d406581101c1c007035a4074440401890000e408000805541407502c3c140f00561a15580b11407980c46142110100040c0c60411a409440511305c5a0400d080c4001d05a907a4000c880e111156003c040b40305120ba501c0e90641c900d840e02c122600d0b02d03815078602c2c400030705003c0150707011748030b00c500c14814480c1241c0b605080c0e03039504154a5064030a5000d0045800d1040080101751400d030000c0d410b0007030302080d1400843e0700c0300c5581da22580001001c10480100300f0320004d083d600c080610418007488001054810320150707504403c0590b50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 806012751 1250 806011501 806011511
    0x211305030715030e0c060708030403031409010c0306050301020304030203120414010507120c020109110f18090c01080f06150a0c060c181d01091d0307051006050f3609030904 76
    0x40d0361100d0041c00c29a60001060003c0070100304108c02443c3e00a00c42d060014070b901c180b007000040d0f99003ca4007020359a442e401d00c060401e625000f00001001e081c0d0083d815410a03650280d180c0c0110f95940009041c074000081c2480700142070505601401e070020403907400c015000030403103890080400f000b035041c0382a241c2150b2051141641d00c3e60400d065000c2c01144c9404c0009271a0140b1a042d07101c070140c40020045903640c411a80107071044002840038074031407c0050141400101428042912441000200e8035021280d0b031942f2003006206030340d801071810544428040ca00054074141c44c014080c2d040039040401c040c1001c424003040302c29156190014205000c218071069580c0e141d000042280149a82084010000010300e0786400340b2003000e0149513800000307003607900e030748a504841b052001c2d030321480015140aa07001c840310400d503400704071500d110906850140c102000d04410704900d451041950a400602c0010301d81407898809030303039410034483c061040e4501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 806014001 1250 806012751 806012771
    0x5010510061e0810050a12032303010603020d1e0e07050a1d1305060c090913050d0e011b0302150f061f020c0d0312050921130503071503 60
    0x703280d1480c200514048030103a140c0d084002290443e5010781200800540c0141c0031401d9034442540802518034003810182c480e01c28100103100300d4242d4011040303515149041120b642e0003400f100c0c1900e4540c240941e460041485e100d0061103001b443c500c41e05040c1c91440a0380392590402180c02800030215074039a902c1d0810440010710030701c038100541824800b09040c07101e070321040ba64406029401e003840c40c003543d1185424403d085404030420b440000f5079551f585420a641d5410100c0c050007181000c905940d5550303201401c240c604280302c0c20040c40846603104042104840140c2d0b03c03500f20829043c40e010b0f5980b000007191800e00c0c01c494002030f031850a0600301030300c141c10050401600c09040707500b50365842040c0c01030204500400f089006a61249114058982c2c882e40da20045582e007802001c00303e61028080c2003550700326403024915000d0b0011300e1010850300340d00c4a0350b540a1145515261540e039401540c150280401c005030010011100101040071034030244129852 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 806015251 1250 806014001 806014007
    0xb0417160312020f0405040b06070c03050f060109140c09150a09050310020702010207032405011211040519020c0102041205062d0109020d0b0d12110106051804020604120501051006 79
    0x50311354041c03220f0106000c02c0080c1d142ca0b401400304c52801030041c6181400549480c1c3c804062504159200e038040302c000d6019101c20040310340104660b00b410402255040170039680301d0405414107900e2030780895410707880da42c4c91480c0091124404034540d0f46040306040070f000107406208182c0300303010302c416088a0301064000c544010343d050b405030900a0865503004c40c0d0411010303120b00c5007840ca0458081000203031145a000c0e01503141180050a001e02d4001c0c0351013601622540124203013410302c112407aa000042c5082499070402503160401c00d200107009020f26070000591008002009040c41008522540140032000e090000c809580740e030650040c2c280c0c6400410881010010018481d0343e074081e00d025142c030000410540b045400180c040c1d07042c60810744405241110042c03019400c1884200381c0c0290000a00020380303000f002929080c0e1210900542280000c0003070110343e92941201c3c098400550855518206424054000c0c181243c2c0305ca20603042a4001c036140d80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 806016501 1250 806015251 806015257
    0x509100c08071b080405092517090f0714040207020402030103060b012606010804060e0f061008121806210a15123c0b1807030b041716031202 62
    0x50000c0b10b032880c03e07151006001c41f400004100500400c005c80d03642c0740f00b0310404a600d003107118954424804608144610300c04840140107e44507610243c1290100d40c1c0114a100450350096505000703800c018000c2800b0744540e100c029030240c4008004020410150700c4800c50718020f0b84c5180d600c0c0356440f12030001c0004c0a000c503500b0905c2c3c000050383c1d0b6209602550b0301c58442c2c5004035a140940314000d04c0c00c40510058546600510100030340c4541541c1c1d04001485c400c001440300304500102c1c2c2c0b0151051500305c2000d00d619a1405030300da124041100e506243e01c0c1100c81c0c2c0b241c01d800885900000c15540610203508183d2540140e101e614183c4040c2c5001803855500c40401d42c0d00c4002d0007440d40c0741c00c4000d44000d181d14103464030400c9103d010b14100003d05210140341c0c503107540c110708020003080c000b40810741100401c079000a2404140c0741e00c0140c0b21000d45803814000ca01840d24092900e0f007040010b44060380d00407545c1c448013442d00c03c0d240c8024500080c142141680 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 806017751 1250 806016501 806016503
    0x31b240b090a0b04020d060b03070e03030a170c04031b031103030307120504051f0b040b031b1908030a030c0e0a180902011112030f07080106120509100c08071b 70
    0x507100101040c03280360190f105031280400104010301c0c050680480d10b06569581d80036041e418000b10412100715009440c50181c00021000380d8940340c001d21010b0058108070b580100581c05101c0041d00c04075045085030091500704225400c81d072104025204900104d010482e000c0c1c4644012040d5410000144ca0203000e0340e884500305c800520407508028807005009813002d10948100001d00395005044c4440d00300908404207820141c42c081c4802da030300f080e010f54080d9200700a01c0c84207100004801d100035400321010b241180c84003510000c15030081c0c2180605000000c2d00b50010303505a8840e0700fa000b92921500f035542c030b43d070b010012420402e100d11011400560b0308a1985407282d882144400c0c4141801d156550704c2c01c2c5800d00e84888041200b8080d0400030500c1a40380c0005009a8400440e203040701141d03050100c001d02c4100c401511209140d200d0340491405502404146801c5031224410446040a00c40c018205007054a0040c04030f80c81c4101000d54181c7c0c1c03d9198511 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 806019001 1250 806017751 806017759
    0x1b06090f072702192006010b070b07050d1a180601091a040b13050a0b030c0d0207330e12070b04060b18060307051f0309031b240b 57
    0x9200c80c0c000c000a03051504012000319420002070309400384400d2030000038291503460b914000e038000d000d2085030f0314905c10140daa600000040080b0f20fa104111864268401e080001d00e4076000c0040e905802500300c03805615007060008a20f01e01050000340d0383c040c040792031034107403009400040041102543e00c21b0028014034030034000004080e0010b110709500310009850290707503812044c40e50b0041281c044a4004400c2c08120070f140c582c50100183c02c0c501c011034618204004034504c284500040d4450a0341c001c40d035a001c0c1b10402000101d6244003030003850000058042d104e1b0000011420361011500e810382c1302c52030700c01c001a550303410700c090b00031580703841c0c0325841c1d00000c8040100308491240d107429010081d40c03144143c41c04e504000c20342110160270550101810020a034220500071440035440410851100070050b8100f807280c1000030f2011242c0c10700f200d071205400280c8800d00600d085100800c48403106800c003014981c41303010500c4614801090640d03111703141403130780 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 806020251 1250 806019001 806019029
    0x10c1103030f04080f010e06060109030b090114040308090708190825030908010c03021c0c0e03030f07050c1f0f030f061d0609041e081b06090f07 64
    0xa501208001a420002401c4034100074003503540008a80c06500070010725000030421a265101c24055208002c04610281441e8500000000d184244510001d84144031910100f0220342c800c1d4481c1600007100e03139070415980341a040c050300d08030301500c44d4103ca20a1240005402c80c01203025034484419034525074801074503407940084be17000402005110389113461f4510110010311080b070266442600c40119662810000030708459008071414145401080000110903426001c04902e5160410000c0c50400c2e06c001203034142410300480d90181310016000c490000c0c1080540240fa100300121601c608000b021f00800c448140d245c1c410b071400302e03500c500b0380e28001d2060120001d075500d0000f034205c00c040201c00503a0101d5000c40010004188222074500300507100703562041040d503102050f400c00e550f42c00b150ae646000351900c0a521444590104541d01040700c0100380d040d0b00c007100030650032000f152120000d0302c103922188690b1506c0301e450316002c508081114400128862 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 806021501 1250 806020251 806020253
    0x22110918070b251211030f0910030e01090320011a01030504050a120f030515030c040b0409080c030903062202101403040b07090f12150b0306010905060f04020306010c 73
    0x1140c000c4000240d02180c0007509071840f0410010f0806034900130300000c609140c00b410301500701c40f20500d840209800403c0344100c0b0081c028100c82d079207030050300c100d40100103050007180104004911450306d9403d1071040c000307069100d16510415504a030317122000d240d0701d44101c0d00702c030401c0010800c0c00c803a4056008540d0b0285d40250380c00390040060340d05410b6143d98000c2d0300d505840790400070501d10a02840c030326031f1511070740390b204424450210b00407000c080065642d13003000e81c409201310b0319a40e03141c2050320b80303170003c0c020694408162602c408901141c10f40300d400c030b140454000d1003041e000410343c4240c0051224411103080c1101c0a003440c603028002d0590f2513040960521141c1030385c202030076110b82e00444c4201e020f46010369450401520080c034040c6503a100c0901d003450038105000091050080b5055142e02400d680300070010000c0c420081c107035515000d40d05003e10030001450f0b08a940080e803085008440341d10601114404000480c041613a8244c0094a50b1100134 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 806022751 1250 806021501 806021519
    0x314131b0f03080c0a050303090109030305011502190c08100902101b17041502030d1b27080304080708010506061305040903020a0203010f0903090920032211091807 72
    0x704040546050301d81805c41c94035218074643c802d070344a40c400d0703643d010442c00340b541c144907241c0034001c811141882002c001d04002d6441381400001440414510301c0c3d00b04001e50410810f00501b40d03401a58400842640311400038140718109a025008581c490014184207160b400440c0750f1079984019060b40301c0e103640e6031a10b0004030209d01020100008a08991210079403890580c0035402140d48105da0303504001034621316136070211501040705000c5101c54000807500d10700079051001c21100d180c01950356080780000da01c923440c035000010303000c40c1181c0085103220503070f00404024080c584550b000e100c1203119556880319002d02034081400745160a800004240c0d000f441120319441d940e4001034211150007201d5840b065680c420501050f400c25030310001400585820041d00601884070104411101c00a403036400c4004005400350410441c184080010214006502e1343c013490318642c0040c441011900c03d1001c14001411114107050030103450000342c0182085030b140c500d110b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 806024001 1250 806022751 806022757
    0x91b08060a06052b020d0605011d0405030901031a0a0e09070614180409150507020c06131208040b03010308040f090e10110c010905060a0c080f040b04030314131b0f0308 74
    0x203880c841501444d00c102607034401c15000d128500402c0009120b51410380e0041c10108a1950803001c0240f480411021130404415280015001e00740481c4238200294128500c03041542c141d544906054008101c9241c00c82e01c2074890841c2804035402d85880c0e200075111550b203040800c86503441040900c0d48090414001200c00030003a001084100b05562201620400310b144414030340d40e18400c0085887c0d04228410072400c080e181d1600c0d080300700450348c1500005009040e0f42c0150001e080080002d1442110014120846925203950b101d1070101e40540c1300744034154500c681d07118080b5140600348074442d2110f0f11800105014164014080090300000302102c0300c4c0035051000c04070b503031030a00428014a00c213102070581494602d03400c004a801401d01e0104000c0713000204520980142011504543c1101c140681d50395646001c4000d44000d01c11035000d21031450a2041c1d041d658400100024800c1c0c030600745102116004030030f40000d03481800c140e0440c55404002103280300c802 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 806025251 1250 806024001 806024059
    0x60c1b012a0204110d2310062f060705070203011103060907030e030d02040602010615031803050c0a02041d1011091203040902041e14101101091b08060a0605 69
    0x4a50305081103804a8000c44864100304441d124080306c00030300090100500c5c03980f00900e4020100c556007804802085150304000c10b40222024510340141c034580c404981038003102000894000e8940510020301e02e03004210304900943c2400304c0715510007040790580c0d20418014041c6080da58516208030301130f0504080044080c00104800401405d50303000502c0544980d40000c40d0f07540c6412000e0507a40080a4428109480c00c0c6503e188140c8000d25100e841e6050729007291070700c84002d005030820211601c000d500030310f8101c0c1c4a605851100703c281c00c81c0802000d5a00030640b80c03013040e0580e81e048104030035145003007109804c54030304042c000c0b40f080d0385d107411241840d03120f603280780803a44590000d226103010821042c0525880c0c1d800000903000541d00032005001e00004642c0788045000c5210501070400c2030746000c0c5100354030003154503810030380b00414071221004e4049094a40e0065065034003584c000140100c0031070048504490b00505075a9400501c028002030208103ca5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 806026501 1250 806025251 806025281
    0x9021c020a0803031609080c0d1205130f03050f0a0c090914030c15010803070b0c070303020904110c0f062502070f060e0109050108100311060c1b012a0204 68
    0x70882e003500300084c503c00c02c01c1d9603004030040c01d449005803074505107030320004460b48100550101070311103400c0c4281c90741d03101c1000074000700c5009040d191030148498030403270915010400603104100c0040303082100e000ea810f4520000700181c103e52680807105010f4420203c60504100068030340e8405483c440c06003038114074410501c0f60b240e00b142c0c0030b03114580899201c50701d22a203181c0c000e61480d00410410008500e03108042d5103000c044c403001403100c1030040c0f010607598107042c029011200c60904c020020002105640070380d40d07841d0001c00c40c2040741d00c07500d070404400d13031030000e0450300030404032800164001d07803241e0901c0c020001c1c2c6440c01c214000c1d428001590700d1012400d0300a8103035912800c1603000500d000401a0b0803503407040e41000302c803c00f400f0010316014140010f590b000030760044070400c09400302e442441202d084041c00c0c818076003000b000100220136140494002d80e5000b41000c50303000303170740003c40403400c040d1102d1a00001c440018079207584094800070580b5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 806027751 1250 806026501 806026519
    0x3170c07080304080304020a0f080a0615030210081b090303030a0216080a080613020708090d060b120c0406082e0b04060b0903100516050f0c0a1406010909021c02 71
    0x165450696400699041301c007104088240011498074036540809041903c0e002c0d00360525002019640300f05412026019503591614000e0071039130162900080c40c2c01800d15204d42c1082030008208200c12111031415158840a24821724240c400b15044c1402c010011400c0d919049a064006d601070304504040d20502900000040c5040700030345041801074444509a107400014050403210703101641c0051441080688005844c1c1c406407503031004103590003444d61803076240800003844541d03107032640a418065034500c0010000351080002c1c40c252001d0060590341c0c0e928540d1a80720703c021140030039040c1010b0182c00f0a04010405428101c0c8000c02c4d0240b0480101c0d04442c46c5411400c2241c2000900009508003003102d92085c04039020304010300d240442440a41c42c4140400c00b0800900055150900405409540c42c41c040c45d0250b5540d0030080c505000c1180c20401c1441c2c540c0101400042c40d0b4410744030b07035401107070050150354024490000b0048003140b5003078126031140c119 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 806029001 1250 806027751 806027753
    0x30702190602060606030c1218010509070f0f1208030c1201120b061801061b05070b1306020604080d2309010f0b0d11041112070201020d061203170c07 66
    0x21944403450242011400c0c62810403100a0504600030040341c00354030108144106011044110b0b4420307064030700d01290b40d441e141a102411080851090300304e60030001840790070310f004113200b802c6640c81002950034640c0c0300451200044075210342c0d030003210308a0b000d4000c100d0290081d688a00f080d0002843d0840003503120000482c00c0e003003114a80d0100c40b0ba402001a105229500010105c40c00e40c0000102000740343d05d844140141000c10201c0094403902c0207000804203001c03640641610321568a07800000341c0c60300070101c400c6000d20310000029017a4008202140a02c2c0c0080084c0c3c0b420920403103010150440c81084280c1190402d0354510034204009803500804c808030011500c000e0420045d02919014005140318046c02c00605000890304140d1540703400c02614040707a41c1d0818008820301e802034200c82c24a000c003020422003810350660040c05100741c00303242003181c541c0380c091001c240012410000d01168618141c82c0c201c6504030140343e80a12021007561074003c603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 806030251 1250 806029001 806029009
    0xf0806031c20070f09090b190f0509011506050f03010621050f0703050a020a1205060d02030a03091d01050d020d0c051009090f0216060f090f051609200c030702 70
    0xc050b01508158210140c2070043d050440708940042442210030300c0602d546e500c07041c11400018010740a031540219225004034440d030054800d032000800200b20501d44030140358060300718034a006c51038046400d00801e107140950140c9940e4841400c042d406c0d81c5c2040b405807070348041c1b81c0e44d41d0100740c81e800040d0311b0b80b880340c050f0728030800c80b01e0b006100c9420035480140a0b64005002c0600040c0144000c4030040c0c3d20020003030711403141040101e01600c90f400800c803038141040019405000781c444c410181134005036070358101c0d04240b0041d44141c0082d66024400d034000c1c0a16540003050707500090152420b00740d611400350066601c00d003413558800004215942281030040441c80114080082c0311044c858810b00c0600701e9003d40c9042808048075030041d0100f0f400030003203a80d03002c58506400c45c0b80d003c1c070316150f0303c07070104a01d01d2400d0a1507940c03100348400d82c003140c010385100843c4d201c01a000d0507200350b03094100d0040c280d401443d9440190008d0304d9281d0300b44010701c640340141c0c0d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 806031501 1250 806030251 806030297
    0x1a0f0a180b0414070506160303050c040306060602060f06010305011a03060a09020a02010e0c0a120b04051006030803091624020c130b010908030406050702040f020904050a0605010f0806031c 83
    0x1228000c002800082d4221403030600700b195008500c00c0da0103115824900241d20f4070401f5142e45403500017001c0c1d50f1020348502502641d000904801c0c504640403070f00a400041c1580600038151400d0450340d6440d004400750b480074003440b01e11640b0300c800090040f0620000d150000c7c001880e9288103030300c3d0208842203800004071000140c0d12280408d00c8400140015400d8031404d90703094295a040101e002c2c405955030b1401001042000300103001d1040901807c0b05201e800749091204035600c2c18142965042543c1d10740309406850985035840c2c0c900d1261400b118141440542a1003c0c640c1504084a0601000d03065015000c0e1041d002d075180d0b02801c05200f017240000071b041c50110001010411503800841182d40100414040140c10006854038250304840110302200f03a40c048001900031034514a03005802c002c00e0010750011070b0040001e5500c02e82e2905034091501e0421241c48000761038058140c1c104c0c01801d600740040401104126000d814004c0221035043c85010740c0c01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 806032751 1250 806031501 806031503
    0x506042c1006090602010e0d050705160303050703090902031b0315030109151b1202160f061d0d0e091b0706050f061e09040213060902071a0f0a180b04 66
    0x40780480501c8800e400c400b04030042c0040d440200400741182c20340c50384d11a480746500091000109000c0704116041001700d480c0400e182103480605c1c1d503454042d0464101d4402100801d0003102d0100e180940303842501d1080c8900c0802e2a02000381d40c130307100000e900150400712060303c221800003030340d1424001c401c0d074544180c4000b8060581d020007d001c86d10a00c00c0c03e0204103107410303000001076010401900076404000b0059840c41d00d514010300c80700e002d060040004544900c40828014998041c0005000040d41160600007088000da05c1d21601071491003c9421760100030704608107081010391007003000071700800154000c448a9040e41107000d0880b00252541c00700310500d45c61a0750590800d40946812410740c84d0071548086080c19401d440b8000d00c0302d000024295074030441c425096410b00740b801c101c0c0d40c1e200d44044002e50b10000302902c400c0d07001d41103201090003500c0b00c5449010403001610f001e84a814040f0081e102036622400e0741008210500007150040410900503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 806034001 1250 806032751 806032771
    0x90219030b04020f0d2103020d1103070f03020f070b04050705090c21070504182d2304020d1110050702010e03060105090703150b0c0d08010f0506042c 66
    0x242c9483d00c10003019203c02e1080e9030003100c20184940026409008680340988096031034030280c840b21004030001d010300c90305210b0701810b006101d00e00e218018020342c002e031600d99440b54480a510f01c10b8044e44103001303108010410401c491b40108103182e0361140c00c503110b54150f59100e81c0d900000b0340758240a65042242150014106400707084500603030b02c00c1c1142c980250118540f0000180160144e48915042c00703200c40a2103550031a9a4804035043c0070b50280e50001e21902c204088003c10f500ea807070001240380221241e1510002e8280c001580d030011007800c6591b6482d8207000200c0013002003168442c4d0b28440d210003680e69148464110340441c0d823526155403850000600b02c8100889040c02a000030005108685462001030344c0b0540b1070501140790303200f9080d40e44d841c0c4015848503901031004100100c0900380800c0f004952000d980d182100c59889500c1c40c14645100c4c0b2810764803401c00c2104100e01c8029000f1021034035200c2a043c1900802030030150201082200c842406c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 806035251 1250 806034001 806034023
    0x711040c0c031e0e04150806040b0f0901050601080606070f02120c01020f013606020f18040c0f1d060309100510080a060b041d06060102100207030203121503100c1d030c0409021903 79
    0x303100104190b5000290cd0000d01050402000103000250301070314444c000c480009946083c000301c0305847d40619800b03024000f0108100e01e400d510303503c03079459a900500400182081e042070500076605032440e451508000d10352010341c01243c40d100031010b00c0c1c6001d48041c040300819401c0c409020304c1500314a0301c175500c180c50990514030210142d6a240b14a103020600200d40380d000825a03051091400c01c65204001288810000441105403940c00040001006200d800c00728541d0a50706d01c1850a10240e20346a845582061441c040c01149510211038000400e142d504400d805034005400000d230415004d00e0102e40e8030303405070707080c1070b0740d1195042c04280d59040000162503d2503800450806a203590000e460b40b1900c40c0f50030f071090303c2c40c01203820a205001c3e00005000020115510f408000c001d0721301804c40400c10001055030341507054032580300003940d01c52404004025240483c1100d04003c01090072403001d0b600a0311100840c260003803180e0b042c80103503004800b0302c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 806036501 1250 806035251 806035261
    0x10e0c0d03020a14010e010b01110a0b060301060510030b0306010e0c0703031505100c032a0b0c09041b1407170315030d020a0507090218060711040c0c031e0e04150806040b 75
    0x7c01d40d90300c0c14004d070410800021280c0b000c0d5020038807031001c1d07910000d00c0245441e00000a03014010b940c11003640701c14600c07900703500960160700c82c03184144107406448407a0390b01c030807000c5882e800329492800440b04102110000c0e200342e018000400400300120445600c540111301010010120329020400c02000030040c0f603003081007210000d4440c12403180602c1d000c043e1003220482034030028007140001c1c2c0442c1d2214046016102d00d0310f8050001c100c10640500741004210f92040100007040c1545001d1441030800307011142c495400024003e01586501501c05a90303000070701c1300f00424035410103440d60fa80c4c28170401e015103c544c2e0041140d0700c0725040880c10614254000d0b039490b403040000e00390b9100809030040f50103d0490b6520b4a48500d8141006d400801d001820361140ca01402c0700c4d400d540003140070030228000e036190300403615100c0c41142003c00c41c0300c0c04c0b00030411200e208100b51802e81c00c800642521004200303001030341d80546900d013040c01e83c5d0461f0742d02c610b242048 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 806037751 1250 806036501 806036503
    0xc0708060112020112051005130b03030307181706070c06180c080d1115060d060f02041802070b0a0e030f0f0a080615160f0b07080403020d02010e0c0d03020a14010e 72
    0x1c211700c034200c0c00401150402001c5102ca0405c0e510074180540212003003082d070001264001e81050b82c020301a2560303881c002200612854200070b03011908001c00700c2c003040758400318500008440b00c1600a0907a40c5800b9001da40a180c0510102c2e20261140c1900112000e03491880605620070440030028904200c0690b0a04031a26110001c0007884000b481c044900010781c0045a0400f009450307454440c0404600003298010002d80220b08103600081154401c0d4020022906010a518031000740c20407100c06900ca0050042c000e18481804524150402c0c1e10805000c7c644504823403804d4a1000c00103400e8200e500300314650000810303481c18003500083c4665110800b01c0c0d811140700c046c2c0c9080c08650248007504500c0c1c2060f2040b001c1041200d0210444c0650000002c26a92a10b00d03001080d90790300b1141100180100031845201c6401406060403450207000a40390907081d2509104280c444440150114442ca02001001c10a85074441e06942da0220011032181a50341080b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 806039001 1250 806037751 806037767
    0x4020c010212090d180b0a0e1512132a0909050a0b090a0201140a14070b0610031a01031a040e24070816030605090a02120115050405060c07080601120201 67
    0x80000d0010000c1719501900c81440d0000a840f184d180440d151030031b801c1c0495441e10340c9002980c01100c0701004084c9203041802074510001e0390101c0d0b0409590703019a02081c004542d500030411072a003180300310f0343d07000c031060400c1c13440788076072030500c0256646004401d9900f40d070703420b5540c0e420101e5040d051002224440750702c4820301004240002280d40020314140d6100208190700b000441c0021190b40705900303400025201482013512841c2d20300b4515000340c000e0300c4a070f20584007802004480c502901035441400d014646001c0c1c0980504d0055010705040d80d20010204c2006818020340c0d81c446c4502c00c0c40891700350061038401030320380d1540c00c01c100c990291f80b1103074200342c10807966660042c8840e130300c4480d42e1504800d0100c50715040d40a000a82c0001d80e1040b00c0c441040b16100e11540a41b0250700000300340c0000d80da940c81818120660240034000040042201f0700c5076081c11f400a100d580080d00c102c9240c90350301c81d142c5040440c2031f00701c1090094405520000e540e800511 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 806040251 1250 806039001 806039023
    0xf16080c0d02031e070503030403030914010e0102280f21050f09120c0901030b090c0105040812030615030901050f0601050c1506030109050f07030501060b07080301050f04020c01021209 81
    0xe0400c0c0c0101a0b00001e980d444800d02c2d0903910f204000c91000b441c02c0620444000384000340449466a03180c0c5000b601d01d0b11180240106280441821304d13056124410810b40301006802800e00c21800a54540c11040c0c03100040d05108039107051030001420558110400f01d006185900303040300d2701d00002c0300d6460800c0701c0741c0400205001c10a039a81e0018116204601c08070cc00921060240420074100344021300c90030740c04100c02c400002446407840100348541c207641c0944129802c075a00541d00f5014038010f24840d44d00c4801c42292820704500119003250b40140312048001e842c0b03d02c0007256104444900d41d0340d46403003d00018074800d0541c40d4000b0401d0030700c60304140d0445500e82e07443c1462140c89900c001d028001c1411501d0a601282d2119040402c4d1602043c44a03882d95131000a44012100396281a070005a500c000101703440070300394041c54440c41e59107484104920320851607102c0d603116a00304458880b0500910052442c5002c1c0100c1d080e0b0352a0034440141003007a1144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 806041501 1250 806040251 806040259
    0x10809070b180a08010509300d050601050705030409061e03080a200703030819090818010302132606131502040306050106120608150105120f16080c 65
    0x8060100320301c40c1040d100c8040daa9101c282d071111103000040c440b9000d940c0008040d503c2c1c102070140c83e80700419070032141050308801d130440010102c61682c09100c64020200c801c3c2d818803011001b0600c5400041d004070051400908008280d02c038182540e12a5006000760303a0760b85c4c020015001b6a45894008140e480000c0e10890b01e180c03555451445009004c0041080d1281082540c0e14107420400c0907084c004203e1b800710303032280381c040d00c103e406a401d6840240702803031703680051401303005452a0903400000c280c140031031020031030b440320500c12106044c03507028001ea610341003d003514000200440002c002004250501e0000b095842c140141c026030840010401054942082c0a244c10f501c80e1200c0401c1a00c240a90000d001d9904000d101c01d05180c00065000e60280305402c003035202040c1040340941e140c40e1203036507000070172914402c6a0545c004100340c3c038018040f4444003480c40e080d101e03031029020000781406d01c0c0e411504071900c10360105102ea440c04114a58000f00c1c06e039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 806042751 1250 806041501 806041513
    0xf07050f010603202e090909050c011809050408040501080a0e07120606120c060f0c050c01084302010b0a05040207020d050f0a0209070c120f05040f0b09010809 70
    0xb07124800280302c55004c02c400d459058030064100c0e164a140c00c01d03501030b45040742e4403103110f06802c0c07801e9107424940040001c2c4e40c040c0c00302d0001030510460a1a5520500a101c2c81044000540e400d80c180c10080c04a11422140090300201078020700d88542d1203802055178a45c10480007409414000c2d01105404d403814403001c48140001802c13006079095403100440c201081c1c50f140b80030345440d4002000e07401100d010007003084080c0c0d201e6010340c4c032941c884651030f20701c1ca00b00300d68529848034040c1c030a41c442111290594003520446400240c11079004041c018240704210040c5458141141c201402080b0081c604e603210b074100c60305107800d00c0240308565403140040e8400b811800f03072912130f6070300040d05802c5541e01e14180c04940e030300900b5240c1d900c00e00d01c0241d171a10810f4009900a83d00d60002800881c411000f5442d419401070141040e83c15019088408109001034032013030150400c008500071086000545c000d09042c400c0719074542202000500304480030f491014107521131 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 806044001 1250 806042751 806042753
    0x312070207170a030c0b0a0e010e030a080106081909031b0c050a08150a0c17151503040206070f15090f060608191202010b0d080904050c030115081b0f07050f010603 72
    0x5c24100ba11500b2280070ba4090300c490b010207005000c04500c4d1403882d880c0280201c12240b021001d03103450a681e4031102c0c1d03141c0e03840f102aa80410129044c04e821950500c00c00000c0c1816840070344e500d0f00900c0d04101501c9030024691300d1b014814400d50b41d00c01155020015460100000c0014011400c041c00c40c0f00e98840109242800140c417154803d40c550410700082c903c0741c100c114a540c0c40b8045483c643c11300d02c900c604004e1819825034021504c240b1919060b071900804c85c0d004e40c0c0c0c040c0899107054120b4130341c202d258460140c1140c4407c1045518480f090072030140052060040032203140002d0a072400e80120b0f11580e03c03140540c0c00000d07901010a07000c2c0000c1040a4008050102020f08203a0880c014102242401e5101c0700489403942071000b03c0002d84078151080c3c50030032a90700c40058000340c90009105103079a03040c034505401b841c503200320059500183c0b6032054281115100d100740d02d0641045440c0c0219450100f01c12003402805c01908547c0c42601c80200899425 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 806045251 1250 806044001 806044007
    0x1a09070f0f0e030a0501051e09030702010509091b030a140f011202091f0e0105130603170c0a02150c060a060e0f041a0907440312070207170a03 63
    0x10030658506100b0741c806241d81c1e580b0184141e894065105000300032a1506000f95840d1341c0040032a122507800d500c00040540c103000003202c00d0a0340503103070a42070200e01d40c1007001d64100141456410280c2c4260681102980c5001d076018182c000c5010680000e0001a40c1e0428002807a042002600c040100603490700700417000035954051701c10740c0c07952f039544041c44441040d60410031054071045000144482c1401911410b0342c2c0304540c0080700c92048055201503074060300024150940200710030350343c5c1891034002c0204908990a9880325201c81c0c0000e4020074000240d00c50441c40003a0700189120705100b40c41e80010614420460b507811b00c8100d03400010000d14505a114043c0049030a00c00c00b1030040101802c07081109034145400c14850b515100d01e40300b4910785441480e840d080303400175000ba00038182300343d44001c840b560048041c0c0d940030700040d4100c03c06004c01c0180c80d0491018042e03003031107540540c0080030140e00d0000c8440040a003101d010040e500150f00d80800264 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 806046501 1250 806045251 806045267
    0x11404050f1014030906040c05100909020a0306030213050604140f060603060604090515190509130609020a120c060f200f0d0315080109021815041a09070f 68
    0x41c00781c03160811a80355640c00d60303500707a002215606401000c0200b0400007400904148078901c0707146c039141d00b15900c1050207125135100401c039002c0340c82c00c60300340700703140ea035a0190081e1407841c03401203600e40d9240c020030044a004006401900c0d01c1e0010014581400d00610701071000d8001e11030054500724540c08551080a803140e8451800040450620740d01c1c20103490261151010030400b41c108020358144001040340300d20300415070a0002c00c4906a0714074100308540c0068803050969455491180300b100f101c0c80d0841e034003503450111002503280c1c038100c0c1020b032484501010007040c40e4100140302c0c404941c001c0b4104800310b48602000d1354050502502e144411a07045503508c40c00030301c50b0402c0ca00c1001003185104000381002d280354141c004114061805004025503038030341784181d003621812400650850300710002c0001452040c030072641d006a41040014010802c1000502034440c0b1595100b40208004da41d4010781c50205103158014820f400c2842200001e107402800d440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 806047751 1250 806046501 806046529
    0x5090a060c02010e0a09090302010b010305012d032415050d02060d0e010c020d0e040506031c0905030304060f0e01031505210d03051602060405030409050612100b01140405 75
    0x2000c0c40500380700b164041c050b41c04801000800789104e490b21a25007000034a00d032982500158240000d1610a50280c49118140e0340d54075404030080c2c40224020140c4645010b1038481c03505011000000308204108242c9c601000d65400780700c03003110b507003d0305c00c1d500559990040d840c501c0c50100026950b958041420680c1510b06c152100b90804201c0014945115260041e508001e100c000e52640407603464402e003c00d0f03d8130200d40c1007410a1000300d4800319112034141d03110000603483e1014044141c010040c161400384100c0c1d44402c0401d0942d08251700a00c0030441d201002c90380345800602c0c00c0d1002c10300703190401a5071b04480c20314880c50024030405000703604440009809070440b180e5604200500301c1240d45114000300000e000b400100c0c0c1800781007003100c0e400d0f0000c0f8804952039010760f812070002c50525003850030714401080084c0c40c45900021003a04085804020f1094050007e8503100014090402c0c40024180d0303e07044212600b8000108410f103c555540c803102c801c44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 806049001 1250 806047751 806047757
    0x11506030e06191404060501051903020607020910081c030c020105090a2414090607020303090a120c150501031101030c23040e01031101030f02070210080601020c12070f0605090a06 79
    0x43c5450b500b074001030824852000e02505260100010310105422450482d20b003610121406031440600d10b425030094000294401810802d03800503103040341000307400540981c3c1d45602240e803039852038a003d904d00013105c142d0305280304020b10f90b6010312420003460400d00003400549840040300e6191641d506004004290071041d0204500070211100806120b8110411840c07040e00b0100540d090201c0d4060054030a680005501902c040103a1380a146060010041c5034042d90314080d882d5254001326040210500122000c01d2819206081c507080c5550009155415030500e01c0001c8892a1598185401c0055140150341d00c440d50b441c5c45840b119020200b0200111190100e04c1580d020840c21314a150022043c890303030400810359242c00f604d003003040c0c42c01c01c1002c40030307401503010280d800302314143d4010440e40034110302507000c074052043d92001103074200002d4142e5102c9410b1045a8041d240c01c2c0221444640f040010301142e0920a0500717040c0340004124080f240980b00030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 806050251 1250 806049001 806049031
    0x50c0d0804060e0106060503040c08070f03060218060301090507081005220e1c120c080a0e0f06100617010308030417090406090c030b0a0b0d1d0708011506030e06 71
    0x6100d0303a98440c012030f44800c0300038001c0b141e8400c001040390f00140c070306071644400c5440c0012a020005240c800725400c003404000e10501c1c60f03c980c0029001909003032900c2210007010074440e03031084020f60207003548100000e041e040c4a40c00900f0000c00a107407504c1140c2c1c5250502c22540c80614290300020f105c1c07030030b10404070880c0c4454013a0900001c5e84403d44a0b00d0301100c400c24205681d213440c080d82d959030301103074004401141c083d181410409008644128045001e40d410745e0460102c0000703183c11111101280a0540e180c694202c80161072540c141c8814000140e005401020103034901401c080715504685078403002c0d01c03002d007009052010507405424110908400c0d50100c3d18010001c00c1110723910303e1201c01400b20251000c001038604008030020340b60084640c015141500c182c2c81c10006a1018640180300260121014038081083c8d4140000100486d5024051300d20010404001d07440030385404039107580126051509022104120500002d200d0b84d002c0244020703030716 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 806051501 1250 806050251 806050253
    0xf1704030f0e030d0e0609030106092a030507080a0e0a1a01080d020c1e010903080712080906040c060302090f0607080909060907020a0605040f0203030d050105030708031828090603050c01050c0d0804 87
    0x5c0140382b107070f20010619040c40c6d41082c0b401e09440d00501d0007800c8500d0b03010b40210f480780880880c2d01c21074452000c90351500100d50035192076070268501c840c0d20400c440c440c00c025160400c403003010066803000c1550880060010074001d210402000390240000c0001d810104001050361200d00e510310480c00201613461000c0e8820300c458001160072500d56990780c1182d044c044e01c0300c0707070420501021407a07000204403c9880003880c40e2040c0d81251940500904100e02100170f5071000d0ba805078007220800002e11b4540d980750091030700b14402c16080e650366041c10b0a110303040e500101030600c5002c0f6a03040001c415004241801c2e6203502100000742c0d41d07200d1400601c00c0202080194040c403012402044602071076000a041e0b400071800c5884c15030350391040c4d940c1c034070035050b507030519408071100004103082482850b22540078803200c0c280c584809024024004185511155015480da0000c2080c00800e001d1f6140e1040d003031811030b14148841020035030300c0c103000070041d0400c103840000074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 806052751 1250 806051501 806051503
    0x2060301030b09012307180305150903041e03150c0903080a020307151508030a090e19020a0f08060105030f0103080904151e05060711010f1704030f0e030d0e060903 72
    0x107603041816a010710f003060014a154491090105d0701c8030045041e011800c1d100001c580c0d01c00c1f0449a0000092881c045e01158500307800c4006031200e0540d12082c040402c0307522030f04c1c0d58410030545050104181620f181401840c0080a1510b851441d20701050700701b0443e4004e20020550740c00c00003440e41c58a400d4012490352140f0b40010340b0300c4094031010113281c04c0e83c1c0c1103403045416143c00f4409680d00e403a100340c2c403840303122554030110301c107064104101152095015405020b00c41e00d030503075141c5440c0305001d9034081d111034800101c10303454194443c0d13049440290441c0017881c0c06400e5160400c04e845584406001c090a00040810880415070719500300c02200030381d0300a0f42c01100d50b02e001044c900504510300003040d000049000c2913604003001a284840e0b0401d58029020701e40900564040030591044030030413450340c80c10242030048084d02c1e4069442542d40e207101c001e2040c001400d106c90b19818030300c260407010700d42c82516448401545200c000301c810a69a030140b600007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 806054001 1250 806052751 806052761
    0x40305030d020403050d020c06090f0307120b160c15090501150f140906090f22120e10170718030b06040c0908061b040321090501090302060301030b0901 67
    0x104540310001d200c1c90801d5040d006803046034819022103e40c0002c50a060303032034503410340c80141c21030700a002c520410310305044003c0ad061400b405445505445030790141d11b014100300e05032804410502404405200d0380460080000305190903059034015a4513100c00210103911862400d031503000c09420701c0004e610000c0d00003803981610126964820041680d880107224034840142d103124100b105080210a41d4411782c0018040d01c0c0594811505106100c800340060443c0030390300b1140707046444c0303030703a01c10306200d0140407031041c82e4010000c02032464110f038580358001c4003840c001020700d80e00a151045200d14410148149544400007102c2200c1120350b65000c0b0000444000140001c0744002d60064405850a0050003011601602d041c92103100c2c502059000320b00144c10400740000c80100039440e00303010f5181c01e682c1e48501e181d040000c03501048102d40c416103403643c140c1084191008150a0821520088c51078000a03254003051002410f008030520009020701004e51003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 806055251 1250 806054001 806054003
    0x12a020d0c0812150109050f150a031e020301050a0506090306070e0111030a0306030c090e060121060507020f10051909062012010803090a030602071a070e01090b13031202030403 78
    0x10f8003991400c88440c10708010400d240c140462009000480c8a0601103e0882410000303800b000381240c2070301c59859542c1c0142e0621041503506c002e0b4001200e401d4031003000151040d8405622541450b040004100c82a4046441071200b000030309102d07203000c500c145e40550941803a001c040b51090042c1e401d00c8005425110601002942850700c0d03815501000a0701c5c0174007000c14010744c5641080086500c96041c0c0340090703001000402595250030304035050000401ea513500004a55620b6505886042c0c0340c3d04003581242e601000f080d403042200304132003007203104140035078204090610309503480079184841c0c8603200c40b001c005008094105909241203016558800a50a09228440d400110141180c1e012007000054616000010f80b02e107010014595a245c9281d0b507a560004e500422040b1043e810300d00c1d540b4059080410702030b00c00c6109481d00c50000080b21300040048040340c004100c80031043c0003240b40d88090800c2402600e500210109000d580110264558021540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 806056501 1250 806055251 806055277
    0xf06030210111e281a0103020f010c2303210f1b03060120070f090c05070b060d051018202b080c012a020d0c08 49
    0x160341d0320030310307840030000d151181100c003a1200d4602e80c00d03401c42401290f00c0701030301d035a01002c15031004160348842e01035125502e00060809040d02c1d510180ca046407203e4680da019004801041942803240d1a61802482460402e005d81d1440d601c40034000b0500d080321602040100d00508003c1e410000c40c1c503034400960502c1d6a803580074060301510002110180c20607544040400c50035080021186a00c1c0044c0c01c00e1825503a440c801114805030b980ca061958182c0303042c040500300000d01070f101c0034242101c11480301074140320030704090341c3c1e0300c3e4100d00800c007080100c0c1d00844c1c100496160403650407548007103105c4c1c06007029484c1171480002d00600038513091104186140c00048801481d200d03100a245030407001000640e50758540303100681040280140110105801d00701d20810f4920141095820b6115101c071205500100b1400c000d80c1c7d50360716006000341e5268410b007110400c0c11400c0141c100d5040009403645401203070130703052003d60b9032404100030031001501d845d240000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 806057751 1250 806056501 806056519
    0x50307030e03010209091909021c031103030c1c110d06030b1b090904050f2407171513060315110304150e030405121c0809070506070507030519110307030b0601030f060302 75
    0xad00103908080082a046011945d40c14540040d80400301c00e41c3d01c107041160b00c0a00b0002040b806000e03031400c49200d2a05a90f0751412001c542e0341c0b01000d0300a4600030840050a00e0440ca00319052203c003405201c506080d540e02450300e81651303002c6400506054805210700d0702e443c0360480c64888628098400750290340181c0c2a0304140e080c800704420508246510292036100c03042d42c202c0d0b0140302903102d459807040000d02c0c1c22132905039074901660150072020703e1010040d141040b01c906420840382040e02e0489030071841c14034003400e07505070592980d035803442c10f043c1c0e66150444100f41030119019140c448140c100c54080c07044e24010000035024424401401c0d2a90761100c1c0c0c2010390011240c1c030508184d48052051222a1081540d84010907020b07040600b000001c0c0c0182038116950302c81d0800c00320001d8424480c444805074480721621005000d86404003803090940c5415019a000358010400308000c4440142c216100303081c000703110420703005840d01030301c81a0400780d0409055 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 806059001 1250 806057751 806057779
    0x80c0129280b190f0e0118080d050c07090c0822020a0f03141605010e0a0f090203070912020108070e04020910020f071a071202030d0603050307030e0301020909190902 73
    0x508001c1411442c030f042040039041c010001a80c54000d448840740000780b500040c00720342d501a18074000d1021410301440080356884401e945000420302d01200000e0b004280e468000200700181c0001e40034598080c00380a900c0f5100a04204004145a4400e0b1411700031980343d0140a480f0700150b07802a0000c01480d40b0380900f60810881c0d48021502d51403000d42d4545080008681520000d902c81580380700585000c0044600648807002d0690000041000084e1140703114181c500402c0c05c101d015849160004019105100d41d030f001d81c1c14002e680f404a001070385c0c000c1001ea445629820300e5a07120a100d4081402070007080011a004904802d0f900c1c68181c0006100d5280212031040700d5a0700d854071804240003008601000240c407080c001038001402d0201180d80c86041407049909007900058004251072440d07005680a0704005031400501da4043c851411864040d402135107880440d00120714403000050201d8904000b05104440d0480c0c2c0380c1203500d009070002c1220881800e5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 806060251 1250 806059001 806059019
    0x28060e060906040e0a0b09031b0a02030c0a06050a030507120c032901080c07020321090301060b0a0206040f060e0a06020405040c0c051e0118080c012928 67
    0x159400c030310410584000540d1860580101ca40d5a80c2c00d5024001032130700ca5130751140c00000030304240101c3c0424003d843d0480c00d94403000b0f1160010b42c000384901000c90040c9800d01902039080d80c050241c9107014003941c0e80000031142e03030740304520300000c1c550303600303007080700e042c811080d00c0907005040c900c110486562540141031150703140710050055911001c68103480d64030741001140401c1d6940001882e40e04854080c148450006c2d0959000340c40d6682c0206a000f040b00c0b170340c24409004101d1401504003441000040c0000b110344038034106111300003a5540300e0003080108103034074100f00c0d031007040030940001e0103012020b412030f4040070441c80c14201a4001c2d014403401a0b1a02c05481c03cec4d10b00c1960400205070308071015041000d4903540c2c0c103406013130340800400c0701e40d281c5820340644080a0305041699010704200c588507841c0c80441d40c2035a580480707003518524856070100c010344140b2895003101c0004c490348120030103019810915800306801d144507621100100280102c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 806061501 1250 806060251 806060279
    0x3130f0f061a03070609180e0610230d12030e2a0d030e12070806150907080103170a14030c090306100308030402040f0b10020304080111030c032806 65
    0x40c810104092800d020b40a0603610b06252081c140082e9480c0400c0141805040d9104a52801880f011804200c4004040d14001301580e081d9583c0700484010080712302261603030420f108000600302031810b96800001c0320020681c1c03000c2c0031199848007540307010340079074024541d10707900d5400d60390046d488020078280409801000075010015852004040c42c01c64003802095034592210180c4160340381c144000c2001d141c14000c460b01c40d503000030440c80701c00c010452140c1c504100060340441d401c001c2c442008400391080e01801001c000501c006231011030800c0041d200745581d50385900d180041115242040454414034202c00803c1c8a500030120000308076000d400d03401c9407903945502c044000100400d20020f8801c0d40140f01080c01840d0079000320000381903404000c1032809040000480140c100c4400d000543d1000500f0801e0319400c1c0645c8803040d42c403981c074501318501220f14140e9884000c05520811203c807900400560f103c154510700c0700c002244c204181c2e034a0b041003070b060315 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 806062751 1250 806061501 806061521
    0x16050106030b091005040b010b09180a021b0c090105040f180f050618060714120a050109050c0a020c0d24020c070506071a0c04050d06090b0a1103130f0f06 68
    0x7005001485a0058645c001c540c081c3d9070024082c41c882e842d2050f00c4a840c1c01c52045141c0c061020916241051900d100395400340c21000c1d0010790b500c0310603102031103030131828941c0411600008001995942d03980e8825044802c00c0d103004c9684504424013100500d81c405015001518020340c46061040302d4503501b6040b4401d03000c813051500d8400c003140c1c52004024611640d075001800140c8036030310625440c1d2240b5130b14601c040c00c01c1c0c080e02c491102c01e2400c4031021841075981004020301c4c000e40c010507070000c05a428951415030b807003c0c000e4440c812b2201860044510001c0f100801c400f00c001ca842c0744103001a820710002000f9048c40295008407800c0440b407080b0700f400300e4a450310404807a203140d4400400100c521007003110540311140188039030b0a20038144400211915200031011007079108800000e0084203614042d004860058008901145005141c0b06103080000c21203401410702420310b00540c0141ca08080d5006824000505200d070f80c660040400c081500030041807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 806064001 1250 806062751 806062753
    0xf01050f0906010e150303190521070e0d020d06020720030106120312060b0a030c1205010e010b0c030f0f040302270a020a0201110f0405091503070b16050106030b09 72
    0x903200c030711249964100a000d070380c0d03066600b5004140d104138a40c0400e90310f00c20140680b410300780c1e40340ea81d02d1400030068060011850000d40301c00c104000480000d2804118988042d039401c0601c40103102104010702a4020055103964001303542d1421003030f0301080c0c1d2000b0b0641d80c6910b1480c24407154a50325076201044201080b01c3c010503e8107004503003e90f03805010b41503000386240c8007201c101c101800b281e9481035460002081d150081c1d80140100ea0854901050822880800800014036550780a000350b01c0c0030f0041c05101361048081d81114602905a900d030810b0081c82403c600c03502d1601d081483d13001a644d091401042c0c080c1040303d00881e10b00b43c449c03003100305e04098001680c0400c0303503481004000914030031007903001d07040c034030b140703100000b5040c070f680000a510b68010000310207080310208003048a80762003002c040d40b200d4208411040002488040380d952243c1e4043e4000c9101c0205100802140b45460191801d4010000744800e544c0d90803d4054400292049851 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 806065251 1250 806064001 806064031
    0x9010801080a120f03020c060115090605040b07032307061418060601080a060f0e01030b1308192a0b060105130e0402010e09010b13090605220e0f0105 66
    0x8a00c0402c0105500390400c00620006045010031500d0300024030106090690900070b402c107203942006000e0203024043d0139070401d090600790180114030706600c1030081003c100424002000140142c1d41c16030f900d030400011101000d0405103641014444c00d55000201041113024000d20343c1180c013489051100f000300381c0d00d0b400d0541c14020b207612101c80041e404103001c107080c1e51217101d0580c0d00c00c02c0b540c80000d41d00e44409020100c41010303480480c1c0c81c2071200040c814086620380041d04241000c0c0c82184104040e41c1d6204580180c0e040f144050050200c4a040503000e500b2955442d002190710b481404007820300003a0103400c41105941d01d0311100700061701540134404a41e01441c3c1c0244d00b0004525010044210fa080103204038104495903540b14156103c55080a0103088114550380d104d02521081b01580c0000c0e920a040e2132341003d6007081540c40340d1502480c21264038000e40c8441e0040510500644a1500c0360480740c405c01140e0b244620040d803002e401082840b1010070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 806066501 1250 806065251 806065259
    0xb1c111e03040822090f0903021b0f04022701030b01020604061a040f0c090605030601091a070503190e0a031a090f10020703030b0612280518100c050a1107050603090309010801 77
    0x1046507603651f80200542d01c02c0d54101d50f04038149040e284810b030000e002001110103030001c40e05a070848000702850344410320000e0000003a01401c13110552081c681081403d8032040002c2d030f100c0c0c0142014200b2503071a52210541c04400210f00c00c000d202400c1403152219060011f0000e0154442c2400019488000800d2aa104000300c0b4040d03c3d05940c0d814100d414030300300300e80600c2c4840880130090b0003044128005003052000e02542c2468800c144006c103030240c030141c00c00490100c0c00d071042c8079002003440042c214080c60003401144080d02c52040d6a5860210f00d09840007118000c01d1058540003020580740d5002420028866901400200f4041c8244100c0d0302030b003c000d130012141d00001543d20710382480d80b2110040544014644041c5614441080b02c106a604640d43e03540070707103403c1d20b10104000d80e0610788040c1a041004881102009040b80901ca40000c100140c00d044071144ca40100001405080020850765072401c01101150b42c4e80d000e100c081c0c0c080360903040002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 806067751 1250 806066501 806066531
    0x20d0504151b0e010f0306050301090c0503150108060a0e0a0212010204150306030507060305091e160501020a02030c0f0d051005010609060c1109100b1c111e0304082209 74
    0x2192540c8804203d0745a5000540341010240c4c4d070031040585c3c90000083c1940c09014440b8200c1c000d00d2205683c0d410201410708192016082a8046400342d004004ac034200083d09a4003c58485000030116018803000c0e0400040000c041d610144024125803e031906600038011640031300d01c0080ca621120100b68166040e0344406802da401240d400c10449009401196011840c0400d40e6604e01000c602c520201d9a0515401c1d9145e1108102c0e6002e82601600c0f000038080034001041380c0161a07000a69401c003402c00e06010b1403546210024940b02c488503030a1241d4864151071160300d003450300f034000300800d20924002410b84040040c00b24000d04401840031303080f0700600c3c0b5010040d818406242030152040c005141c1e090310018001c140f0f080601902c220711641c0c2c00358038624001482c280d40b480003044440807401c11447c0054020230404180c880848860741e603c1ea515814029003d000f14241000c01c456811803402e0004c1200440c402626800c00702005650a025074003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 806069001 1250 806067751 806067791
    0xb0609031005180109020f0405041e0303020909010504181410020a050d0507080115050a02030918150402181203090a06170708040c14150c15090a0201020c0904030201020d050415 78
    0x61f4016424448a1413141801d030041a03025000c0e00945203c203115000541e01003003011001d07070019a0200e100e8140d85040100311b4010241182d080c89000102c2c0c105540d03500103d08010302c2803c0d4030040840c0e00c00180402004400040811912003000c104041c0c41035000c2e10001074114503040000321580d02981c0d10324144e8885030350058402c403e0b82c80c01c2e2255132154030100150300c000d0182544a40d40c010700303594031070700c2090071250f41d00304951004e0403400150290b9109a0041c82060303080c2295210101000d0f404880d4840901e0083c00c0030b90031740c42004511a0031500924011482d5500103441206807003c099001d04d80b990307200002c40d0701120580b070080070040304034010071a0f2041c42c0313040c1c1070503040206030440c03045100c0b070341c5201035200046030032140d00280810702d4541c40c618006640a8480c5020704001e5609500003900c4400c41c80206106d140001301240c107061003581680c07013038000e501040180c1e04060612100c0b0300030840180d212141000321303c03d2400014110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 806070251 1250 806069001 806069003
    0x221040f120503091324080f070321170108030a140a08060d0812011806080106050603010608130c032609090c03060d170706060e15040b0609031005180109 68
    0x14600300480c400800c015070300c0b8405c09241c40e035124403210079130010000c0020b110042d08030041601500d400c107514100400c205400300140c00c024170820100c1c0d40c005a4103492000d40c251414208d00c245800d03a15200010701140e90006504004514003800100400e0105203d844081230880b02a40e05447c40c4602c8401e040000c015001040d55801c0403894849410300c81d400e02d81c01e00442025050794891301743e0001c625120856030140800c607091041501400c0808024000942003d02140381c2c0c0c0f00612607030303080019010000b990008542d404000181d440015800060b590b82030400c3c1005441c4282a810b45108240b0005c514042045480c404805007200e0881d40e00c0d80500d01071500014080c070f8228500c4c03c02200011b042e4451034a80e00400065291150420b051110483e056504400e01c440484814022600c40007074821881e0340d81240c000c240e1080d0f960210300d41e8003600c41d86941510a04005035078030b280c02e4102a21130003900404800380104a4055030a8500300c001c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 806071501 1250 806070251 806070253
    0x316030204020304031704030e010315030c0b0a09081204140a120b090f0a0303140c040617040203030409050f0403080610091a070c0303050703080114010e01050a0221040f1205 77
    0x100820060401e40c01465100d402418070b0b013a60705031405c000c04038680456080300007a40042a501240d170301840358240ca07821f02c0900400485c02d658402d80400301c18068500350700804540ca40000344283c0701c8201428180040c0da40e4002d2800210036141c0113802841901040740800c02d0407403c003103840d28116070800d0342c1c4200d13203081505c4c2c94202c040c002d000c62055028040d81c000340b5040c00c2001d4500c070341c4070740d42c00a41c8000350541c8840b161409060109c200340c04100412203554010310f10043c0785900e2000c0b0950f51110b100103440d5110b5603000034480ca01300020400e0b070311103020b052489075000c2d4542080b1540d8240c100041c07d855404504041911003100b44078501b0381182081048034540034461801a140d121111080312580c021030000d18005002c008140c0d001482c1c3d401000440365150030080c0410028001c401c940480b03034100240400c0e01da081520030410442042d01082c0313030a200180942030101c042d130060240b06650440c400d0001485a000c1c05542c5510fa0080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 806072751 1250 806071501 806071543
    0xd0f1503020409030c170a0e040506030303040b1005090a05220c0b0702010c0c141503060d0809030a0c0f051c080d02030619060c1a0601090b0c011107080a030b03 71
    0x10742040010f09260900f40c0401900503801d50014000d004540350581800c0112610761500450081c4030740d005e80c3d2003900071410801442400d03100003041e65040742e80920b50004595a01091480020301c40e0703c20390784401440d0500101d0411580700d40d000303c000038a40660466945000c1c8408030409c18010711101000364200403004603040689801841407410005141032525100c0b4000e401d82c00c0250342009a01150702d0380e142c4242545850744043d8907403415440c22100050107000140e4001e401810300251400903aa0244000b6242c1540710b1500100b107a11518081c16900c0382e4040d584c0602200802401d101a0b4205102081903100d5013240c501400d45075030602942015001d203401104441c0402150a51340301c20b8400350110342e0343c0548031000350400700d040300e5840001103c03800c041c00034403001e640d114281c4800e030707580d0002c255610600041b8041c01846120418600318001103044000c00c0400c1c80101000442d6a030b0510180840b07900b015154000303038058109205080d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 806074001 1250 806072751 806072753
    0x1060c0308011a04050301060806060f19060804060209040c0806150f0415030b150a120905061f05100c06060902030919080702041e0c0206070e0d0c05060f0d0f1503 72
    0x2034103d003403800c0d00364034000d818030f9511030200742900c10540010384150016000c100c1c2505111100d210b80b40802c03140c0944400e11802044481000c030b00034081000300c0000003905100c542d404440d8013510280c1b042000c1549404000d02980054912a10540021200c2142211114161803110714051a002d00d09403504542d05468085000680141901d0b8045004d00b13503a6039107004500c1001e900700c242d0b18000842c0041a804000102005051800104001240b000104030780c1c0810621031010b1840e4140042d684c1180d1941e00465110f1400307034155003256404602c6688061250304140302c0281c40343c503100243d0004a404280941c82210340c51401401c00d40c1c5e1466190041035418a44040b5030040b90945414852460010303a140c032140d184031100344140f42c1258106e10180041d401c0017000101525503106840d0b2196500d003950030184035000c40c03240010880100b01c0d0750b54071031003480c1314416003056407840c4c060b40c58801d0342d0749460000d0080d0740b50325040326841c005c1d844c15 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 806075251 1250 806074001 806074019
    0x40605130b030724110f030403030801080d050a1e0c1202070504050907060c020d0f080f0c1c02030f0f1b0a0b100303020d052d04140414010911070605071701060c030801 74
    0x74617101c0041072281604038442000309200410203103000303035038401c0345604003061240b602030700c01e0340c0204015080191001d1103600c0142d10150340044422008815940d00040310011a46400601009010300030080391907000a1140e049500945061009546202c0542d48506282c8140700204084424800043c60f01c5040303a1b40c0d507841941884030803041c94450081c3c517040849940e400100c00502801012010080e410221000121010304100350f0b860094a81c000c201c07041040001c0401e04880e80e1064109075140070303214991a04001d2100989260741d1307084210250307250480c14021a481c421828002e0003a04c2c1c058005061640c0f207200100e03119403040340032a200a100000440b580400c12150041980a64011a48581c101201d8000001d45010407603c036521f442000c1416480c4004401e0440e0041c00e40000c90142c2c3c1510312145100310400208010f140101b000181a040340700b12171003c0c2c0513442c001060303032075081c283c801040c10080038000c00d107200010029804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 806076501 1250 806075251 806075267
    0x3060e01080a0308040318080d0801051f05090103110309060f1b0415030603060911010f0201060503060a0b030c061611060405030604110307050d03031b0509010c08030402040605130b030724 83
    0x110a140c00d40c410301c2d140f13047c6a241d40703407500161215000b40310b54005c3c00340d000a003103024201c100c3d541500100e44041d19014081c400c620b10003130000114405415030301a9203c01c14511100003243d64924107084507a840c0c40086913203a00c3c041d905004a45060103e0049100220b4001a4075107001d08101c0c0c1c980d190102c188001c0e0805071070741d4010000410030b002d8491082c1c49214142d10440c010320001d440021105442011613140090401141d600014001c1d00441d41d48070024421450b080030a0800641c0300d200f64010f00f00184103400b0000da5a2040ca609000707401d00105070700e41000704525446280f00e500c0c0d15902010200b0085101d003651108401c20003070864484c19660f40c0880c2c19400e075080c0660100c1c1e5100600130381040d404c1d1441d0b1040c905403030030134500f02603400080c0c00066010001741006001100040464450354440f4000d0130000741520489104512404081c0c81d146050a0090143e80c40004060341054062084e06c000454030b00c03410b485903601101c03641 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 806077751 1250 806076501 806076503
    0x11192702040f0b12070815060702060c0106060c1e0206030403051803060705090901120201050307080a0b041e0b09060108010506070804051507022826010c02030a03060e01080a030804 80
    0x5508020000e070300118184003000603c1221034007511814a030302010b0034154010000010b00c200c40303041200450981c0300210380c161044540a4980e4294004106c030b6000f1100041100d603e00240400c2e0342e50801c10400bc040d100346038582d90aa14403661000600644c00c0083d00540d061000c50002801200988502d03070600a4001d2007800b4500001d103810001ea807018041000001c05020303904120a165000d481f540d011712032040b0440d80000d206200045c0307a8401c2050300c1002ca03c1c00c2c0c4480d0001d2601c40d80c010400d2200c034580e5540d0440c080400c80c0d8190003203280628101441c01c014082c0303841010143c441c01d403540c3c13138041401105c1e8402d501c100c883c443c0400001c5041da44038090b10440302d40c18820591a03032002d2041c1f01001078004030f0f40e8036a0310802400200132442d6450001a1150034440001c0400341c1c4440000035403100c8a11240c0354240071882d10129800005404d650340d003a98180903490b91605010515003080c0185550364002040c0180802d0085581071380103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 806079001 1250 806077751 806077829
    0x90405011e0203011409090d030c05120709090c0806150a0210050a0e070b040b0703200a0b09060106140906070321020703020d050c1b03070f031119 65
    0x8140100c109003601007031030707810111280c1d02000501200c81100c5444000300300c1519101d803103003800d0340340c941c1e40e80341480c61808060310b40c01000c080620910560300f519092000c49482ca04250b04003402e585014001c94104915100c19405d1030362046034050300510025020503484002280325140f036030312401000055101d81001401246202d2058a10030b1510340000200d0394480300c581030034000b442d40160711404052100f407000045000464880d07562500303100002001c1a5800c45d004040c1100c840701c01c0c001d0020b50300500407514282440b88001b203041e1441c907070b01c51209560015200c07581c0c40c9201e500340320302151810642c000300102806410035a4241c07040980c0c000c0003410440c02242c200390041800d400301a01000100d00e000d00604105051040d510166a0b5400700c008150380702240012001105880a2020002500010000301d8400c0c0e00c90521048204003010058050031400c010700141707604085410042c1c41401c0e070010319642d409150f407035004104104c1c0c0b03506 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 806080251 1250 806079001 806079011
    0x815041703130512030106202e0b0909033114040f0e0a0f08040503120403060614010c0615030206030916080f0607120e031801031a06040909030c1b17010207050c09040501 75
    0x81c20700c68a1110000c0c00d042c044003c203205605022000d81cae0b40c84003080d000b10001800d1050b000c00100035900b80601c01c00e019140a680702c4070305000d6000d1a031804a99908403079020907180d40301c01309101c04a60946042c04060f036080c0300d140403a04032920510f856049040540c002400500a0b441c405000b2600306007001e0302c07100001d0600c4078544001d0b2517000001741c1041001031600402004080c4020800303410340360f60002826090444400034a89543d07200c8140f10b0340a0134090784091a0060926600c07031800b8501e460b81c0b0441440c01c270700d5005654100290307000e400202d0104400e0f14401600c0705803641c074005d40b07640d041d20300703030024240e111505561000400c0014000c1002c0d40d4000c04207411103500090101c810040d0546034003040d041c4540100e8550b079048504031554010000f4040c011410b0841c1d850038603a0740200314113554524a1894a5503481c1d04064800100c6810300300d20650200c64200d00c204100144035130410308640449190400c003040c0c1c01409000080380b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 806081501 1250 806080251 806080273
    0x30c1d0a0b0f1209030703080106030c0c060e031c0b0a090e1b032e2403031b140102040e0108060906010e041406090f06070306081504170313051203010620 68
    0x1010703c0886040046500101d0f0000616a1203840240101420f0804211030314142c44020000700b00c0705d102a02140e20340542c1d15002d103040080b10300101c03071000c07142c442c80c0c8241c0d10350b0094446152074510034200f0820100f42c0c0d1110f0310950741a400042d00a04003002d4000c7d100480c43c3c8900318050f03240c02160184558039040d411001100f00c0c044440040d401e00b07403803030603044075901034510b10350b07a490407108900707001d40500440982c5c0d0541495000c0302e540352040c03e994824200300410b080d24810440040c1c0b001500a00162820140c0340c89850782c0f0780c040c0b96502c04049408551507400700380104041c84c0710624640d00a4002d880c6451515400d00d03c80380713842ca060b03951050b10f03031007010301c0044c8840a001c810381103000c510303043c04050301d002d440d2550b17144194005410340d0700e03000105007040200c5541c81840c146801100c3e860785000c03285500070f07503180309065540d4050b0742d01461050242c24102c2c0c3c142c60503500c9540b590080d00c0d42190340c0030381d9503035400d000d442402c0000c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 806082751 1250 806081501 806081527
    0x60b03010213120b1e04031d0604060c05070e0402011409040f0908030a061e0339030501060f0302090f0910021303020102071d0f09070510030c1d0a0b0f 67
    0x150203010b414028854001851800301d0601c113000307140103a107a005055801c806816900401d0700541c0601d807444418a070300c4d01179400b00354504101507000700b00086c00220b068001c001303101050b0084040d84d40c0d42e030b620008855a0042164001c2c0046d404841002c43d0215410103440040f07030123400024520381001e4880105c414200058070030000210400040d50620b0240802801401001400c04c181c45040c9015080c1c260000030701c1300749041500b031040d020f03404101075280c1c040708480311000c6a40d142d600e564070741400181c0305035003441808200c1011851814017100d9014102e004a561650b8080400d544080d1544455000d032000d040d04500d60750010300814011103541123a203e00e9840060311301659540907684030407800c454200030120000d08541e110383c00c008101070b01d82c0c400a0050034841c0e550001c640c81000c010400241d41d030f155000d1000d5a469403a04009030303026007800c04a031184031210342d03400420070300d050041c0d4004001a00c10a00c12512240c01c0c100240319070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 806084001 1250 806082751 806082787
    0x31051f0513020c0316110406050105090105070f02060f070318030f0b04030c020a0b0904230115021213090b1806130608420c1b0f010c031116060b030102 67
    0xa038101d00c2c5117085070818464581d0181e00d40041c11a4204411854100042e0a82c0590880181400808551801032002845090064035801021180d442a0000f0f1000742908601401c1c1d00003203102c3c8040c05862107828101050341d8200108140d030b010f4550384c118101800901c200c0c00c0008140d0005c0050300c0d03118810014051000700280c5904044043c08216408840c1510003801c00e00526414090038143d4503054440303200d001c5400901d11780050f458040c22840e4642c40d40000100907041c03100c05d40c410800c2c1e50910106001915403d4200b188a001c000250503007034108101081503442d201b11206406a1190408501141e641d6802404d04101c0e1401032880a80c904403030a0042c0084c0c041c451104d08091a07400c02800380303404d070302442c2d801800c0600c1210700040d4602c03034140c6015902500c035407503001c940031800c00f00503540c060503502c442c40c00032904000e91740d10f40040360310684020b980500103260315490310b40ca8280103040c61007103a9401d95420004844003090301461 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 806085251 1250 806084001 806084017
    0x4050c0c060901060306050709060c14150903040e010b090603191d010e0c0406030c06050702010c29061f120f06060f1103030106081531051f0513020c03 67
    0x64a50305e141082c070141c03200100303494204011100e090007010780050440241c56000103d0030611001c80b0f0201d407409052a6942089102020030804e00e00d40001c0140f00384e48030120540c0a42e640c0c4c046080320390041190080d07110740180001003542e00281c600b40d1145e610000040b40240c20f0781c0e00300843d2a0807500d40b22803a511042d20040240e01040382008680d002d507000c0100d10720b59110464865002e01940040000004140c000c1da0703c6045035005540c0c0200c01024480c1d03145110780c0c1c4c03800148a080c4031081c0c0400025116113030110256806c1150b055120308400c6241104440038508021905001699070000c040541807600c140005402c1c651525400241000b40280000065078202c22170f5034810001072004507402250395070401d00d4040a10550216940064078443c5040b4402c008840d03207410503040f40c0807100a5a60815050ba07081100791104c0c0800004526a0302240160082c0b00000b00158108a03a440d0720100526600500b001e084c42d0300d4600795800204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 806086501 1250 806085251 806085253
    0x501080c25081605011b05040b0f090628020606091617010306060608150d0602030c16080a0e03030c12160605010b0307030b09070c0206030901020c120a020705030f060604050c0c0609 80
    0xe445081244c01d00c030f0014405900c4005201540c81c581c0c0080c910b20460003a52022040401c69000e83c3c0c02d840c0907600810b000501c950344a03007032650284400e403c00d09a030800c0c408400f11513a17a4500200d0642c1c01110094050764055448030042c0010b1111800803404204102405002c8ac150306c140460107140b15400220740749140000040403100007400c401e241580802c0382541d03603075540d912070302600d5001401603100d81d5860051034040c080c15001181104400a018040115000040c00d08410075210b0f80c440c0c50042080c9a56409042d94070134055104000c9008010080000b038103842c000100a044e12035010340d22441a00d20130f03400300e11907881c08014040d1251b0540a22600403000392020b050516046100030485041004081e00410000001c912400b00a4046603201c030210011a0a21600c0300840d01c0b480d40500c0700c500041c09409400314070703803801013821505050410004c145e00e85903241000f0003801c0c054103200e00c002081110000c2c2c1c20092240c107114200c004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 806087751 1250 806086501 806086537
    0x70305011b0905060307170a06120b0601030f0209030c12010e0d08040b0f0403020309010804060204091422150b04151707060203040807120f1703010305070501080c2508 74
    0xd00281c00c5040030340200d84503080c24410000c4286e840000e000340f00b0751f038120a54881d104c52903030304010520398001e595484002c0c1101c2c000d01c5040500a80900001c3e81c00300300c503d050308010f034128000d1001035076040d000040c1c0f5907518980140c01d0342808040100002e00d800c0221031261070100340400307400c003280308032040005102040c00701d103620080070f1132031603c1c43c41c060350020340700d12130300034524140324107540400c06202c156810307500034050740361013001030081c4006001200d002c21100c45041c0740303c80804c010001c451001c50207c07103601030b1080101030110100c0e14040c1098120054000d1354410a0040c0e1034107080c00c04000700110310140811004010400b42070144a0700814150b500400c01040341c04000600ca001701c1ea119510401c4825840c9007041cbe11400341200a824000c80c004581404050340d00154100c910503400c85d52802d075038200542d0501030031152039580038018014000018242c81c1c8012000945500040c08401c460b074407196035410113201851046002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 806089001 1250 806087751 806087801
    0x1e1303120f0201050c0d09050a0506070905040f092d201c020f01050d14010608012402370506191a060a0203040806090c18040308010509070207030501 66
    0x91040c8108950b44024092460004501c080f94806c0c02820302c0c90340d0307450704184140a03091040001d0707564090700307854981c10f14000c020003188007400707541d1003a40350401c480070b000f00d46e200e031070308041d0304c1501d0420909c0c0b96017513040842c0c18281c2d40028201501d10b080005140a40b1031521030301c0c4058440c801c41040c2003480000514000c62000b01c60650400d640545d6455040c2c190140003441e00276640d40b80c4240e0013001c2d1010007000500d41803a88004250542c000c245141a140f4440036800107403041c100785988084d81d5449500581c2008465a000d040800680d8107031481c000310081407100d6074041c0c0c4184030065401924150020000c1c407046442640c101d26030340c1d201000510070030f02600c103d9168481c0b0002d02620544001461401403402801030720024043c000640f840742c078001007425161056400788a10a69110090301c507203c0603203810501454040c0d41d080303116800d1005201102e48003a16280130f5216030200000054024051051404150f4504004100c01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 806090251 1250 806089001 806089007
    0x304090c050a202107050703060603020108091203010e070c0b0405070533030619170106090615030c0239030606090a0203040f0f03051b0303010b1e130312 68
    0x110580c01610b003e02601864110300041c001d11030307a43e10181d603240d8603103101c80030200344140b42000b409409017940010900100341d0000040324001e03245ca80303e90b541c002d03403561140c0103c1c0a02c01da44d0024001448078801c4151001da2003c00d80c100301001c555640c41e040341c000b078115400c0f074581c5e0002c0814492820109a03c0d0f1140742c0b0700c403403244010f00425401000c4580c5841407180d94002000140140d540e10340c43ca24644603034500d400c40152079900144004a940d2202c641039030800000046600142c843c01c0b0446810020000549944d41e208901501c820180482140b14403500e805004010074040c0c08030400e10350303185a030b85c08001c141c080055208114140310380c00841c10821540c450a500075403001224100681d690380f50325080e40403816042018150905170a2a003007010b401c00f0040142c2d11904508411004e0300c954100e03500c1c07009000d000714000081c00015105000304e05410140441c2544041c105800481249074440042c0d1050f83c0c504002e5100c41403c40d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 806091501 1250 806090251 806090267
    0x303070201110f0f0306040603080703020d030b06090f0904020a170a0c080106031e05030705010207030e0414060f042711010807020304030209010b070203100c02010515061207110304090c050a 84
    0x160101c03000e00742100c3c00400792450168201135541d5000000003da0141e95980c00b03900510340c8070480a84034403175403c0080d552031249188101180c5007104240152903c041034541c4c0d108001c185101c4040300100340644940058800c98001c401c0c801c002c2580805c0e50340c6603c44028040003800c0c2c600035400c041c07040e03d856500690b4140d01d044014004100301c2c01414a0303d040d0f1294511500b44a46030480c610320810201038a40d51012415504065018582c1c9a4007402100c0c00c1c002e01041d0484501052400e0792495070043c590440c0343c6c041d040c82d8100c0c00c600c40090805500070741001c948144c0100b4558000c407000da20000c0000c0007988c1101946400c901c19200030b60a050842d4042002ea0106002e81018110302151180455508100010b26605820010300c419441c040020b40600000d540b291460210301107000c100b4105081510f10281c1925005901034480d400d050ba0400319400740107080d0b0004000104012549029401d0310040980d03130390f651802403110003841f402c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 806092751 1250 806091501 806091521
    0x306020a0e130b1c08030601050715150311041b0e01020a02040603140105090303070f140415080a0507020f0309090a15031217011d0a1d011b0810090b0a12050303070201 74
    0x204062004401084150781031b030782e00482c203082450f507031421420038641c03c5027602001081a818440c540c6c400e90b00c0754030508100c81c465440d01c5241c0e0a11000c01042c0c4507000108034500220304125207240d4410a250601d061042c016101500c80c40c0c0c0201d010307100c4940003540d40709080596500f0803502440340320741c000c00740c1e4065810341c108080010042216841004200900038100714200065402103d004140b0460036550f5407090040c081c051500403110303c0e281e2403824002500d07650000ca00820046540340241d840e0000d28000c005c0c0709200a0038001c0714a0703441d110404507041102501000c0c42c00b0395401c07410044044001807072429022900c00303481d0200c400400010482c0740038450074440500318044d440d65041752400c000d10b1001c600006450034120200f25000043d0301c030103c0003500d60841107104205100c103a8500000399030008600c040d5005c100064036540d0303c138031070502d070040400010380d07134507100c0403520241c4510556142c0c0002090107a415024841d08801c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 806094001 1250 806092751 806092789
    0x50721030527120f1e060f0603070e2505040b120c0409060b070b070f0c0303091a07090e0105030a1a0406090f08091e1e13020d200301030203070306020a0e130b 70
    0x5800c0c004545c40d01c1d0400a02120f54205544010850a80d810300c9070001624001c1095000381c0342200c0c02c89442001505581d0021302c0010300c882c40c9600c03420442d020384c0d00c1414014a40140c0600350340b6944c00c01850319030360103800e11022402d0503160084a0003440382480641e101c0395281080341102001404a00511500d100034601c9a83c1000150040300d816040004e4500d4840c00c00154210242150140b20710f403000c2004030207a0001c410070709591244400500036a200c40c00e1503a1107150440191a000d01c00b500d0440c0880c0c0d070007603258041d2003000301281c0100642d454100704034070f202046590003000300300f11881f42800318011030721400b44d000b0109081c0744100810001c1480c2840c1c0c1c951111032175903410164459505000360003154034011560781492440d00c0004010110780781240031481c1100004280403201564145c075002400303400f0403455591031600940c00f2040c44030034071540032024591550785203a1210328041b51800450310250800400411846880c030200f14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 806095251 1250 806094001 806094043
    0x60f061f0807030e01020c0610062a02061b030d14070201050f041e020a030f1b031208100506031303030f140a1508030304050721030527120f 62
    0x103298424003581d00240d403810000b44000c2c0341214280688034170310384203290f0701c1002c09210300382402110000460340c040d581c0440c50449580703031540744012924102054072600c402c0305d0141c50b044008002030884424080c43e0225660700a504640252440a905076a601886a4519003600343c150b401000c900c0200030902c1c1c402c03400ca074055405840034103405481c0400e120b410501401800c0215001001001c0c0c0c566640350601c0d007204a408225142100302030445480d100c0421a401941c1e03000d00b0310310071030002c000d044688680040c010114544034100000341c07078132414021809040944104c1c51b9208860030040c054440000c480d0310717203d280c40d1108850303e110000513a041010b0110114107101c0402c41c2c610041843d800007955800000140800c100380064180120340c20482454050340c0010700380302410040d4031010740070031010440310030b0003da0501c405a1040d0882190840140e0002c0425020703c101691325410f940f095a55a2400b1001c10048801640504803241c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 806096501 1250 806095251 806095309
    0x13020109050108010501080a1a131508150c070c260f061b18091311060a09030803190606020304081b0d1203021210050f03010e06061908060f06 63
    0x1f030034038000e02140c9419a140400500e81c807070549030b0050b03907100400c901e4280c00e844503080020a603500c010024840b252100040c080804204c0c9084c0703114071600a4201d41c1d40181114650b402028201c907049003007070002ca1950414403800722200201e0b0940480c00c8200c2520a1600008c5070140c01c3c0c0b6400001007201480c9130400b810ba9400503009141d840b900b4828007d685103020030303101365000020034200441410b41c0792891000078010a400841010390b04180021480b40b21003001c0029051307075041c400b0401440045030400c07411561021100100c14040307040ba0266004170005070400601048081c10800c40024058218400b9142207000c40d00081c00902c6a517100404200d5040c40302d61005d400b03981075810b04070800c0d101e0300d482c1c13401e04003005181209001e841d200d841c00460100041c101403103805d403c24102e500801d22511143c04210f1002c51010724a03000040c0b054021a9601007800307010b000301300841061030581004000c0060600c10514070084a406a603074841c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 806097751 1250 806096501 806096507
    0x6031303020712081b07180908071205190e060706270b070207050108150f031005090d121b0305091204081507050a090603020d0e0318030f01020405150d020c0613020109050108010501 80
    0x400fa8011f400000d0114400c0c6045096805044400340c6501c0009041d400c07240d81000083c030b507022541103100141401664166010042041007640290042c0000070000b0170a82c444010b104c4c40f8400c0074541e00d60184e056001100504007100c00e502a0014030a909404000a07070250100f42420f444c0c1c0d284c60b200400011174032203109482850303480c464152544003445580600b0b0030120041c0b1a515100070072641c0c401c840300402c800208805024221406944a0001c410600078258605042515412030160401621501a50064401c08000391000340020001409960054800201c0640000055440080081c418030a0400c40300e084198001c0300c2c54156480c1c2d04005868183c05a030040003041c43d10008132003072000003210a4070f41001c0c41c080c1d06e101c0d4110704440c100b110800c034180c05c0c0c0c0103512031540c06c07191258201881000c0e00025100384039092400504010701c1070846841e0030000d44183c03440b507400401034400d40d40c0c00002c060190000703081010655142000003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 806099001 1250 806097751 806097779
    0x50f070302030606100e0a030303020c060a02030103030c02040507030b0612010f080705030d052d0705160506040902071e030f0e062107091a0d06090b06031303020712081b07 76
    0x148240700c00e010b00007010b401b450104c05007003409810410304d10703101d183c0940250b000a200d14014420b42e070005007159400c0c02180c0c141c030790566901115480c03642c240320241201401040905444a2965a41b40c030b4510140c14002100300c400c80d415450115907002180c230b00c3d0810052034000321403d0000391000160200c8013441c0b498069074170481003003540501d0110402060b001c000052912564894050143c034415020f002541c07140b00c120500780010041911802d5004030040c0410171111286602030002103001d200b0200301c03500780480e00010400c030302c4421400325030030b156502c15040c0d102c41c521050040541e455441c000f070110202107251400038501c0050200440001c410a00c41c128400080005448015004007182406a82707500111187c04000b840d0170700c0042e0740021750185801400c0702504d45c0c0d140d81c407401108400303443c00590540c00c3d807180c03c000203020814820842003607400346030300d0f9488400d80e8015075200e43d00c05140b182c05501045051080c1c0404540e9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 806100251 1250 806099001 806099011
    0x50409050a0e0c191a0322050c01110a021201140f041e02010c0609051c0c0b070e1f03200c070b0913020f041505070803012106020a0c050f0703020306 66
    0x311032841c0003041102070800400313800c0740c1041017489665042401c070120142d8018442c619641c210225200c0b142020f800f00c40782c0c0600943d0040d12002c0242d4001e14000000921000c00d80d0303104039168010600000082405680c10385d59072445c03103190300b121702e101e039085256070400c10a01c2c00c10303840e003410041032100307809000f2003040000c504681c00303410036082c419030120060240301070f142003082d26005080b20344c0384031350415405916120b04c90000d4644030784c2d00c81003607007080e240c5000446c1c1a03508580d40e1604031a000d0742c1c0320490412075200e07001c01c3c00a540c010643c030000a0402c3c1008502d00d000c1040309100303102e448014000800e100702513403042c2400744d48850413140041d4100111621008190b0310010b840407180059500a00035101400781b04405410804000c95107445100c0c4c001c2d01001082c0012720002c0105075120301d441c440410b0040d42c0340780d241c503080700701c0c2d0203c0300100100e04c3c80c090310f0303003044824004502da910001028095403031850b0003017912041c00400c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 806101501 1250 806100251 806100259
    0xb0601050f030406050a020909090109120c200607151b0507121d100801050906060304050d031a09011202011d030307030c02060408070602060a0f05060105090609031c050409050a0e0c 80
    0x60090710403135050715400000100b80004509040ac200c60082c58804000e50303800900c1c206541c0660b00800041d0710f440da00c120b01070060892200c803510b040b0070320b0f00010342c0800104007030804140d40e49560981c40e4491200000c2d03014240b424503054203564910001406000e200388800b04038041240484034405040c24444030000c0e840003d50200d81d44440c0d544028451b017051130090b030206003241a50829111030815807144010040c0c5c81c0000c90b03004046502c84c00070100110302c00c6d0000d0621703903240768148420380302c0c04c1c0c0050740300c1e8000d07001a00000c1040d480d0f01d0a6680c044080c6407500141d408030341100d80c12401085c0c40e40315244000d014094518558011520360a040350000d09001080d10142a141e14000391168000d03140c1920540c103106200c0d0258a1510400d8003842e01612203916010b0050144400c540140708002e40c14002c2040344015041101c04035106446503a41c0e42d582c40e030902c84440126203010703019101140c074005c80d80f00c601000042041b69440116 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 806102751 1250 806101501 806101511
    0x721060b04060905151201090803070c050708030403060b0415051f110a081c0e0601050906010c0b07050307020d05072d320c01080c0f090d08070b0601050f030406 71
    0x201003800307006690b012103180c0c2e14010400481c645c07482400400310100f190043e100c0400c0b00516800e07140d0b4558050100c40040000ca1f440718092180349011078071650581d1310155481e01900d05641196106980f141e131601c15014513840c00303114022144c9180e5542140507420300d004210a0001d1195201c040b2807640c0b0350358505030050796203640002900046a000c41e5861500103004d400c480b03140800c1c07480d9980211000031007800b030f61140000342001480503130319040c104a448034002c0d0140307050207485032040d130120341050501446441c00d41c45099481c1840c51000303103400d20101005040140500101000030400c1c40000f182070074a0601300307440c45640000c0c00c6510044c010040074079a841c18101d9108502d06540c4031680048500d4481c0700501d0704c0041d0715098058002400030b60824000b41d10340140201a145910107485100d081100725004141030207038610082d2880c04000c80d40a0030084070043c030907840707002843d16900300840302014007102d010140004004235124 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 806104001 1250 806102751 806102771
    0x5150a110c21040503011b08060a0b070b04080c0604031107061701090b04021c0f0f02030705192c03070b044205090405060103020906181c0b09072106 66
    0x50410750f00a40300c010000c200c3e5110300e110365001c0d88a00701102c0b0108200c0c80000d00245800c84640044405079484c0078603001c0c003980c503038418040040c011a0580020700107031081150802109104034440e4485029098181c00380c107107400d01c41d5202000300140c4080c100c10514001d80c51238110b440007900440e40e400c80900280180c0070300c518501508080a100310b44c030001540250b90905400da10401005841d050508203030702c41120380c1e0380400c0702001502100c0f02103000c1c0380d84c043c181e86002440c4403044039007460031500e40601300207000e6409040280600e02440307218000c0c12044400c6280505d07000140c140c03102044c01142c0640420051141829680e0a0800d14849066260105400040303005009500402c004a00a07807030440091680c0d402031080302c4240c02c00034801c90402411242c10862a8120041c0c19003200503c9010300b0140008a28101200e126001c61486881c2403a90b040c0740660070b50007154941e001c00c0e00f0042c4000444d5048003680d0b0048404a10341001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 806105251 1250 806104001 806104063
    0x108090a05030f0d0b01050a05070b1f090b120a2312030a0203011805101202062503110a02060a080901140403030e0d1404120f05150a110c 61
    0xc800028000d4000000c90340455102d0b10010034000b410740d441040725842442c0115600c3c0101c5403448003140080040c1400300380d803080c0e61540840d0504403501008800300d85038410868660200580d20313210440b42c103d600d064002ea0321070440c00c100404961800d03482d00c1c852540c0c0c0c1500300c1c000c2c103c50790320048080000e1203540f100d003103d403c14a1780ca05110200070001d500910640b9001090484001a00b1801d4040d1a00681c0c980d0031318080942403120040c00c0303000045040346d21650410600c1c6808032594150b0559070011580300001207218107001e810031514003040c0069800c000030b07100042e581c100645e100c843c01480e24251544c0c9142216005010300444400c2c8501070800b000304145c3d0540007984a207004005a4615140003002942c00300900500c102001c00188400e06c21880030418807240780d4094400c80e0682e0419480d000e042c103400c04142070000d6440c004221805405014504041c1012035003d132034402c01b42c013400d8840d0300700309500144128040c60400e01d000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 806106501 1250 806105251 806105263
    0x40611070c030b0106120218010f0513121e030c120c0b13200904060209060906072d110d05010605100206040b10050109030f0609060f0e0c1509010809 66
    0x5442803103001c0c41a00c03402c1c4210440c800744100300000d111482449075156080c000d03074440940d2111407d81a0004100541d907428451240e507040001c1404070340c84070225040c056008145c0885080c2c1e10b00341034141200c1e100d02140508102c12012040800001c0d48500c10f41d0155810148940f0612030b030000c100c400c290f0b00c010141141000e1814040d903039011520820350103100b04480a403580d03450100c0303000841e020080960260b120400640420036540040c05400f10003800c0600c0c24014030005030054200e82070588010300700d6000d229200c648055454001008040a074122034510b540d16502914584019405091030100c840100102500080041d01c00289180076a15940a000750754060840d010ba41c10002003011501c1202418124800d0340c030107079280c440560460b00e840c50414142801120055914000400455450722950011a086030804501654542d12041c5000c81c880b10644c8150040a5010519404081101e0300b45e1001e00701005030395508803a030380c02c0032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 806107751 1250 806106501 806106503
    0x1e030105071b03030f1104080625020c0906040905060115020d0305220c090e010b010801050d0203060403051c020703090504140f06100302040b070803061810090b060c0d1d060309030304061107 84
    0x494081130106c3d0090001c01e04034441c0e20107400c0d40d0ac948030410401e0703a981943c0030f81c04016800101c010a00c1d803d240c50010341c401405000411042d01d01d5581030b1404100340d008180200004503441d5100340c0c10703c0b0081500709203241c00d00c900e00300760401c40c0000010723540080c0c00c00c5000f0214020030a8981034100244007400080100416401d1a81d000c0e00d00b0825090000f21203500210381c502d012800203d03620b40150040507141d1791070350151075552000b41c084407442503410a003070420783c140c001866401c1c0702e640d0300d00915261205000135601c8401510b4400008282000803880c204100703240d200e48100d03408540f080010303200313400a201300d4002c0c4c0c0d01040002003c0c0103100c02480218000c01c01074426540b1156610076804c544030301038ac0e500310840640b01c4100000c841c4c0f504481c1080070003d101c03905d44080d42508914100090025001007501c0d80c4c03c03e281032520303c111115103801510454518904290007945a2100a00c010702031541c6100414902e1584810360701c0c12 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 806109001 1250 806107751 806107781
    0x4020d02030a0501051515030105062503020304030b0121170906030a2403030806040b1f120f060f1a07150501050f01050f0703110c1e030105071b03030f 67
    0x9600d0b074140700b8060942182c6010940d9002c559420b00d0f1b0810940e007a03a03129820015504590900d010440c0c00d91200340c0c0111309840c01851003891032042149070364101e20a400540d62a8950302e010507010205920a106403206406016404a0300b42800b0f00310941c4810406010383da00002b207081805240719490700a10f003c000c208119246074410a02c5400c422000103080c072505080d43e65a100c00e00005000503501f6000c00d1890410340c02041380008010320f20640354442da030f08400052b00003e400030000d42904d9071612407400360710454004516140d41030003007a0030306c407144001e42e90902c1200b05500c1008054000089001d007075078200c82e4020071a0b40c182c0f4650001202400d800e020310fa124005440002000390301072400c5a80710110055104c0c02c107507440e00c090320911040d0070300c0300d800c1c06008103c694603035131250002000000080c07596800904681030508650009105805218140d6094000303220303c80011940c06606180100f00040402094000307000310840ba4010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 806110251 1250 806109001 806109013
    0x19080408070b0403260406080a110a120e0d020703080310090203130507050f091f030b0702250b070b0c0f0403030e011d06030106121404050115080703150504020d0203 73
    0x4101d00c242c02803003101c2c0104100400d0020a070f1841065040742d4011400e43c65080000700540c60140c542235070701c9404100000340012001a401103564000c40300d281c0010714001528071010443e2090034044080f40c402440605500540039540d400c0350b010280200b080840050440c292034240d0700080c1003100c00654907810040c001c0442c244101030704403501e002c0d042001c40c0d81c1c101142d02c41000b07403000f018050f1544803070751a141019a4407180c43c81c850b00000020020804611159000711810303130040c03035031000c2c041c400d018104c0c068004220881c084c803c100301d08001c1c1d03426a182c06800c1840e00115848007010081c080c03080000140c801500440d00006040d0441e0040c0704104080c0c0301e01c12a50050040019840161541e03142d000d102440103100317051180022000c5603a440c1d90000300000e241c034003420600f1341181e04640581d1a42d40b0b507202003c0700e50240f40101180c000130030f200c03402c5a569080000900c400f000c16150307204006800e45d036070b00041c461000d4020b01030f00d103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 806111501 1250 806110251 806110259
    0x2a0606150c1905070905070f1d1008091e06040308060a0806070936020904060f090501090e0a031205042103150b091c2f03010506060304051908040807 66
    0x24580c2c81c1c0070800e8445008070b031800200014940500341c4548041da4030081c1c0407103c10005d49007691030781c0c1d402c02494455040c03e1003540329040001e00060160302d40181501d49004554a0610001d80c0303204000c0f45806100c040c62030016016800950504103410583e45420200341816126401112103104085c2401a03d5401c680004160380307450301d00c4034030328602044400d202d00d2844140c800b9501c0d1035001c04c408940d1036010b0411a20014000b00b034242ea582900044c241e59038104505165a83c0e00410881406e03104004448100038040d259641d20342e01c003c2c15031a41001074000791501c1d00c0016080040d40c409403c1c00c0610803110450880c54400001c1c02412010500c1b0b45002c078103c4081207001c40101a035660500c014041728100114021840041800742000c41e04020031520902a0780c031600450011034410720542500480160101402c0d2807010300b216000344010004c1c080443c40200d40307501079800c2c403012052421602c0c90605514882c0e0350044180d070040c0c8101207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 806112751 1250 806111501 806111533
    0xb04080d0c090b0715020d0e03041509030312110702040c02030306090c0412031404120b040c0609050d030f0c02040e070e0a060602071e08010903052a0606150c 70
    0x140060034260800c21400c04003800c2e034a80d04240601100c400003071100d18000380d01da070455211188050800750900040c01103039004d40302c40200b818034075040850300788201e030000030904c901e0070114a4092003040c61034402030008450380b402c152800740c40303032a50304d0a485040d0803116240e034090410015159201c1d00203440741c0042c1ca080307103e10100000b14042d5800403081d80d0a84a0036401207414602954041d01c0c040ca00212019030450240800203108015031b080314412800f44408500f1840c1501d131200b450043c6400c01c80610807070721400e124a032a4034850240041c0d250920000500246000381c0e419540d0303000003035100b0309050b010021a030740851a00200c1e08241544541c0b500c9555120055840318050300c0f0059110010400c04200d120b11140303070b40b015504041c165a500d030140745003540c05640003500495000500c0d44500c0c0d45242c20400c0f601c20029411000c48036103080591100005004644100c600003101d075020548031086905041c5490210392000c1401d245070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 806114001 1250 806112751 806112757
    0x30c030c0503061303050306040b0f0a0305030a0807020f0c010516020915030f030f030f0601050f0d020910170105010e040608061003060507180315110a02100f0e07050d0f0b0408 78
    0x8207000f40140d00c08201d2203002e03080500b00e050f0b40b6464850440e9030b224180f2000340f40584210798050f038000550000ca407160305044010314000e01c09507175503030440340c0090111280501030600719401508284411480030402907001d90003441c0c51a56035220074540c9202903480b030710295108180d1001d1141100422080c040301800070b0b0305813030307100107900101a10b0380107074641410708460420001d4421001c0c1d1100580c0a0814117082e030510128a8000c2002c1e00040141200c00d6400100031125140c03000300300c20780d41c2141c50118240001c2d81c4000501403010700c00d0506009194109041c1c0381c4d242e40092019110780740c00c03035606141132840e00c140d0f01d50f24071080d90550301d080c0c04160f05c140714002c41d40d80da10b01c5400c1d03000d035030b459540c1d2344140a4110301d0005500f5a81c2c20710382820000c000050491500d503500074003030b1005645031442152014111501040e21b02942004044400300c0c0b0380c402c4034821102e541e603030031950528030b0700c81d05940c0c4020188110035040004100f42903000e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 806115107 1106 806114001 806114009
    0x15070c03120215060a1206050603120a030b04050609040b04030c170d0506010801092c030c0303090a0303050906220203010e01051503011b0504030f0606030c030c 71
    0x44552907801003000a0040e00302000203c162032140390402d8128008441011210345001065801019280001012251210b0020346c1e00c0d502408103c50560b00314a4991b95507008160042c01005a441c0991007949064085182d6007807406549205035480811901261a83d8600380c680302d843d69000c45a0303401081202403610354030405024951249000842d90b41045030015081c030905030050309242d49031020314404080000382010721070703240d200001c900036201a42142180306561300c4508030310001050080c2c40800142981c2024001c0d40c08100c0340d1903510249481e900e007911011360138044c004050204800208081070390b184010000034100d02805101400d4440444072000d900807000031000c0035040c28000c0c480c0120030300140030300d019041200589280503a000240c1101340c1c0c200c030301082020a0380600095500454580340865a03468241029811401 = true := by decide +kernel

theorem cover : BRFrame.Cov 805935251 806115107 := by
  have h0 := BRFrame.cov_init 805935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 805935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 805935251 ≤ n) (h2 : n < 806115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
