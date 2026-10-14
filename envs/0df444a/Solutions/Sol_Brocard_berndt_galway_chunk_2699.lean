-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2699
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:29:04.301169+00:00
-- url     : https://prove2.me/submissions/e1872abe-756e-4361-9e1c-c855a444cf95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 485251798 ≤ n < 485431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 485253048 1250 485251798 485251831
    0x170d05060d0809060c0c030609071409040b0117150c0304030f0c02130209040f06080109021305010308041208070b0108060907090207051e070b03040b250905060a12090f030305 77
    0x40c0d41d07908503000c2c03403c101c0c1c0fa241c4501614428901d0030700c2d194030b80c0c0d4050240c2030521425190008551054852142d01d408000d120003043c89a0130400325405007c10300a4001040b000e4810300c0c41889099100040c0c0300524541c0d5410b40c1c699005451003590b0b4140081040b050503805008044030f080c0c9031078140c10501d195000074a58000d130b8110b2804480d4000741c04001e40e40c0f540d20100c840e01c100700050260540d6500e03030703e000f4501e200090340218100c000085203001c00384a1030f416a948607034014146400c207401e400110201703030421100b07141c0411500340441c081010039402080110010000c51824500b81c1e07080207256407041000c01d0051101038000340e0003186500e6401c90b01c0103c049030810018081d440e014465000b02502c1c0800014002407103801040715200d10301c085a044164885044283c028035280040000082e8801310300307010030f181140007000c52050b0343c03600301551081d61207204100c9124210440b2842030381c200a20030190980100b96019000b00c4000700304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 485254298 1250 485253048 485253053
    0x31c050310050d111e090406090512040b041401030b060d060302011407050304090902060415032016020f0a0f0e01080606060306010c03080a020706050108030d060b0a0c060f09170d05060d 82
    0x1012055080740c0700e40d03986840750300e403240b8017400e901104500421650003404d0500304a0020301e5010800d0318240103078210700a00030309000448085690003410103180520300181d0a003043d690304c00080c10942c6640943c0c01517034400e800f0b07090300d401888002681601c0c510000d40301355403001d603e42c8040c03c103003c014081100441038401310b401c1c3d0350000c00c074000300d03200261042c440c0b90010111400300d210800e61450b030590001060124185244105500801d2180b50703502580b00715500c9061003290180c01814440c54a000b0114064030184060f42c1300d00c5030040400880d0050401016008010130144000700500e03500000c09070741107491820901e00003030010344442e1020f8180300042c4085440c0301041c0d4101d07800203400c11420842c070758440d03131081d80f0b0754440b015100100b070810b9000318004150004840054015465004202c8020f80e5141e010340701030140005115a03d41d080700c046025010341c40c000311810303200f031603650018070013000803540d02520641c060030003420301000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 485255548 1250 485254298 485254313
    0x10612081c0b0114070f080a05070515042d0c180f020301030816050307050a0b01080c041407030b010c050105010e01060809010b01053c040906080613060902031c050310050d 76
    0x64001e5101c18150ba51181760070880c02859a42d0320041c0303211400a10180070700e5000d009041000c1c498000d0b10501c1000318200400d10341e050b0750203003000800080d80740030300091800030f90410700020f200f00070309011a1108044a074555001041d030044a9050a6500340c2038802c110020007120703802c508550640c0c0340e40c2c0301409000c0303041200c01034003810f01003800820001c0da002190f10404480c6641c6080c40d103c88007070b4007071090510900c14620098240c0c501030041e41c50b2aa00045210080c2c1c0d1045000c4010344010840a41809511030b01500415000c0c0107071406000c819400361595490904020302d6000010f00582c0f01e45d250981c43d80e1640e80c80401c07510307442c40e0412003415a40251741c80a40d01c410005a041d0501c4030758848045081d80200900207c441100341003000540d2090307000d460b2102154140f0002000e098100b001401c10340c0301c02c080c24009002c450b65204ca0038040001c2c42c000300b05c050301050f004000c220142c40410008000780200742ca0110610085a03940308 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 485256798 1250 485255548 485255567
    0x1302041d01031109190204080a0b09010c0c0204050717010305010507020613030c261305120705031c17071e030c050304020f0301020d0207032a0503031305010612081c0b01 75
    0x6100f070307516901046184841742c9081c816455009400c56586030781780c1030300d5030341c00c3d0585044031542618400a0410441841004560422904c0c0c001c0507040035070801c40107002c02072600313060000c0800e46010704400b40041c1806144107800004060401c0b9101a1408c80d005001c042803038060051240020340c0081c00f4480b550740440c1442100b40900301c0010343d510f0300440202d0840b404980607411444000c0c1d18401c950081d1106032905950007002d9031100000e000341505a03001c2c800d00081d44904000c040c40c03c058070b2902a0010840392a034002c0da42040e40c5c07010010703098004204240d0308100d4491407416003030a04010101c0300a402400c24000144082d10541d40645425025282034040f69603190a0800455503100705181c054854007001c42103986400344d6100d20300415041000b5100f0603070308400190701f150340e071442c4c0f454201d050840c00c0700c0654840301c0014000c0c030b0548007296950300c83c51081d5103440c0156140c4241c403484441094040f42010111915643c120390080d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 485258048 1250 485256798 485256833
    0x70b07080d050702010902040212040b060604260109020a1d0901060f1203020a051006140d0308040807050a0506180d02010c1d0f03101506050406020c060c0c1302041d0103 75
    0x10407990360b0188281e00406d0301d0f0f400a5000741c0000340d1580507580c0004071521030f82c4500c58400464a644040c0002d60103240117580145101301010717044000005010002c10030580008100d00c941540440c01040056025075200450303d4081090107450880c89503108401e1002005510b160196804410382c40d48105d8040502c01d10103039040c0340c400e105101c0440d030401d00705c1e20900c08c02035605004000d20720550300300107681c070300100481c54680d800002c0d498142c0da541d96103813510b45030301c2100e0b4011081240d4502c030324000310000420910401e40314484000b848555029040c188a0800403042c010340210b9140560440410340c00000054115450150441e0a00c2404c40410a00c6810920156061107001d150301e140742565000032052074500c1c40700804032981c80e001543c01703000b50302883c0c0141e00800d10020780ca04040c0080c10b62034204208640c42c480d488030200300d0b8004032034120340e2078035000103061040e0000c22203403c420396541c070504007641d851510740001c2d00d01041c030345 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 485259298 1250 485258048 485258051
    0x70317040302151603110702030601050f01120e0c090c030603060f0a2301030501060f0e0a02031306091211070501200705090a02090103050703022506020c030a02030c070b07080d 78
    0x3090505100300103440c254865094400340c1400d0900c0c0c030307201040d403d20300c15002900b00409424410300c28070586001c268040e00400305a420b1100b00301c45101c58901040c10003551401d19641c4080501450351103c030620003a04010591388144112407400501e64070704e5107420014020301c0d440005190342e01008d1003405010fa0307294403110300041d01c68a0b0a406201d15a05078045240c00701d50038084c1200d22981c000c00c803095540142c28495220740c841e800c0580d42c5500010b0711607001e03400a544c030510261456400c00c40507911807040b90340081c01900d03419040031750300115541000b540c51a0316240b400405910340760000003409013134144030041c51502603000c649d40103031081160074082c0c4001814190a4034000103154000c1d0007080190b4002820300b00458503aa009100b10358281030316101139003900700c074101c10304d1403582d10800c00c840c0f9a5080201c0a0980f0051005e0919100c0341e6024541c4c9100d82c006003803905000740c00820000c20200403043c0040c1800702181c1c0c1c01030342e0080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 485260548 1250 485259298 485259301
    0x3050a0b041106070303060e10030b0c030a022514010204080705041a041b021501050901031b09240503030a08071b0503031321020c040207020f130501051005070317 72
    0x108646059842c030951504201d01141480c201501500b008041d140d060200c400c0e655605161081507071340e18800a402c1040746004600c400030140001c2d6401b17542c41102600d07016800c010302c2c3d2201d81e070510038150640f80310210340800c030482c0306680d90b4900507802541018207103c14143c46600a1003094030070ba945400300f9049421107022422007620090040020250800074844043e09420f0031900602905401c0f42c0d21982001d007150580d140580411800ea0960751440020064442c0d96203a40115410000d40e60f4500d010f010740d440500e813294060240c440000395107003405600014881e40052007404441988165415409001c61030a5203004090002d401074085d01a80c0290680c04000f042020340c06500114816007031140c039050301221346245003005200c1d0700a00b014010b800c90003e0392924909174004e40440c50009146121542e03000d40041c82c01107010f2070f90307450389403034a00400140c03801601e0108040501d080080c5402b20740d0740c00070000c52104408440d00340c005070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 485261798 1250 485260548 485260553
    0x21c0b010504090903350c190e030a140c1305060d11121227010207060f031103010305011401082e140a06050901050a03051507020f15010e070903050a0b04 68
    0x16080c450784020380c0c41013290a5071031b05901050b804034400d06242c15091400704102d8840881202c0101d9404642048003615000046400101210515605100c1c0c1020240842d0308074003480d000c1da81c0c02c002400503108001c148280c070f4445c10050303c000c500d03001c00c00c84152148041003501c1540a10103003084901e020004000500111007034203a07100c0d2100c07620aa03200f1400508019044198019010040d0051900c264508c81c0c0941e00680003070004001241c001c201d1841148a03904000c1a04150400014140d030000d03482134505070345612654046015000c0405d0141c411301d406403c00031400490121250306544032441d00400314992545011210340c00152a2121100d01441500740001020060001030040074440c1c2e01070000043d15240800c181d0301106d60100140c10141c000c80c83c000002c1c4401041c44056016080c100a0b80074410300c40c8005042141540a480b541040310b4174000d0705004040c54144550305c0b10a1001c07c00008400581a17840100081c0c69034451 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 485263048 1250 485261798 485261807
    0x30603051002071e0c0e060603041e050102160b010f0906060804031d06030a0b2b06150803030906012409290408101b0c170903060406021c0b010504090903 68
    0x4004184c0043c0c19403003d01c20081d20340300000c2220f504000d54882c0c1e45408040001ca0b1000743c078010421003095100d03840c03504005004071042405000018280045180b10b4449a0809041100d20000c0200180005048180d078807001d401003910400c40e15086c00800791180c44050005030174400350500446030310031114074407003c906001d03169580fa1b08105910b400070300f6140340000d00c10703001e0355038100d05407030030306080e804e00310282c0007100081e01d2030344900c00182050510404030581e1b509011540c1c2c0c2c810402580034204103070040c04550b00d06038501034040303040030441402003a1000266005903000e41c2ca81c050780c2544580c002c0c80da100c000130140c015a4040c4030041d4080c0400d0004940c0c074085081501940d55600902010402100c4000305a40c075291007000b24248103508030108008104000c0400c04010015152081e01c50000c2d24160b002c883c00c03100320340c000480027516854071844c8c4e41028500a400d011102303890780060114080e0b4056000c2d204c1e0f49007643d40526109 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 485264298 1250 485263048 485263073
    0x102070c0b0c0f010f02032410050c0a050105040f0b130803013006060609060c15150801480809070302060d090327050112091a0708060103060305100207 67
    0x200844401c04445c400079400445642d40c2241180d00145030030500800c110030600c2c40104040030120390304000742c03000d8002c1c280e80c11584c4910850403000034000d11405005a0027450403014009451400150658000302840c29001c4218a11000030f01d9103000c0c2c9043d6000081d01c0a0150718049056000c000e110880d554000c090b0f8601e64140b01c2940e1010041d220107239203140c01d10340c4941060701c4404480b480102600c164164040c041c61031079102421560403c950003032a140d40e08002825140340d40d110003150440c510070030411340d100c00d400c8440c1a8810030020301c16120b170200341260b21100741604080c012200c000464a080910041c0d02850740104a0764a9040c0c4026901c010503003100100c0100d21103402c00c3c114605a040720314034603000b400341003001c2130506004440001495001400c0d0b01c0d12009403400086150000042010303a0020310b084610b48078030b00919240b006022141032610b441c000384081800850560314000c017002016035038000d43d10f4840f405164 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 485265548 1250 485264298 485264323
    0x70e1303050d090b0402090a15090e1c110c010c0f0320030a12060b03040c0b07030905150d0515030307060b1f02060a0614011e0c080a0306090e0102070c0b0c 69
    0x540010b0030304004851300042d01640c02a6810040b55031040c414004441c81c0011046825042180c1004030340c6440c0c21001401d4954825207603410060304242511340802000c00e008503181500d074100d05d400401004480210920701484062015250851a007400b00d0020302080300f0412103182031000d01030300740c00030b1803120102c1340d45a080e000e004015190b03d500c1075040130305054000071013400b100f0607280110340000700f031180c0394075048c1c6041950780051003c80512072403400015007a640c0000c06400f2140c04041e1640c3c1d080e10840300030840c0d900510f824030680c0c0d45208410141c4000060361042c5a01410005002d02200c0015120382100c03040310b101d0812401145c1002907001c12518050080f085040c85904c0d00c681c5984c41070b00c9543c007024000703a040708501382c41c030901d14041f5400b00414105040507844c59158104d950f1b1040d054000401d4403088104901990f910a221440c40c28500031400e1481696610700c00c040300b0311500d41c146a02050500351582d040c00084507446 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 485266798 1250 485265548 485265551
    0x20912030a200a020a06230d060305060a0626030d090501060f0e060603070f0e1320090a0e063705041a0603130b01031a0108070e1303050d 61
    0x686090300144200700c21030040807244480c064004100301c0c0040ca000343c0c00c1c0d006040034141030030203000701e4001c52100d60180b90301e07602241000041180b14001c016021062601082e10341c118107126245c40d202408403070f002894030740100040c1001000500c0310040e950808105003600c8110035286004565000700c84501c0d0480100400074158041822182d04214a907801980c6480d98075400c0c0003200d00c290411002c00c0000d0b0390034414403210043c1065420000c000c02c0c40d00c0302141c4d90196080c1c03840241d0340e03521007042034512108a44402010340c10b2807079182c44072420228800c07130505c0c8640601c41112001040c1c07642c0da902c513074851504008090144400a00c80c00703d800e00250200c0c1461040d0204000c2502d00b400e001c0c809030094880711001c2c21a1030003040c070038594070042403100f0040c0914a5440001c40d071a400c98001c5010781c0c04100d0110041401031081e00c01a0f105402e9035008550401148001c0300364244e11044101d02a07400c0c046504007034407144a00001c1c6040103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 485268048 1250 485266798 485266807
    0x3020c0a05012903030406021b011b051e0a0c031202010908070c0303030605040c170403120e03120705070c060516140307030f0306060e13150f06030c0905090a02091203 74
    0x80640c59544030303860404038081c00240c485406045d01ca21540c0078a01c0181c010240202c0000545602a20706280600d44604040170500e60a18614241c2c84c00300d465811220840d0102186490222980001003000e00900ca10036610b490f0444000e210090110030541c01c1c3c1c5017598000c1d8000941903070454891959040b1502d4a1100300d9014002100400d181070030201c3d40b0f04081c841c100c60342c0d02e1901d54051800002c1c0200280c100c00a20171801c1020021204100d512a4010f181c1100d1061008603145c01c10f10a100012102c001c22010400005104400104e4001d509104c22a601418419903a02c140100c0580343e0380052006032403011845030000010200000510f0058003039500c800118082d0641101620150320600001618800260000c1d21300b0600540360f8a00c40b00c8002101c580d020b645110030300c03847d031240d01d00280c103050802c007864141c0900c03030700704901d403509070304050528001820703103180605807001544e030200320003035a41c41325498100c103030038020b04807501c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 485269298 1250 485268048 485268071
    0x21e1009051203180d0309030804061a03120405090105060304080f0d0608070f1409010e01180b10201f0c03181101090e0c070b100e01030b0103060c02030c0d03020c0a0501 75
    0xc80c1444e48403196075101e14400404902e100b48619484a0b9155035070046c10303256a00d031500541755040012511000c030034402c41c40c943c0d0070085801a104a104111745540c50700c03081107000001607000c18000d10742001080000352510085035140c2c1e480102c05610780c44040c50990080516401500b203c1c417a01001027101c5985001a2007120901780443d04800c8411080c4205c8110070301c644008404007400500286030003140f0110b20054409002500301801400100441c1100000c0004901c6824031200106005903140110035003200082c20402c546803400041e030350300003802070340c1c039a0b6454a41c08031320710a400054005040000c000744c204101e040412444131040503060100d05182e100180c04400040d400b442510400d20481c2802238907141c043ca1820014000301c40d8503a029804100280c100c0d800a0180d800b6600b007061641c1180f40c00411100070728203905c01d641c4180541c0a540100080c900a10101440d003d41c4a034496a10f907032030401c507044c4c001c01039424058003050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 485270548 1250 485269298 485269321
    0x7020102040f05121b010201020d05130507081b010e0619020c0901170304030b0402010e060408031c0b09060d0615080a021e09040f0c0e01090c021e1009051203 70
    0x42d1801d19840d80d514941c1c54013006010444488141c1c0680c010540005100c000e00001c0036003403206000240c500034005000d40304603076044907460b9226681e202a5801d02200300700010242c010a801403541c1292403105917502c1d0074207441503040146030300007070403d91158401c1e00d51103202c0c103c907269140e404100294951407030300303005030090341c3e8240006001c4006280542040804030003861409080d5150501c801078000c105a05000d03909201c08410346a142c002c000500414000d1a250303c1718017502c008448046c071007000303450304122580c0501e5840f590010f401c40300846085811552600d00750700540b00c01c00b540c00f00ca1035180400594a803002c11a02c5400c2c2c400c4410704c2440c2c81e8100054030483e40c0168450b00401101d00007000603044203041d91109004940324000305a030344030074a89061098000340103440d1a07240020301a601040203502004076400c0042d2000b47c2081020754800701350350000701c8581c440303c00000f4000309004103001c00790217200203507403441d2402c0010b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 485271798 1250 485270548 485270557
    0x703141603020d08060d03080a021303201905010f02010f0518070506030411060307051e07140a0308060418020411090a06050a020709020a050c070303111204051008040f0b07020102 79
    0xd0150188494000c500c03403084018a1040c030001300341b028921890345080304d02d00c02c004d0190001d59820031003140c4092141440340700962148568524681c039114151054421861050340180f41c000308503a540c401130005103080d0340307003032804051240a01400b00c5c050020083d032440030b0307494882809040314483c18040c91003510745007220405640d480c24400644821240076124400c0c441c0c1d5103019143c400b0007540c0107047d5180860400210402c2008855400b1003414212000082c10a04011205240080b5003080e90040c12001d645901d0103441124002c00d8644269030750300440c80c540e00c90071402000d054000d44201301c68038906c081c2500c2c541c440d2035514480c0d28140b900055452045044030440715065000d400490f207441c0924020f50008000e8400307006081c051403c1c04c1404200c95001940643c2d80c0030803554075640414101903030960301d0000a0020030080c081d81c5c030360702c0b051461010a0710b400d4820307a44034104a542d4561100004102c050301c171061203030007541500a0f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 485273048 1250 485271798 485271803
    0x801020307030e06090607030507020f06010b0d1a0d03081003051203040b0f04030e010f0c080309160605070f140118060203150406082509060909050d0e09010b07031416 74
    0x4111900e1030040f0182d48140403180c03c0c40300d5010100184c100740c8030350482034219002e401101c14412444115500380202600401c145030000f1032008406030301401500c4404031050743c2042c00750701d100041404584a21000b5090048080100b100702112241a200960300141500c0340116000c0f0010490750050740c081d5903240315080456000b2010840700d0b40125859200d5002c8845c1c900e00645041e05405032100c140100620070300049841c22000354450581d810140c1100814450208140c94841c1c000c0d008104003401a02c2c0047d142590720706035207410a11b180703000c10200780762501600c25545140d5a44290601080070400c5c00c0e0007441c000c1401c204501400038002082c0811101d452240b89603651050881280d0b0603503003565042c001140c1042c848855480c2d4164a09440306a8044889107903a034856209120062180190202080c900801c103201000000390b030b0004107000e10550000b00290803000c1501031220b02c020100c640d00d0700f80c1c0b2075451902024000481c03020a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 485274298 1250 485273048 485273051
    0x3030804060f1103151503150307090204080c150c0307240b090105060d090507060203130b0901090b0d02160305030f0a051b090d02030a050f0f1b0f0613080102030703 73
    0x208524010300e802009030184280c00f00600755a603000001c03040b210141d04007900422901703880083c51001d00021031069195081d401c05204511043c1443c1044544c0590300292040c4000d0000c0003010400b40d040c02e400b01c2d40c80302d41c90840710281c1c01a10415564001e43e200000310603007080034040d01e01c0038102c0c030300340090040c01e54400c900d82911023800e19140d11140000050200b071601c0700103008826100c0100241c03401c0755580707031441c0007411307004180503a0010803400048040c00d44024080d05004462a042c00403020002e00408040c0c042c07450303542c401040100c004290355060f210028504400c20024024504014029a1050326103840340c0d0025030004034070a105000d0386010b103102445481c8a1041c580b080191a0080c03031485600c200205203090242ea0108289020180102c014103907000151141070303e40304041e200000503800402d80c8141046610203190091101a02d540100444800005485108ad450103540c020076035240070647c554154069031086009890 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 485275548 1250 485274298 485274311
    0x30a1506020313030605041a04150c030b0a0501050901020f06100303030b03010915050a38030609060703050c0c0d0905030c041104030f0201020f0d080604140405061512070303080406 80
    0x202240c4920502502c0355040f102e0b103804100050702a030003564407a025907901c40311611240d241c43c01c0707400d06503402d5440b14140001009041e8851044462500b00c6050401c5807104c1c034000304144c064580709041c1481800305a00495900a101750004070b0340c500c0544140f840d01031130a601110990100b500080d1800201c1400c81c00c0500c50341140a0304902c8032001e12241c3e291a03400347c64028151840640c4800e02d902c11070800c1c070500100031144008071601c00035441c2101d2644017825480358401e0303020780180220020041440307a04103071249008201c1d40d4420001902910881c008009240315011410300a02c1c3d01180380000e8920441c10744182110a4003040b0a0f65603014480484180401040000a61440a0581007071042c0151000d00c401c600015003000849034950000c6126a8104040ca29081c4184001c102d16440c01c1040b0782050748480b030341d503040100b030f907052a01010f80c40d120640e00c100220310303808a41412241c5e51030316850300420080055800315007503030400340e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 485276798 1250 485275548 485275559
    0xb0901050d1a090a110909151b04060302030a2a18030f030503101a090d17041d090d140a0207050604090e1908091318121106091020030a15 61
    0x8000c240601001ca0090140400524400a4450019025041009c000014602c0a2009501a200611040d03c0050f00c920704550f446046d21038000d07034141075000e003150402c4800440c8948100d440668603101c901e114081500801c5251540c00161002d000080c0800425603c000150310500c0c05803100c00c0095a03400d950a01ba000841000c20a12801d0256003441d040840890300964007030f4091112403250503041d40340030ba0290b0041c121850300342840e00d4062401c0908070b5000070b81c6500030581071b034022000924118541101c0005003100040720f01c6501e2080000070043c02d0002d010b250345030358511410700105600c000104d100c0c02900806086e03850b50500981159811040032841c20030310404108040d8890840050b0542d51460302503005840320b0150f4150a116030705c800040c2422400140043c600c521281d801c660000c0c0030016402004503001c052411a40300100b0452001800e054012944400d94a4508c01c040104200d508454020b0b41286d603010001158064643c3e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 485278048 1250 485276798 485276809
    0x10080106090c26070c0213050c0304170a02030405060d0b150309240703021308010c020a030e030d210b13020414010804120813060e100f0b0901050d1a090a11 69
    0x3030203c0c03100315075440005010501030f82d089807440d40700816561000c0850030303807941100d03400c6e5121500d4034400301c01c000800c10b00081810350030598003180740c10010704000081d0f6a01c928040c450041c2c0c0b000c903980d1a004001c3e00801800c1c0f4005040110702c1020303180c0b0810300c1e00122022a964803658000c1826400503400141100d9614809011103586068094000c0c0d0701940c03101821021032100051565000c1c0b04400d81541c0e9503000d003180340000d080041c466200811400c4c40394100c0000da1b090316411134a802209507510720070b640c1d00d120101016005020700c150311a0070011510210b2140544d039402002525403401c0a204a405400c00441d921001110300816034a025a0306505081c0210b04466000401404058440c052655200196203d900711201c5c0342d44036a000c2055a01d060152011401104004200030080440055031031b42c03040c4185405401514400000d10809840ca102661050b00407050f260601c03200b400e66480380c820081d6011a42040250907502d0003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 485279298 1250 485278048 485278097
    0x2102092a130312020a1b0603050106110a060b0402090613090c020a0b1f0b0a0804030206060103020f0406112407021515120c0405090102181c0b10080106090c 69
    0xd207000c444081d800c50752124554820480003a044d4400c1881c1c000010302560ba0b00751a10350010240d60001d490070101038181c90060304800180b003a9102480d151724000140014445d40040c1c2c0071840c0840300002ca0000c2c4580482c9640098001402c800060200f0308080111001d0402c1000302c035143d20801c0ba101c40301101c0051040804c0300210381480a602020b000070300003440d4030911a5540c05486402d0341c0800508000320701140d04000505170180002a03200b1400e007001c1d807501c40c0288c42d03c5118419400740e1801d0040441241c8100c560030800f90b18103041300540c403402c1000740340061002d044110350510051044a480845861003a00c0150054419918142e09180c032001002032214900b048100c40c1d100304c100800c1d17195a5405903c0c0035030364003400181d580194510b0b0b4202e00d1281c5003580d0040c1e49250722641454000311024050b1a0050603400254440d03003210805070210303502144180d820440c000c98031080550122071002040c0c2ca82c50a50900c441034902400390 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 485280548 1250 485279298 485279317
    0xd21020f010c0e310c1e02120d1b09180209061e0d15090e0a050604060c02070305010e0d0801051e04020a0c020315090d05132102092a 59
    0x151040b160a0398203004408961200004490329240d07207040b04c46014034102c031201c0c0e01c0125101c014503141d458005844211584120f07803034044c00240c6141c040d55440728516408000900080c1c115980c604c81d07031280d5105a84055240111350a0740e0340101801d0043c0695080d2101c0c004034224402440d1084074500c0502602d254101001c01c8000001c0d0f50000117900e1503150200709811040001d0b100d06e000745020f455480c0100b50400205204032041d56542c210b0741d900900691022510009055500a600c8407011800c01e1b180d0b0800c906200d41c55000910f198200840601144408034003090040d505a850490582e80c0380100150743c0209046030703c2c0300d4410b0600c145107040540080c8682c0707055080010640e04181c2c04249018480401c02c0c00121604c024041e05c90b00c00c0c0007000140c046413910b0350034458003500d030004114052043d0410701c1d021031001c4124080c00a0500301c65a0000c00030b0440340303001c80e02240400e01c00d03401c2114101003607420309914049401510903030305 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 485281798 1250 485280548 485280557
    0x100608070e06040302180f06010201061a0313020a080a0b0f04020d020d050304050d080705060601020a0b2e03060203060a06021f0f02090a0b040816050f010e0d21020f010c 75
    0x8448190590340800912100d5070000d07410040132015803038400e00c48074031500d00424a8407034503124a0b0282d5030140540007504590401004104e240c0d00f410055083c4054614006e03501e440c0c400c00700700410b1079820020740000c8803a900242c0c0a1010404100701e40c01810054082c0d664120040e40720441101e00075071284428500b82c0150420031400d80c00d1b41d1040c01100d00c0d0640740c00010f049441c4008044030301da0000500d62080040c1804261340002d000c2c002060039042c660744442580700c0040000d000300b1420544141c144810802c4000004801d201000310240c6a0404402940c0700302d81940c02800407440c006222407001400d903002c04c007400a081004694102c404028040610005001603028000d440302c9603261a0743c0340092003451003250380c403803030b040c08642407201505812031160f030350f61401c01c0030ba110300c00c0f42880080246004100f00301c280700011100d945811001c2c0c151816030350520500d504954214410a0054007110381c0882d1681c452401d80300d80c2d02c503110008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 485283048 1250 485281798 485281801
    0x151d0103060b07061d030c030a030f0207021c03050f0f0a0e0109081b031e0105060a090212010302040c02030c0a03080105030f0105090d0507171201061115010512030c070b07030206100608 82
    0x503107550701580f120210315213080030281d0305c0829507107150415020700c64070780c000007140110160940f0a01d010400910020b5080098a07000901b407031408201c0b51000441c484030403001c042c8180115014101140100c540f02c400d200c540503c0317504042407401c040741104da80d417803003276011301d01d0541107039011402000c52000c40700914801780d1701e003500703d0340610401550076a81105c0360802e1609800400c00007849180150030040c00c2405680041ea0640c070401004001c44041041641925015503012075021442d00d012403440c130420301240f00c0c40c054401d48204056011005c64101c490480c00c07100380300e46012601c2c1c200e81c000d40b00c860304c2d54000b2081c05104d03801200075101d03090260b55001c1c110045840c44503d0b40c1d001001e119940d45120b4018801c440d0032403590801d0f02820b100501c0741c00c440d0760540000040601a851143c142c10303a498880f414204107d928407080c5106079594140d031040141c50319001104110098000c2030000703540d140200b50b407002101c01940d14001103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 485284298 1250 485283048 485283053
    0x61506050304231e010203090d050307090302091009050f06030d0216030f0c0f0b3006010815060c03040302120d02061302041413170c0c060d06151d0103060b07 70
    0x42e400c5040c102070f030b401801d400307500c89400000301c40803841c800e800141e52031411510701424200211000401d0010500c284001641e01100010540742c2c19a0200390039290310302011404590f5500c00e0310260304000400ca4140140d8503100e01555088e01112450685804c0c1640c8600c01112031000c030511407082040840c03030030f00d11000c1e018081c0d038903030300c500d80c442d5610005082160006805000d002910b110040044c850b9010b00e02c070101104042500c25001c90380280c1d0f00580124100450031003c580c04d01040c2040e2204504010581c82d683c016100b8595101d0300a440281d02c2034081280020948401140c1c0301031414160b805002d866070754000c5840306022080c0180e07046640d518600c0080000801c400b4026240002c41e800780c1e18080c0f501c0700c40c14202c0314803000c001d40144540c2c080d00400003181404450101d800c5510b940132041d8036802403000d68031110940d07a98281c0400310700c4c0c10850b840380034500d401c28a00503e54000054060341d4445c810a80410800c12100c1c02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 485285548 1250 485284298 485284343
    0x50606210606070209100e010506190806030c130903030605060c0c10180e061201112d0307030c140405060f0f21061008010b030406150e04061506050304 67
    0xc1c0904002c02071824040d00c0d0b00841c40708101101d401002c140c0d06d1009000310310030400701c1401064220744c010721300b044080291926070321442554080c1304201e0045030040d03800340305050704080b02038119071020b0003c040c04409031040034400d501007852b00001181906083c0203c070712082c8074030010900c00d082c1c0420b1104000c0350001c01da081019008120b45a030840400341402031001848402c04c9051200810410190b40b148400b090303850300c0b01451440110b0700681e41000014841004004400140b4014510840340c0381003140c9400010030409a415a00c5039103125201d41c0c41d140709a0071b0303140d0084548654001c00c1d51180d0280a01101e01080d00020040120809081c0b402c140e04281c01060521503580300b000e10001d07001c1084854141614a501018524604460a5458a5103a00c1c1610020300301628180e107803449901482c0300381170f8100040c040c01032a20f200d40741070308000000b000324030b14101040f120b688000400303a1142c03043e80c0c004e507040340d0b42e154115501c01a609 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 485286798 1250 485285548 485285551
    0x20c07060e0307181b0c0203060f060307030206070b010e131e02120d030b01020d020c01270f0801050402010f03090803070e1c1110020a050d14280305060621 69
    0x65042c40794400101309504100011581c2d403416840c0403454249641700801003501d40c0110500704a2520260f102680d00014900e401514400b4036480c191030302e80103c0d003008003640000c0e4111100180e441c041254034030714a412210000e02281164072418044440c2506882d070280268048410300900c66544000012240c0d10091002983c40340d02d6580606042600040c500807994556041d46196018065100034449510240c000c10311200006090b188141d040701441c0e420000c4043c7e1094840100140600001204117861a41d1001003a006c1c6c0700454080340011510300c0c20140c041e010707010304c1140541c080c204604656072208100c9130b000d018000da60f070200ba00d1094200000c80c3d15a0940c1c120301a640c0d040c1410501401c1c01880540c04c8000011503012044c1d41c004903170003158150340f80005117441a0146412010030740c0d64060790784074481d1a41602d04d070990600c0460b120901e42002600d0501140e690801044118016444c0d4420450381408943c0c00008040c0a107a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 485288048 1250 485286798 485286827
    0xb070509040f1407110a06090f0501020c06090706050a08010e1e010801090c050f0607020d0c050915031c0e0442090c020c090603211c020c0706 63
    0x2506004290000038103032010100290415903031000080303645503083d8000d60f405081c41c01c04c124004c001000c031541e00c000903580900081e980b106000d0800211203039520166030480004c0d925284c00c0c040071502c07014150f8840b45c8170f101d01213002901e6401002a2258080715480d04181c90b860300e101d2200d100401016078416515000b000b10fa44151511a240a421102d0000540100500d0b10041700e040b81e40285110b41e00710200a080c941d9002c0c1103881032a81911071000c0d941d17a41c5080c8001400640020b82c1c00f00e0742c441040703101241640c42e04c140d0001142190301c45520310009540c14500b8407000e90000b50712154216090409812451886035503208540b800301c0f175400c4803c9540905002d40c1c210b4044e50950082e44144980a50060300070a5410071401c040800e0280da02d07414101c1d0a805081d10100190701540c2c280829200a02c0881c240c03210304d480c01c66000712540c4111034140351004404685031000095100742d03219a91808014000b80d800d00006981191199000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 485289298 1250 485288048 485288057
    0xf060c0714030d09031e050c0d0c0f0803010e04030305160c080a050433020610091e18050d020a050309040906060f06170105040227010302300708130b07 67
    0x30400320030f2910980360642d0099075a92904103031490800904980c901213481008018441e5603640d12000c80c801c1c0459815041826890f0090301e0804000d03042098003811300c2201000000384249441c1c03401c0c0c4180e02c2580c04101580d2907903070394110214070140f030f94005180c4030118000544800010001d0f4221400c0190070213685030703691b4242c20901c0001010074202060f41200d040c07284001c403145140c040c0050b200c6c52801554005c0c091445106140303005032903030100c1401030301c3d02411314070000c03802c4000d000d081c0d590310007590729614000048a40340714120f880c842c00d92000c40d4143d05035030300101075480c0c00f01000070040078000c0c104040e03c1095480400003000c12040c0440030051040b62030308103c0528091000c0d11a800c1640214000c900403c110007500b09030100d40302c9200c8008224140f12a40400100c0090140120003030042e648410f1011180303d0315000781c80102c0c1102c1d010f00c401c0c0d690403000c50303c03d82d06951014581403a04545000100c296241c03d1384204a45032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 485290548 1250 485289298 485289307
    0xf050c030106081e0106150f050d0c080709050613051e040e0601030b0106090f150905150403021323070c240f1512080706051501020f060c071403 64
    0x30382118181d90081c650b80d8007060600403100f410903003101085201e440204012890312083d80500e020f826211010400180c50400c4c8640c000c1c2c098813040c0c0c130354000400000380d0440c4043c1102c0c00c01c0e10007101240124400044070300d8070408440c2c12910514820400301c2c5440d080c400162012101c1c1c8125104c4070140001a440d54402e039039101d81104010403c5500d182400700c514075041c1c205208200000c0801e005520300490903100303c4020034400c403299045072808440d82c0056070829031740400c40c02d4401c11100c0700740d00904140d070f0088843e2440307107246401d414129024020800b49001c43c802c200c100b001003406106910207003034140780101852650f80c45c410b07040c44c084803000c4002a060180c4c04003400d481042c0c541150604100244090264245164032491003a02c0c50490601d40041c200701442080d9450203034404c00601060400508500d0310790460f060250040c072811050000d42100000e40030701810380c9990407132910019071500940707800d1040844160744010030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 485291798 1250 485290548 485290573
    0xa05130b0103020d0509030307082511152d010f050105130305010f0c350a150b09040b0102060f0406050c04080d1806090e012d0b0c010c0306030803040f05 68
    0x31075210b02086c074081c50f6640350040e00070340400303406480b040710000281024204c08984002d9015001031303901301441c1406202d90014903100c500000e0317038078050320349040c0300001d40c10018001c41c194030302e1503038003049441d000940700a103000d00c158035290440100800455000d44e0041ca40702c40710030002e0784090344a80320203007552071400c0c4001c0c40030398900c07081e00c220340d1040c1c01d003064503445442d540008030045000803e902c10b00c40f0a480076030074000031410402542d400320912600f95401100c8490755410a089503400c4440760340c1c015400d140c0c20164940c4042072079481012060315040340c0e903c0b90389070782004100c014512781c030f42c4600304000f0880f01000c000507003480d0a541d5902c212031030351050302d188124040d0720401c04d0101581040c481010101080390540318403044149407050b0444808509022008810381204484040483c41682c80c2c0018800280301030001e0140c0c04000d0f038100c084851603c0040e00d501000d001080000f0076000f04d10407458000e000315844440041c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 485293048 1250 485291798 485291801
    0x91602070e04080f0f041e031104150f03030809010e07120611071a0402040b040b0f0402070609020a0b0309011425020a0b010914090d020a0311150403030b09060a05130b0103020d 78
    0x2005c004c0543ea070103d020004e44030368000703282e10f006008a03004030081c60b50342d440050040c00401c0610660325001058000601d00002c0d00040c1152404070300b40559900380a8a040300c242c4100c0020b500344016400d00300d1002494104a8164590144545070b840e16260010b155655a102c03078018100080130105818000300201844c3c40496412541443e00c100011145030402440c001ca00b040510350250341c84450320084074100381c43c05641e4510614141e4014509100000c1d4071803100440454042c1315180603520801e80c1e030000304045034000d030007817120340300445541c5a2041c3c151402546002480340501c04400d0720300403500c040321f465036021850781090f080307406107a03595041c607984a0f82c02ca034a01d800140c1c40c8007074600c480c82003074029298800c00d070014007400300207170540600c1030041019032000d89207000d80c2501401c1c0707480d005000c1c041600c1080d124107071800c080744051505100d05011504028000c3d00182000d070f00c05405040082c2c091418182c1c02e100d4040a2a42c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 485294298 1250 485293048 485293057
    0xa090e01060504080f0a050309060717120610081b0f0c34030c050f060c060a05070f0e0d03111609090309171506060c0f010902091602070e04080f 64
    0xc80e12101c0d03c99003040c060515100c2c01c0c1214881c164000151140410750101c110b50300c6400c00c1e12102d40d03030760840c1000da50400b0511039a010301c40300007507070240b104049904d85020b400200c0d54040c903800d40840444058209680031192600342c224152900b10304000240045074030000c00c130f81003080c1030032218201070996032002c01c80600003140784031124002c120000d242100600c8682401c1c04c5031034100400300d40303020380750288000440c030080d0ba0362041d091b580c550f40c0450868a0307901e400c040702c001030941a5a507101054a1b07242c5a0007543c040c41c021000602d029107031445d088000e03101240d48101d0f10504007468010310034881c18041c8241100c0000d400740001c007090040c82c0d40b0b8010f14568a0754071116910440301448841c076030740429960034a010035905181aa01d0303d400140700c1d0f106081d10801c0390301c6142010303e40c0326819085150340c1e90086940301410342e07c500c1c2c03901034950315401810050304020700600c1210205074610b034200d4010702986017017200c0c00c1c0001103a80d00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 485295548 1250 485294298 485294309
    0x6010305270d020f0706051909120f0b0a090203030304060f0612080304050c090106021902040f0603060c1403070e091003020d0311010608010b062505010c0306081b0102060601050a090e01 82
    0x80b02007500c4040c3c0403c0b9160340031800710002c2c4150b526008008100380500700c010211207503141d1000352810304c540f080001a00c441d80c600b42c0580803030700d0300254505441c0000c50380a86401c0015030740d491140b098800054000d0051403031581c482e540d201c010440e40a6000c1503558900c00030611801710b4140000a510490034603070703a030400d400c183d8074001100030700501c1000e00d000180002c0341d0111701140d2454601c1c241c82d01048042c03001801401d0713100c0078a40028a0080000107200e941c0d00500d0030211292640c10040c514022600c410f40f200301c03110070204806203c40700d0030b801d081e8519503001640c081c125900c19220f03030002c0c80045604806900044c0700032a540010402803080d1802448036100804c04050f20314085082409020100d881c018030203070b04940e5208202650101e003e0f40107000f001402c41400c0702800510040c013940000d8820810b000d54101c6c0030070004a590a016001440555140401101d503980980c8500040112945000810101c0ea0b1149400f07800c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 485296798 1250 485295548 485295553
    0x1c050106210203070905042a08011107140a02011e02010617160e090a03050c0c0a0605270d081e0d1d01050f01050103020c030909010801020717070305030601030527 72
    0xc1e4180109840e001094110410302468130080c8000904103a400441116294004640e00a0402c00e104020102c03680046000d500700907540e0b0b81c81203590024286076110382c10750991920a000a81d42d1031040c0e840003030105508480409400328141c103014100142c510020991035181d81c190802c8229130010000341ea0f101c882c0c2100c0c8582005c0040b00034182c04441242036240c41100b0303035582d06020350081c05001300080d880303140139030511980505c84030240c10004000e540380b400038403d5100d4081c040c400311004800c4003840000d14079000445200070815401c4a400384c9031000150b10003903024014040026003103200c00c0c42c50002d031900014440d80014021040e924035541920340804203201c2ea4500700c10006601540300340641590020b103001070720b8001146005240d442007103207a0754400c03a200b0002884110540040000c81d124074029074020720700d10490340d400d001d04bd00041c0424014000030325503501c69881250302c640e114060311090021102d5030171080080014268054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 485298048 1250 485296798 485296859
    0x40e040c1508130c0806090706030c0c020609060a021501030f0b15060d0c050c01060b180a030b04030e060d1b0305060913020d0503070605010f0609050f1c050106 71
    0x144416220060036040103007000742100140081ca4003000800320600d02a0702144202840a96000c0ca4003404005085a101d130a142041c0c171760b580c1841c81203070000382c00c0c2452424000d10400c0c840d540c96601500b1035081001800400400d50000b03a00c0404501c10008003000b00c031204e0304a54000c500603001440001c0c03080c03d1414200d10010002c02c09410340c2d10049069440d2581290b02c00301149600203240c41070604119142c3c464118986029800c200c00828614815802407080351488040140380200b1001400300300b0320315100241050400d4800600401d000303036400080140010f01c0c5510f08600c01d55a001150650400e100c0d043c000640418655509840744a402000880e08016070385010b41500c036001c071021134000d006450300764440c01086001c10540300d10a51090043c4944d6840304002c444a4000c1e125007070000d440480002018140119071040002c0e015180b611460000b00c0003100045030581e08907542d658031440042c06903040b04094070b502502d8030b03500c2940c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 485299298 1250 485298048 485298053
    0xf04110f1c090311160e0402040905100c0518100203040b03070302040b0d020a12090510090503070203071202091602060708150d1b090506090720010c1701081b040b04060803040e04 79
    0x90105a00300e61030b05c401031308070504c02044055119584958100c4004c511424030b450701c03a04110100071400d0b10740b402c104400714960340001c060030040c80410303a041c01500130b14003040030780c00c12480c040d005604108002d02142101200441d4030902e281000b600c0c16580b40310340100707640450070340300c0c03001d6020880c10308240d8440e0041c0c1c1a400842c134240459030036619995202c02d07c01d45807515650ba9400758800b00b0800b442030700c90041d0010b094560b804c0e40e500d2178108000366444100d21428107040021958841c1405a20700002c003130340102003640e00d00c80c040d21424005083c00801e0340c00380c15480c403541d8429584400107842444240070a100e036080e07049849480b504010601c5050108114581c5c13070b00721030280e201c09036140c9140c03900c182609242000c29518004002e0303508140750303440401c0d003000d0066003150501000c0300c03417aa40c6842c0c49440340102109a420710b11180f10690710303460f0640094600e044000c00c0002c40c1540c40ca017043c5113500c01c1c5e10200c01c42e04200d040005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 485300548 1250 485299298 485299303
    0x9030b0a0c140a1b0b01050306180606010c3f020a11060a050c030412020f06040501021e1c081f050109030f080d020d0b0f04110f1c090311 61
    0x412844044007800a03014690010389120b011032840b4407030600c0400c40018407403080e01196500794421601d000e01c0b00460402c84148a424020203001e842020003160607880c030b004e00100154000341c0903110070784420004581c5040c21403804d803a40ca08000582303400c1400c81070750b0f44140241d0740740445108a0446400030385101d03005650199042690143c01180c8941c43ca030541c40000c86072240e4608003200c083d41d40d4000c590724035000e444007003030109060000e0b800c02900180202c441c0a4892110000c1003103900c181d020346401604400702a005040030001c0d0348000c1d01c115004c2d2044c00c2501c0b07a0008e4030210241145001131004418804608240c100b26507822100301400e11182e030030322001030100703811480000c00d0030340007051000074486002d00340c0f082ca01240a09540e13407541c01c440b19010700241010320703104103e800384403423881c0b84c28810b9000310404503040a0034408015191000c03a040543d140811000704061607a01c1117044c4030b210501846070302d8200110034808656803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 485301798 1250 485300548 485300551
    0x90601060216260a03020a0302120f0f0313120207051306140105070c0801050c040303080604060e150f091e0f060102191a0406050105030f03030c0a03020705120a09030b 74
    0xc01c0d900040081c0401c18507101d104401c0d03e458078428079092550089210894404480008540c0201a100b5007056400724240300340c80e000ea801c80d411070f05c4101c1900c95500c0b91b00d50900c2078200c1007007090040c4801e08003441d403020602100400200362521640e0503014049003840040c0c002c284140b00c80d00d00241c1078808803504003400c005c120305250082503690011000c2c281840300204140781000f48902c400c0014005800080c040b90404110502c0315401c640001c8001c10310480004d100d030f003014414002102c1009421150945400340744003a0010b19586d0160025068a440722081d2100513a40c2d024031060600e00c10708000d200303808814a20081e15500300c5581d04000d02869a0380010f4155281c000c1e401040c01d0342026180c090040010151090104030501c010082030001c258005030403200c094050360940c210709031482d40c6900c0122801e10104000380604000d0724426800b520400c2d10807002c550f01840307203422050464000a49070720003e2803901d824010802c91a4415 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 485303048 1250 485301798 485301809
    0xc1b0717160306091407030605180f060a150b120702010e0f120a0c1e0c1403120903010b060720010f050d090c1e0e0c030417070201030f0e0303090601 66
    0x1c1c01c0d04a84040200ca80d55040e11000e094252100b400a052000d00c04540010018901c1115000c03541ca25084010300000c451044015401031006c228001010940c0212a060203000d40b10313940c0e0b41e20f0440001d00c1d40c41803507125107011030700204014590000800802074550200b4100340f0701560000e003503c3e0340ac0c09854098100300a40081050001007041c0110403200981e1f446401e83c800c102d4180c811800c000d84070340e516684540722481c1034040b6003425802a511000322640710039200340104100302075180c02d0790201c1c3d1092080360200c005440740f021300034008280c60340d481001404a03004a90291102107003201c0d4528a0000700492a808210a08103600c0e0901000d80c00b5205004040a076008141ca4480c40020808444111400b5214080c82d00070884160000c00f40c4205542c01020350391003428000c078400c2042141031701d218940c0a07130803184551300015048907503000408101e052540764450712503101064020341c0d81081c40100119100e1406480043c03400c0c0040c0c0c0403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 485304298 1250 485303048 485303053
    0x507061814040906061202122d03090d0b010e280203040201030609060623031005131506121b080703180510020406140a170c1b0717 58
    0x1800d68004000039410100d40c090460404840a240d001c03802030316115500034119450500007051078070709071002c02c5209000780d501440803000f20070300b20b0742d42d800540e0103100c1b9100a0f0800c500c540092002c41c1e0301501001c142c90500800d1404209206803190741201d009551000510080c00213020255002d4480c5a040781210140000701c0d1b00c2003d801c0c12070b2029900040041e080d0b9019800407401040e0b0a0f02c200f0040fa0368041c02401440d4509801042200300c0398001b500e00d078004140d90040a00072210001c1a01c1c101c10001c024000d1061028501d459029500c01d40740f81e03c0000000b00442c6c3c40b06203581041c0302030002200c62405c0c0ca00c00b105d2004001000041e03008035640e0307011150303090006958990002074021407403c6240180203104020f5015030110f00380e0003600840f139060300c0f52909034164440c2001d20340102c1c0c00000c00220b11500461461885000701c0360000e150580c501d20b00b41a150301002900b000394101d00c400d40c402d4204101c095040480080c44e016001c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 485305548 1250 485304298 485304317
    0x4030201090e071709010203190b03070b031305060108010204050f06030405071703070b04050d0f02060121080f160213150909020301330501090302010828110403050706 74
    0x80c02150680c002c80c4420306501001a004500070103491861400e12800a4014642004298080d600444080840280f4071114059024480c001e00f454140002d000d040c0ca5070404c02c072a035260704001d00303c04003003007030140e1007001c684180700340741c068400000007507039544c200401e10100100070090103010b41010030030403001c0b44010441400795182c12160080c040301c9a5a01407540c005c500b0b02514406100060104002c0f0001d10141e4018094580d00500d0070000d0341a61039000912480c1c80458840f004040503c1d139508481e41103500c03c4078031a082190411711507040703801442220b28a0408014241c081d40f030303d41500e48448010301c4040c80b4004100100b00e42d41c80b9180b01da9041103480301d2044045590a4000e40c1a000b407c60130080310460130714403189044450504124803809051020901c1d5124200e0300d019641c040e1100e0b0300355155501410310012a943d50221030031900303100b4103101000d6014110307040c800200710588031411418010f04000165201c0024000300f02c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 485306798 1250 485305548 485305553
    0xb150d1a011a2502010509030d030510050409050d0804021305040b040228090e01020f0a21090317100b030a02122508190203040b012c0a09021f030b03060c0403 70
    0x14040c144400c59410340c0d0385040580c130040c0e54134082e03118415814041c070707969984c00c1c940c1948130a100d508a507000b00505c80d03442c02840200d07229540044c065410081400034140c0c00703944c51079001880a810021148141c100d69011981c0c1074074100c2d020380086053c4420351401015030713040b4600542c0c1c2c04164008841c0f1800c3c681040c0c1c881c4409881e01c510b2419022102035050780c141040001181d50341d17a41d012401056094042c003490346819010510b514012164400c02c11b40b11380c561184e42c111451200d40001c1030034014003140c90107001d4500812480b0a8101450080d800c0320000f50b21100449414445604001e0070000e90b035280c080800800c90503031030800b400c01e800c0e0411482680f0b80400032454007584245103080103000109200421401180c81c2d4100c3d07894100c000400104104020861010760003003184043e01c81c40816501241c82e800f01800500c010031140c1c0170641008841500610003c2601c003003513030340f0005003050400303100e82540908883c500c10b00e0981941d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 485308048 1250 485306798 485306827
    0x1202010501080d1b0803090a17090a0b0c030702030a030f0f021203070c21120f05070c1506090f02220605040e0a02160b220b150d1a011a 60
    0x2c3c010fa00030040c01c1001e241c0340c0541010045005500400c010345d880c584820f242d035440003900c1d800c4500300c100d0400d800003241c1c54800c0d60352040005001e00e550a01c0d01c9841c0c405a081103a03040c000b40010003692005950030091484194030031785030512007012106002d040100300101100035500030607148091f0203c1c1d9000c0340d034480000e0820940d90800c505022050200c161a41c8201007900c0e071203d414039400915905000714440424030110740d4143e4030900351007066401401003541c9070300342400a0800c00045100038a62400081c45aa45940b00c03403d440f05561084180ca500003940c801100ea49018181046000704243c030009281400080117032003603208002d07079001c028000c13401c500443e404959207000300360000c08200c0d040c2e00348689a0802a500c1c40030020040396030021410f070030325100d0b42898001418410541d216010782c008400614420350f406200031080d08001510703000560500c8201c1e41e0380502a40c10a00c080103500350490021101000a10280c03120b880c86 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 485309298 1250 485308048 485308063
    0x105010f36090f05071e050913110d1b2705040c0e07030e07060305100501030e10060e07081e06100e130f050105120d18090216120201050108 62
    0x9880707691880544058180008050408006041050754001002804070025890b0705948075106171a50344c142e080c00701218020144682c0d5081108040006d00c1445100c20f001b01d903501038402d04030039440000c00130310b5001c0e22410880d1468031401d41505414080d41c1c025019001200310b8043c2a0320511141898070707100e0002c901c20035141c0c0001010000d82550030b00040c01d81410030300d298140390f000a409020600e8541c080d0348210180090414070034010715008200306400750103d2801c103001100501118500001075114032000c94034140000c0c03042a009091a008004050505a2009201420250101c02c1605011202d4810561600509a00420120740e0000d03020b604903015100c086800000079031102c04241e80300d048041c141c11017554070800700b208001c50f1f03894008102c1d00c4200e8485586250703000c0c11038550514000c1107800351086c1442c0400d00078030b58440c501700a80e030006c1440c100101815101504000090780c1d1202d81442900007840990305040c00756039103842 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 485310548 1250 485309298 485309369
    0x240306120201170414010c05070311150123030304030609020108070c11040203041a090607021908071e060e010603120c02090c0a05210603061617070e04020c0105010f 73
    0x306440840c08101c205114980c09001301402406082003600700039159810125041e00490845042c400142c0d00c04114003850b0103003d81133407142e9081c8901c2da0401c02c850031401d40940c0c27943d20b080b10265001c10161004511401700425980180c0c0f00040c2100300241802080c0070b00071018500145013a1000199400260350041c0c59039103905104081035000b1507400300b05010141480300e400004154144102e00036002c403220441043e590700b840100c140c1e800751144c80e090048200003038035140341002968841001094081582c0c0313030308003224001c8040c052036039542e00c01001001109030b038411030b881c124181841601a80d801143c0011001040700048070400581c1e404058018010340d44a121680c501c81c01c1c0140030600301c2040c0c20241e6845203c0c0c4100c800094145483c6256002955015940d40c0450320440c681480007a201402c003800b4003204060603150303a02c482c130250403005e40c00c200200d00ba51400403000098a455007100f41140400c0350041604001a000b25040c00c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 485311798 1250 485310548 485310587
    0x60f05040f031212021b06090f060a090f05060f0a1514010f032d1d0a030e1503071d030f070b0304060e070303081b07021804020a240306120201 63
    0xf001081241d00212201294021903c042064a2400c0f01007007a503a01d11280000c840940e2100070000ba6520b0907804c210b201d0781e008600003012001c103a00124003492180118001300e0320b040c2d07141420804c00311034010303400031040c0c10440024854000c2c05c811500c01c000707020f40340d401c1599400c41400a141c115050100e000c0805601038442d5000c1c03001e1f401c80d1002030030840c0d668017484211001c0707610341011060404801900c5000200b48500440385c81308028041504950b400383d82d0005101d0845622840030700c0210700d100300b0395009520421300c0d80c0e660b800300c108503c0e41c202c104002d00fa60300c0c0070380c1c003400d41c1646185000074194143c07088a55804e880f030707803249002000f40c00361010500c01802600c00000406400900c4030740074050356a00750600340070544003d50a03001d5008042e601c5041400d18801a04a050740d42c0d0f045800585010f00349900d41a800440b210980c3d0000020316030a460000d085526200d8903000d40401020310721407803400d0300001e2182e0504c85800c101c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 485313048 1250 485311798 485311823
    0x5010605040323060901090c0b0a050304261b160f14030a1505061309020d060c0302090a080c01021009120516170306361003060e07060f05040f03 64
    0x24040a0755070003811400d42c04c0b2034603032509848050280510a000720f5050a035020041143d004003020b441a81500b603442a0456603140c854020210900c1071460040042000303c0314804c2c001d200820040c0421a0082c2c115552641d49038540f8080c0041e9242d40380c1c18000900c0b10001060365582116003060b862252503042e0b41c0003d05109a8101c001c00e50700025950000c0100141c00941c880e08003211a207040174025040001a6901e4840095201050b20026000a03155600605001c4290b290041c10040326801249481005801c05d007216401601000a55a4100560f0070301f030b440420244889d400301d40c0c2e081080103003603404d00c003440700102e103021130f40030001400304d980c0781c202c11208000090100f09061a91003a580640120185141014007104070001c450a082c5d407506140510521010800e00c0010090812004006c03600e2000010580c9c0d405040a1080240007910240c1e14000c00904480d0b03100c1c601e02e09221041c001000004003828002040f60782145406107003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 485314298 1250 485313048 485313083
    0x20d0809030c09090f120a0e1005070b100314010209010509090403020313090204060e12060f041e03030e10180b0604060902040b0915131e121b0504050106050403 71
    0x2040c20001c0880d07000380f001002c0000e036000000e598400e2220080030b585207803480030b031083c03c140b08841b181408075645214001d071509017065103d46000a40c60700d1810044265190042c403601034400e404860516041803050004841c0c00032400034001e03008624280e151000a800f60007140c0e1964851001040050103040c024001c0b80c1c100303450580ca0940d100c0c1c4a200c888020b40240c002c8000103030b01030b13040540c103050072441100240740e20001820555603001910707114083c010000c5925440742846c0b620411100ca0243c905030784240c80110300b500440140031700d8a00394a45102900b42410342d003100c1d44c0c0c1e02c480c0c2299a5a04052003c009545800208005c1c2a19510641c1054400076000a04040c0500500483c10301141e211405002c000c0d00c01c034460086500c1048022a030701010008010710340e49058403150400700d240506a650500305261030b030701c054180c50341d009021060103000e540074400030180c41d08880c00c0080b54140708000300a401140402042041c203030442c81072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 485315548 1250 485314298 485314303
    0x6011b02120309090f150f0a170a141522032003031305061018020a030612050c011202030709090b0f0d030e12061b1b0307030806090105060304020d080903 68
    0xe80b5010b00203185905003108101c0745c005040754001d0102c1300c881c40c014024079022807510780c0032600501920980e810000d24280060400072819814840c8650302000600d030010500c8200b01600050300c120900180346171034010004120b50510f14040e03507800416200845491081e64140c038100c8001c030304078030b804a40741d41d210850310b06c244408004c110003558010301c41100e6a1040d410390f013030794517071b55544950754006010741345104000814078130400c8010342c054280e407446450040b4110360f644510710f43e40a8001015a000d410008103244196000b03e03044058001640f011455454261700041100026000d815000ca40369032030200c0960f990000640d10440080000580041c2c40c94040c0c0901c0f403203291540038002103030640454500200780c140c8510040e080440f0958207121102d0190361201c03180c11245005030038280e40e03418040000d48040340c407a48a20805007031201c00c1140105c4140d0003688664820002c200060311842c0030754904c10703440f2042c29198034a40c0700007030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 485316798 1250 485315548 485315557
    0x1b0a0210110712060203042f0114120a050907060c20060d0c03050105090c07030e060c0708031602040605100e0f041b120c090602210f0c031206011b021203 68
    0x410f0001005050050765030007580124800c012081d400b0304004803c850000002c0c0c0c0d8242c100600158540300703940240019078840405004142c5050340c41d1001c243c0d54039003951104502640c1c0c00400c44441d4081114502502c180c0c1011204403a99a80d00b40c050000440c5010f510b15540441c48030603103070300c0c2c1070300d10281c0c802030309124034003a054004000301001d102d014402c0346510049942040741504071540c1c0f03a05a80c90841c680e2810092000561107900a000e0328400c540000a11720000e0010b0015002c403000c0f40b00c0002100e004020503a107003038000c244509442d040400001e03400000c1c1c0d00d514802515090244500b40001500030075810000c3c00100e90301a6a00c1e405551001d503c41c101d013003400c1e0810141140309812a1003132800c2c084c810141e400070350070007000302898448460050030350140702d05c3c04050700b0f00004c0940203131000000590001ca00440d80340c01c0700000307a82c00002031800844891040d58020749450547c2400303406080945a6446001020b00454 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 485318048 1250 485316798 485316809
    0xc0c02060a0f0905061603030c08013b13170a090509090f0609030702040501090204050a0605280f020d021c11070302040507090815070e040f09021002031b0a02101107 73
    0x22502c1b54030741e1401440d0004040f100301c00080c0342400d110701075401122014184c4098581e044010581c0040c803518021070240444a20f05601c0c010f440040c0391035003003a104040d010b40e82c1c3c080385034500d050307040000740c4e00d001a613a02060289000040c0d0000514049400481e020741e059250410204d04140d02c44024640c58003501c010000c030680004001c0803428401e41b070800650380d80381e1210040b80514010940c3c00003070300504200c503070f00c240003a00002c9200301c109800c021101d00a15040c100c180307408004500051984811030703405008090544e14180040c00701442c0c40c0000e40107481c0845070402c20b000740039807038602003001005a00c02850b4040c108012500b001100035007203030198031402e0031070310030320300c503114009031410034580201580e480381c1c0503055103201084080c2803c0b08003001c1035641c0d0140b200240c1d40d00020309800907920340140d6602c000a07035007042c60003101d12a0762015404074402d0401600c2e42002020381c0011440d144074120030303c11391b031820b183d6503902c80e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 485319298 1250 485318048 485318059
    0xd2a020301050903030603070f080303060607020a080a2001050307092601020c0715050c0606010828050402130e070e07050c0d050c070f050904060e240a0c0c02060a0f0905 75
    0x10000c50fa2000070085000d000f00301c0c02c40b00d00503030b64098001078a0140c0181c1d0895002800072410f0790502c070025011300c91008000341604c0b9200c03501c951400b001e856040c4d4415803101c00c1034403010340d0303901000da440c002031808520b185400309010302411801e2060210f020861881a51003e914203554100d00d265038000b55514040c00b001e09580d800342d03000d864428400e00718440c0c80c041c011000c546010251a0142105540d1440151440311005150101a040c2d98400c07480b420304042000703e03000c1044130001260b00b03080c0140b080c0c10303400c0500c09904514048109000400009030359041390741000d201240343d5206642151107000c0c4450101441c807644001580031508140a0940d03128031600b25020180d0b038008003091603085100301a0020070b20310100d00444c0c540d070094115454818120340139011004009422850400700c0340f030742ca0a107841440144010b90184581802c000e01c1c0a9081d80100d80004d1035902c0350020600500c000c04140c0d43e562806801e00c8001800c00400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 485320548 1250 485319298 485319301
    0x3080a0504021c02190f0e07021c0809160b120108070b0414060409060803041a090114160b18010f0614101e0804031e020c0d02040b0402030c04050a080d2a02030105 72
    0xa00380703003035446c50142c080f00002203400242c005100040b84100201d40c10401c50043c141920207480100c0e024204c0303a018062101081103005820743c0610040c00141092a0382d44140c1a5841142006070000c00854204a104202c6404040306481c1500c480100729003880c640a0b0024481b442a0341c05012400c0c00c4c81c40020b990340000c8041c2040705c0d110003c034210080710b441103120a10070046a6404184c20f074188014400c4140c000d06808881d44400004603200d540303138444104c10895400c5100071510b610041c0c00b4500f806085002d003007508003440400d05101c00300428015981d8514054402800710300d4480b403062100d01541c80071910281407050b4018802080e0340e6084400f0b0740840e11642c210040144610411070b18600660b02a10390180007100700906000320341001c0c0e0f40a500d9010701016039540e8030041d4018040e07500c0e0503a49a1a00b400c2c080401c034994009681900400407041100c0c4d0085002e411464130002c10203c803008441d10f5a0303201c80500400382d055844c000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 485321798 1250 485320548 485320559
    0xb040b090f01080d02010e190201020f0709050a0c0c11040e030f0712091401090e180601080d090f18050402040219020a02040b1c0b07050c0a03020a03080a0504021c0219 74
    0x407501d069900c440306030355180b00c00341070513405e9412542c0280401d42c40390204402c021074106008441510520640304015003034540d00c1c0c5002d19980013070000c941d483c070500081003000d01c07500d1244c00c050706000c0b40001560311001f9480c2200180c840c02140c507800c2c1041501000d0040302c1c04890880c031990b4a070345513400d2014480c1c01d14081c003008500d04250100307529464503008800001c059542030307116070034946140001c1802400a141c0c011032101d071161009820701c02c003400707000914010700225510b02d40082c00c5d20400c5d480114550606030701402180c00321300f01c503086952600004526511070380b011400900c1569000307050701a504444008040d40880d890045c14001c0310306000030401241004041e00b11060114a80c0315040c100d1400100340105d0107502111a040c003906108a00780440d0801c1c403440300440040e040b80c50603d0425070000203047d00a600302c0c0e82001a883c090b0f0214011000c0701103490750038041252400c04541c0e074880e43d10f0051440540c10001d0991301c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 485323048 1250 485321798 485321821
    0x210606130605131a042a030605010f050903030d050a1b081314070f0803040306060b09010e011206170a02010201060b03060f0108040c090615081006120b040b09 70
    0x54940520a685008140c4003030102401000c094640040c80c1401d82c5100c1408a001450364480400300c0722640c03256406590303194070031220a0382c00b900304c40c03c040c1905000075007800a02a291800d061a0110911060741d00c0380c02884524000d08200c4d540f07a41000007c0d1841c000c41024810142c00c10040124000041e084039440a5104500a00c1040000c0c01070300d20a9007124140c0414151480880104d0700000e00b200400c001003007035540141d140c3c00c80941d0800c05400c002800d900006040080140500c91700c0010000b6801075402e2410000008220001e0800014100b00c404034034030a81c0c41007a80a14000d00001460111010f0020480c81c0c40301c12043c1c00b64059483e0403000070300d5101d800101e902c200802002003000c00c41450056a0070b0300003070015134040c00a202c2c08988107040d44100382c0503001d4601c04089240303203072500410b5040300820950141c148183d04104444e040128100d0081c01642c010650854807004600106245031145600840d4903003480f075039040e0f4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 485324298 1250 485323048 485323051
    0x7061a030d0309240b0603011706090a080405010807021603060614040504020901050904140303130c140108010b300115050c03040303050307110604060e06011203050f092106 76
    0x39000d0324032803044090260201c440c1010054005215a0305440a005031003041070740300501c6200000f1888011000329180342c200340c228944c09070400500d094421401c00c8090780c80045500200000d40c3d0a60380e02d0840c0c02035101e65414003c50002040f503190003880b255140010704807022000e540e60742041c001500491090321000c0c10149070101d9941000e020700c6120b00e4000d0110401a4644028440084070041064800c0c0183c0301d030605106000b80002c6008148141e21701880305401e00301080080c01d203501c110440b011150000c5066604034a507241103075804a40319403502000c00f80b403511703d52800c070714101104045500d10303d0b4a8620082c181a02e01100d05a42c02c0284001c00b6200c1f03220748031b00210558400e0008100280c8280f008643c80895440d081c0c001c8855296002d00e00b0106480440b070070340e12100750340c401000401c026801003055076415014410a0f48010b011032054642c5060303442d0340024031042688603603500340d07a10014172911504c2c1140c896040c540b00e180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 485325548 1250 485324298 485324351
    0x70609140d1202120115050405190503060c0903060612010e0d031b030e03040320060301080d08061c0f080909010314060a110307030f0905030a050a11061303050304080706 75
    0x500b00d205032400390b4510940b1000310340c400581c00c50ba428105030007007030f8035148400020048204800702d0943c881d020b04103410700401500c08070075400d150405062100041000081c080203000329401c0fa5400034009130030907000e450900903540e04841250141869034903001d0f03140b107004080c140503589503000c49032011a900c6605110b09a40c3c5046040d10701081414030250701c140000e00120300c502c2c80e60040b00310030365269030504040d0b1300441c6d400d8000740e00204a903000354030704120040c0c20428040c0e000500701c4800192a50a001c000500500c1c024040d0020b4952003402c410404d8010803035400c210300424030710181d80c0d43e14122600e5408200000c0107030050402154094032107014803492400c0d01801142580d640038412002000c0c046140c0c0f041a4860402802207442400241290349a030382d159961407100c10005804c0e050000c0e0304c04010f6000d0420403910b940c080503d4540164145031031230b81d9881d1030404d0300517402581c2014101c40d24201315450070340360040c2c1441c0e8005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 485326798 1250 485325548 485325557
    0x30a050d050a0501063006090608010b01080c0301150c05011104050a0803030405030717090a0b0306100509032107050706031401090221060a03140d0306170c0402070609140d 76
    0x80e91066290b055071001e110340000318528220348100d0034a035008400091404e90b041c40e9400040c20801e000340c5503a580b00d0115240d9030031050000c401e00b809500e08000c07080c00e11710280e040414240c81148814441e03661100241c001c03d40c6d82900c951a2000000d401c4030090004240d009001e440301c2c0d1040c4107091191007008800500000c003c020f90340b18079041000b9604005064503050801194090303030040e0748200304046407641d0388911810300501101210b443e260703d0701c4014094a2200c1038850070900c00d0510a00e03c0b655000103182d8480003541c01c100c8580710240e0001945401070010040c491302a65a01042d1594035170b00031080440406046556a42e8a00c0d00c40128445d00d4542080342c00010143d030380c440550700420360884409041c13504030316500e031540442158482010243e58004040d50712000368580038400150113055980a056415001c050b552541d0080038240a5a00800d071101800440d42c007003550309802039001401284a000313102e4030b8442e035000100116 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 485328048 1250 485326798 485326801
    0x10f030f02072904080703180302090412031d030d0b0a050607050f1c050a03111e0c0d0e10080601090302120f1501060c020919020c030a0f0c171308030a050d05 70
    0x201000c601401540c00c01d005d24038104031030b1012a80031440b4880c00c010894800307800001a200c081d07540348200e020318410010800c1d401c070300409480d280c1420b20015802c019003050a060080304071220000c01610000e109031119000c0390f412145980590390000d00402d0030b10074481c01180314014600d130b00e03041d1064403c801c440282c000179030b05054000074009014010005000354080301e403400810080c2404e245400c00b081d10b402d80c0e80c5240200320383c00451351020f0820304001d81c41003070165007000070000c0904004a0444e06158000404000c05000070800c10790045503517501450300a852800781041281c10b00b65140e034802c0d0000d44900c42e5008228aa105039400241170390030039514202d602025800300019400c2c00341c09890580c22110131488084143c0c4014001c008110340550380744d80c82d0400280100385950244414450200da802000466618502010b140844913007910381403208565002071801e83c22102c2c8030f100000314010265006000360001045407501400903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 485329298 1250 485328048 485328113
    0xb0303070f0c0f0b070b040c05090a090219050105071e0804030627020303030a0908091009050a06021b0111100510050f0d05060612190c030c0e07080402010f030f0207 73
    0x3d0202d4403c1c982c16020510420300060891651550482e00803000380e480241c440000035140f00c419250f10481f20f03580c0d07544400f182044018210615000002c0d40740852070500040d02922880c40000c0c41c007500389106596400e8000341d022029600103103a180ca4680300e251020007001002440c02c00c42c3e16540341c00c01c111610511b0b00d00d006034054003175802d644030130b160303180941000c02003156006001e115041c2e5030303180d44603821b16004007540e40181491403c1d0a0050180031a00240c0840d00450b041042c80c20084106403401c0b0028645151041d556a503c07a00f0070144000115003031341040107009081c0c11130b04034281940e40454915080e07a00d94000c015414200d10b200900360b41003007000032010320700401603900d60050344055500c421508440c240d245000c03d10201d42c0c159010001b40309110400b2026400742441103c011103070300b06888003600c100030007840241009059410029154400e401583c2880080c0d0000e644645540c940000c0d2010035640d980924a45011082c61 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 485330548 1250 485329298 485329319
    0xf010f091805180a020312030702150a0911060f0304110a08160f080a0c050405071106040b09100606020a170c070806180c060406050c01060302090106031d0705130f0b0303070f0c 78
    0x5617008000305212041d814240d11681c00040c95101940900f603101c6860415003d403203403141c501c00800050754009860070010078400441400e0041e1420f00451132030188074011a5085604443c1d00c1d00c00e40010b100182c0f48140ca5041030389580101c1c074810125030002c022000c20303904240c0b10101d8154072080c056507203407550003002c2d000c003114140030412401d1503072000d6044a2549040c1e0000600e1603070f0b41d4030f0400192001c0310000382807410000b20741030074040400c0052960000780000da2030031200075604c031010000601a902c003440307010540301c0110100d03240649018152001c1a03503503040390b512020308403642454940003000e040c843c0799010405949604006200030309003070500c08100c4550b00407268401446d0368500c1c0200260f0394071040240202103660700801c0150350311078401040c070590711645009910111080c0103669410b0600d080c041c0d1000c2d40014110302c00160400540f21440030345415020006600c014010200c038035101c084c2c069400054000c3d9200c04a41 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 485331798 1250 485330548 485330563
    0x50601031b09031104020c030c070e0606030c04060e010e03010c20010c0f05070512070602071e030e060a2006100806010e04020d031e0305150d020f010f09180518 71
    0x24040340c002d1000613450843c86071400805840141841c1050588521b541e02820300c0400c1944000c401304041d4a602004940c0500b054a865085081c205102c507594090b6001d1042485200c03080c2c0640369200d20414144800020000e00071203000700e6000c7c0400011481c40398598080b60410090140305004140c4460741c19521100c1c04011030808071051f400510781201d00e0f000f83c4404866140511014000e0503005840050340c46880f4030304510701d100c0400e62030724000741080c191800319800c034040011030b100580d17a060307039245143d008850b14403070102c0b41200407000c8004240400300000790148140c0f52517003240c0c80c0d543c690944a54a01c030900c500c0c0041c0700c003e00081c00509220f20050102c0740301c0d04000d80f0030102d1120300d410283d11b024030304001960303400400800c2600d03004c4041e00c240f416140c1000c844001d4002c283d80c11694402581480343c801181c282d05442030142c40002c002d8240117242000120300103101510040d03c1ca8603800081c101520340c50035000c210701 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 485333048 1250 485331798 485331851
    0xd15170a0b0a110d020a05030f07030e250e0406020a0f081b0a0302070818030709090b040209090a02090a0e1e0319050c03040801020d0e06010f0e0a02091305060103 72
    0x710070700d94803038240201034030a4104800d0046810f100d400d41299041c006040841203a0300c66035241c1ca4542c04002e02d120005200740109400c00c45082c1c01c0400100d02544101e0307201d8001048030420007110507078001d481e4007065503016000d0800050050307507801b0f03003d00b9103682e407280e245901c403900441f079640054803c3d5007610341600a048028400b140203006e403011505003d0300740101343c1c4808410750032420104201d0183d10344c10207000d28082c81420f01525a0003810010031f242512981d4180900610003401105a98049086804100200901039034010070944d42860600d10100c0541410b2041360307420300c2030304080300700c1110701d2050b45813a004000065081070613415510f6145080c002442041c0030f01080201842c2600784010000b03040a000056030f16411940d0200031038412480c68041ca4001d9001408a8000750700313100e0898010b660080d1054a520301410300900c43d404109a000c80300d00314600c01e42040340c002602c140d009803070410103925850303540c040b1030f030721032000c0e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 485334298 1250 485333048 485333063
    0x40203010503071202040f050a050717090714040b04240e0f131401060b090111030c0c10020309030703031709011b05070609050a0506040b090705010516080d15170a 72
    0x2d111014180134071507900382c00100045400b0401007200e03c11100141c84066250740c50310100045650000c45075004501800803135001490050411a01c41b12a0301070461228400c0b203640165517210f401c000d181000c003c00800c000c0b1503804820034040410810700c1c0200c02022000142000d0112110b84140c80d9014200d40320303503035201144c807450040388040702c2426a020118482020901c2a000909020824250745907078520003d0800c0c0001c1540800c01e40c1b00f000315442d00b03d0081041c0d039402005858150b0003002600d010313411401060a001d425218000001041c150b000381c01e165202c3c500c0240d8501612103100300c609a5100380c47c04c0300d02107502d0f1a00055540704000620b00341d40070700d0001503c0c151580d100c90401c4c005220650346a8055014402841825100141c21400b400010103180307103001d0001c2c015000b900075007100c05110046440500c24114111210030f5000700003045407400800b00100034100a008854800c801d0410411500c0c0d0000313050210960003601 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 485335548 1250 485334298 485334313
    0x602251203050307030219030203060f0f18090f03120712021305010e060d0e0303150a03170315060a18090b090a0221070305160801060c1103210d0b040203010503 71
    0x81c1540d9980c409003040d01019420400981500c06641041c8508500c0740d80240c2d807814010104000421034a00e02441800342d5250b85407155140381c7c0c0512281055003502c2100d989a14110781000044164030049010008180c07445140c000d8001740b107a031251f03c9040c445041001500304034000c100c400200c0c900c5d040c009100710760190702c2045041b0401401140703850300401030103040c0c802041c51246c4560020050000c020714032407400740018810758001d400343c1e143d907c0d404100e00107203000b0600c5080000c003260b0303142040b03850b00d9074060014007000c2c2e0798be00005006002d081250240000b91150484c041015026801039000006004040e0400b6454070902c8034000e42c00310041c0c0001c1e01601012201c02c003c1504070724858142f0761000905450440380c484000b00c01100c0c094100500c1200501030705401c00500403565070461011200100c100703007c0380c64038041d40c1089140721402640a54a209104000c00b44a2200d410a005840503802071000342d001c2130041542c5a004100c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 485336798 1250 485335548 485335553
    0x12120714040806062806080a0513050a030c03020715050903010501060212090103020c0102160807060c0305011518050303041e05030d09030b070302070b0109090209090615040e0c030706022512 84
    0xc250307540e0341034000d1608220700d4005d500f00345102a15481140464021307401c001600019226003035004011701d4048030350308a96581c0c1a02c4864000004050001680d4400203151017007081802a24070102c0c502c410259074040903086800c900c3e01c26120b0360030880007140907480810000c0d01900c2e0bc520090074111b07030700019006134011b24108103080d0342c04c1c850304a032a03a0b14000c80a80501540c065079440e0320303900b007003010303142815200700034107041c43d0040140080380c01084844520501e04842856828500c8441c0514664041c0c1d030f0622010902107030b0030b203002002040786582c55402e00b1040b82d96000b0303d900c40e141c4404410202c3d500b01c004101295220310038030303400051864010300d00141d0781d481c0c0021883c2a0824985951b54030f40150842c20b0a2143c41c0d0841d031420010245c500d80300a610301c20144102c02180030350b8480401c142c8004c3d08011042106400400744c40b0503c4e1104802507444480c10500c1a0003120007808900e01c2d10f80703000050079100c0c004c00c80900d24a154 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 485338048 1250 485336798 485336809
    0x6010216050d1b0605030907090902010503040201050f0c0604050115091104061116180b030118020f150c0604031e230c011803030f1415031212071404080606 69
    0x60815214080d0004140c03e507100c10307041d980c02801e0b82d80c07291620707810000b022600d0f016a540080340002e290200c0000982e8121090b03a80c002e0f82480c00a03641c00c0f10100300300040c046c100700214140300e80010302c810031406400001d00d12030301500c24076402d0b54a40b41da0742915411001110381020411092107428400c602500040511000711220b03c1c2d016007410200c0000f548c0283c0c5941e000f02d00e000102c0c6280c3c050704182e220210300074460b8005146141900c0c1da0b200500910030a0000d0342d6054603186c1003048800c078452148a03580790750030f40c03101c03c4d2a080112412800a440c0c6880b80c01c440294002100150b4826692118145049061651036450410305542218000d000c625019a0300b4020111110600c0c03030040da08000500c0c000d02a11000d0817508403042c00c00110300804500c2c0903003070f81c0c800040f81c1501c08540710b90b000700341003103c040d400003994540042e14694614101c1606406840c01da56003040c41d0b5002c648224290140c0d006080854100350086445841d00c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 485339298 1250 485338048 485338069
    0x50318120118060b011b08040806011502100905010f06030f1502070305070b100510021615020a0605130b010b1c021303060e070b040801060e09030408030403150f020403080408060601021605 83
    0x103060441c0250f940130015041080c246d1011140d503100050b080c041c005c014000a80100103c404204214280300006074a900c01d206001e8001030382c60350350708240042504031001580d108582005225101d08040480b191001020b8038130314141c010441603001d407482114403040d01680d80f01d040030f83c42c0d9106120501c016220414207104003c0110f119070700c41c001340340f4040c3c0c190000d2200d12101c42d080b548204c5a50700c44140441e0101301040825000710f0820186903100c2d0000840f5640c0544101140030900340103005241810004175800c80104010300b9210318910301c0d0303485419542404403c0c0d229450b180c08520354070000c1040051200c2d000311002042040c203a0340070b5030300e88040106a8105030300081150391034410400158280e0560150843e504401440c60142041e0f03400d40d030b9210b2403000414400c440d42d01c0c11041d018a6004141c100c0c00c02c5410740d51941d0302d080c00328054103c0d01a4507802c1c01524003040d10340d0b000298551304288008107207000750385000e0030000d10408 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 485340548 1250 485339298 485339321
    0x3071511032511010908061303140f072618060705160906080a050a080c0a060c021c030e0d08180a06140c210403030905031812011806 59
    0x51240121078080841e00c040b80c0c0c400114150442240c0b410020341043c4484609818011500820f0041c00004220f40303600c0400c1d0700c070304103107a48280342c12070300c0c002c0206209125040115091045a583e14018240d2600400030003540d10038031000c0c1600041070780400c5941c00300802001c4070f0410b400c0d5550702e4150380100313043d040c82e40e40c4d21a00e06110b40c02e140803080541b1458207105003d0980701b030b14050004900204122140e540e10565101c410a40207030040790085850040800200310325010158041d80a00c40b18440d01c0c0c000e5502c44000004040e100c814245141e21203100c0d208000e00340320740340c00509a00100b10005d07641004060900000a8588a600c800f0b0700c0040000803100c0d8403942d00043c494040502c849801c040280c21100d200d1410059240004401c0d0090b80c4001494100003c1c0b0761280d150640041c07840344030090103400046a81126191000c1a000b0440d4083c3c80c000b00c6080c0b454211801c80c1d100100401c024003a0720510400705a080d8000142c440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 485341798 1250 485340548 485340553
    0x150602030319020d0203040606030b10051e04090f0605040507050d0f020d020103150b13090b0618180c0c010e07081f0207080c07090b030a0c053c0f03071511 69
    0xc14040084c2c05a80c000c88048d6203946e202c8108108000012481c1907011041c4010703403010070b003803400040c4601040fa00c100070000026584c8643e555690303100340f0889602410a100c1c1185d00d240520103070404540c162540e0190500c002403034100a03d00d0b008055018403030304078095a6a0030050310400042c010782c10590388642503420581e03040b114070040d0001980c82c2d40c452085a155090b03080306034001005050822401c4182e944500e01603031700d21411003052401c48014030300400c0391001000910310b18003034660148442200e9040040c000315076100000c1c0983c4400b0501c0399982d800e5841020155440750088100340d400c460040441400c2d0348001625251141e02c98401c190494440c01503180c100a2080000344103900c6030b00034049041d409041c1184036034450b245003204d14824180103c0e613002d0030060300c40d03582a504600f80041c80303078000c1107548001400d41a9000c101d0340f600440c134402036442c2c03510b000103600b03044a1074148005450b1024520450759111012401e036083d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 485343048 1250 485341798 485341807
    0x4b06010522090c0905090109060b16030311070311010516121d010606050c060109060308030c091f030608190804090908120705070204050a05060108040215070b04050309010315060203031902 83
    0x60030b01d40100c108200e015900c98442a04000400c100c050060b80241191b40c9401802c01c08802d102050b61541e400840300c288001d81541010380250540394a820700000000461008241d000f051400034036008000801082d03072a10a0500c21103029010741e80130900c0c4292445000c400c5402286c0920140c20362820b95410301d44250342921659001800072510103c1c0e6800f808a0070021a070041c4004001440185c0c51521080e40394400503100002c10000080c8541e09602c80c9480303024481021804c80600555500300100140200d000e0100c4a024407910400b250b0310382d070303100c0c40e0164010800e030b8076051604d28514000d149101c8121441001400050000c502142131944030700003035210950f82d0405072040204a07500141040f0840d4940002e0040c26640450b905910903815191000440e644050010007070003a148005c01905024042008216010000d0040d180d42a2000d1054411000c15500740d00d895000700030041e8010f00010307440b195440020b4a00115041d00145403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 485344298 1250 485343048 485343059
    0xa0e0c09091c09030305090105030c04030b150405070203090a260d030c0806060a0804200d0303060e100317070819030e16050303040303084b06010522 66
    0x288421650100c0c40d0708031020b150300354084014682d0011902e072519144482c10f65802401e180030b8039507541c1c104000440052007070184038049030003079500030500c0d214920f0000301c4600b0840c2c29091507405681400082615030380004155071281d00c0013804036800b01d0034a241006045e49204252501030942c51520414810502c090204020700703540100d060804500003402840000d02840c4c005e060070844100490350041074107800c154030001c0141c0c0c44036603000c0c0720743c011202034031250310910003030400c810150541d1281e002c0b144991002030899486422503011b41c0000c0c40064458980340a1880f110103a28005000440c402c208043c00c6c5090220310517000c400440c20300c0040303035603400400c803400000c00c441c0144a08407189548074a0810022030303200d0050340310090600c0746140102c0d00800141540001d00064281840319010007046014203604913515000c10040d040c40704c900c80f4001d44070400b44500c0701031b1109482c0240d0550380c130100410110300045a441d600700082403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 485345548 1250 485344298 485344309
    0x40209030127050d0504060c080318010204171e0312090f0d0c020f1002030a030c0e0414100f0503060c16050d20010e0606060708040b0f0d0609140a0e0c 67
    0x3601c0140c02d03405260396003203183c038901d042c82c400300c0103061000601003080740d10f6105400411041e401100c0e15200d484508480c0030480604030494181d50001c00d0101c0c19006540c5401c0a44030882d003181e50070302c20003882c1084820132000f2800380e50403c008241c0001e0558003016001800d110443c0d01180348152020704280710040e4400010f6130025401081d894548444802d88030200c0300b034030240c059a84080d680c0c1c82101a044103254442840c0a40e50f8040d1400c3e505464000d0401d0200344151007180691741001caa0840a041510300c1c0458110840c515030310581d04c014004000075200c140a40350190040b4521420b510300891501000400501c2059001200d5895130500b20301e01180c6e210140c001c4002444031689464144800302c1c00004481f40c00c08402e4560700e03910f41c10381c20906054404c2d5085100c071000c0000341400c550400c40010484100d951008120a5448807058002d90300b003403032a400050740d07d034003080e41c4402e80e42c06113201c40300080480e280b05111001040d07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 485346798 1250 485345548 485345591
    0xa110604030c09050109050a0507020d030c0c02090c0409062c041e03020607030b030f120a17011707050907050702040b041b0206061207030f03080403122d11090402090301 75
    0x1180b0f580c0341e40c010002140726003d0141c004101403010f00c02480e0280c070003941c981c0e00b64883e000f0151910800c00d54113000325074010405401804007640303443e080c01c1d08102e40c1c2c040e2041c05a910300e0954000703044200603440c2c012030003600d0000086002c895800c20012240500103981d05d501e01629000000400d00d03d5090091090300500a28070f00b40201a08540c0014029030094110103404a03d8850120301c80d80e00b810329902c3c0e6038450700308401c12158091840c0d906078100c05da0368004591a1400400812040b4410701203071000d42d1035a0034015074510589000307010038014800080185029000800741c0103024000041107080c410080d00ca030807140c00c030040503800c1074003484145d0514081d1442040d4041008082c000e00c1c5940d00c4c8031403000aa001340410848402050806210b2000f09407420743e10320b400d1001040441c11a0300600340140c1c030488503084640c811541ca6442e0140100514080690606000710703241800040e602c00c100c480d5140d5607907500041411b610034201c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 485348048 1250 485346798 485346809
    0x1180f09050a020301110405060d020d140403170601020307170304060e030301090c110c0f01050a020304050312190305160c0c18020705120301080d120e0a050f0d03020c0a110604030c 80
    0x82082c0703442c0f07005140c210384030700f0196101314200700002d100940301d103c111080d242e0001d0b0016910005504580003c0295058031104007800c981804185a481084083c15030041600281c20303468800042e80c0c2c910449000800c586070170620240b10343c40007406107034007030700908004c0342444804454906541c4240c02c000641e40c0c2e500c10b0711101641c000e2810203400b4001005002c04c034450701c00075401c10a0303000054104030000854941c40da100380103560060030043d080381c400c4a032100c82c840301c030740107400c0001b14541131010f250303404e80c03182c05003500441c0e07030305641e8103200c641540c21600302d0580301054079030040441d00003614003070f10725010b0140e2a64030001a2a4496450b02506140f01080601c00c80c85041c40148580d90f4082100021260310b428801c0d10300f00502400000303440c5c6044241084c0c041e40c102d0070140140451054018040315081d2400316000d40000e9089008110010303d5543c005603d00c00020107040940c1d50b101030081810b400d25542c3d649020b81d514064015 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 485349298 1250 485348048 485348053
    0x50906130c081812071b0e1005040b01020a0f12051b0d090503060103030e06161a060901050406141504081e21030402091504181101080f01180f0905 65
    0x2008030601000c49200c0c40c03003a1140c050480084405102d90325401070f80405001003a04408090a2211a0300da6200620108047c15400d240120422203104001d2103030902803814111503c040350310208003030f030710154480c0303000c1c0d070000e11920340f509140700c100403010a2100030001202a045038200310406004c4410003010795541c0c61324000e0048132168855070090f071084005100203900301c0784900c03071000c041e228140c40e00c1d124005d4488030100060003400500d000d0410601d560840c00d0b46a1150500f500c50740d0382039a8810074041103511074414141003451b20803040d80e03645414a0002c22444046100c582003d4960121038104081c290705044000c040b0b0418104101c401c0c400004203d503c3d9006030965000c48244210911008000034030501c95400041e441d915401c0450300e4000c0701600800440711980c4071011a1004000c2c1506d80095080e0382c1e9055610421800780300348035003074010403031b646055892a045800349400c3c41a940c0c4408510311880610700c1000d1545000300300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 485350548 1250 485349298 485349301
    0x525112b05040f09051b040303020c0a08030a020a06090c2706090b220f06061107080304030f03050d090b0a020d0b0d1101050a020703060e0604021002030310050906130c08 75
    0x2034001440c40181620024403105000c200080c00e607410700b00302100c021200101c3c003552048010650b110540590303d10703240c008a008005c1c1a03000482240300c0c0d1054900100301903d4100c46540c0380a80e011580059003d400e00c0f60001d00ca0342c0145482c244600c0c41c030350b24a038036004c030400d0443d0070324003016104c84415843c1180005601603900104503a40081100586410105055807081e90888040f43c0d0281c0604542c403400750708c101a140c02c44c4904004141d141d0718001d04400c008203c0d403503140715865001c180880080f0843d001c890780000341ca428400a56400c0e1201e81216070300014041e91f1ba0549070200d1038100c0c10310300c101c03000c950042e86c1e001c01251020032100d00c00012809031415001d17210000e402525801c1d801c1c00242480b42e2103600c01541246400480d400047c0f0315030418110440c5c002c00026441c0c002c0780300320783d08a070304440582c0480c0d407400f00311600e074401d20038807200700b14500704a080d994006802419002c04c0b1440101040141c544000383d078800101c0210 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 485351798 1250 485350548 485350603
    0x6030501091205030f0f0402060705070f060f170a05040813030f03200c041d0318151312020a0308030907062003030109050901022101051003052511 65
    0x3103070510b2401072410002c1c118204007580318500c07580101110303680e5208001103025540c504c010b0310101c691001c203c0b40c40355100c182440242043c0d12170340022a00b40210346201e5402000c0c1a50303182d110f505012407640d81c0c0d109980c0a0320001c0d00079224410200725649451071000e4001e00030318000c0130141442d0b0907030f142c002c0481c01d43c3c00302440c1c00c5042e440c803050303005c0010480f8400ca920803140072a1640080202c588508481341c42c1000e144800503181c81c0600f2001e031020b1050303104441503010a003a901c018102071044682d0300c2c221140c040c00c144410040c286241540c00d001420114581e6100d0b40c806080c0d0b881940c0406866100071010801590701c02c121500c502d035500742d80208000785904a55072800103010301c0c0e00d402d03144c100242c1112001d40c1518409051501c1007581110408070100702400203001e840d0140d030008000031007903070190040d14002c0c070260044004e03840a00700d00c1d602211100c0c00c03136010090300588000c2401001c025141e0300c0000c8620003540e10304441c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 485353048 1250 485351798 485351813
    0x5030706062402060a09020f0a06020616020c0a120c0308071a07030209330f0a090602060c07060c0201060317040f090e031e0705030301030312051b2502040603050109 73
    0x2d881c1214881001c0300c0000349a011805a801c0307a102900850040c10920020718103e8040340700e1600305401200000701ca03940080c43e5030040c1047c45000c0c1480c0c0d0854000c0341c0351489100ca0303071b41161000c203080062255100e064452a401514800e8080b9100e03510303940c07290b00500e82551401405d0180e16064800040130741e8002d401c50400314078102e500d001003204540340c05e0031407403207410300a45844491110302490310144003010100d5500c4031407008490040d000309060800140300d909000c91880d0002860501900501240c5405d1801d9640c130000034210b0034004130219502c4043c00000505140c40141200344204d108588950920101d0407103810168040444142020111030800c071011048840c403090842c0f00c901509000c1c07040343c0b103a2254000c01482880300100000c1819803007403c1882400146000341304030340b200072043d044c45651013030031503100c2d07810002000703040070303050301003640700651804501141c0460300001c0848085a0080d42d60b0f075141d182d2002001400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 485354298 1250 485353048 485353079
    0x50403081602010e090405190c0909061506030b0303030a1a1f0f0e0d06200706020403020906030f1005090c031002030a050c0316080604090209070c050c0307140415030503070606 78
    0x945d146020b51a1035180d155884601c00d42e003595020085042c00180040040c00720f014007a200010300486105150240040112019076806000c44801c0424000e20074080c010b01c0e608014021401c50710345a1800c0000e01c5c1030050203c0e401c4481c50b2702c41c04d40e161045021980f008483c40a0342d81821403901a0640b1943d0303035000200080d01c01026415601d8900109080d03422460000e0b6010f000700d009200d4182201c0700c0e41400101051034801c100168000b00300b680d10981da0708000f929030400741680e07000b003094002c590350001030b12005105006e9200e6079212000d402152400084640030071300704000038100d41d03071041e000000c0040e181d880c0c0c01102d420445540310945540780c96090311004005000300b50007040744160208001c4c0d03850b80c1140b80002d800030074400c0c141c289450050425005004120b8041c001d0341c0c0100300c0c1e840e002c00e00b803040711049810394501c40f070300c5810400103050b200c00050790b40005801c04000300d80200007514146103c0c0700c1c00105076040c00580c8102e0703680c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 485355548 1250 485354298 485354327
    0x150612030301060305180d0f09171e2404060b0402180f0a12080c0d140f160c0b031501050f0d050603070b07051b03011a0f01030603050303190513120c0305040308160201 74
    0x3022804d102b50b1480050010b8002110000c0184242c4140d5070043c200200d404140c244110980c0a100c0fa480c91702035200d016a110341410406840c030035040c0f0060b4041d00e0840c0f01441c255036014010390914646001c0b50b114020003000e40d103610f40200d1150294400700564250748040b81144a83d00200003564412266007030110f6101c0f1010741d540d045200f0054100e044c41e0740462900c2283c903100c0440c0a81542c040b000b514501d484010424040d00210b50007008100c04940400700c55001d041250006c00484071000e1404c0c0f80c1c0603500c4003501e4040c1019070144111a03002070034040f02e5000e4114240304001421400080c80004103003505600c2906109074500280c00e00c47c49804a2021003000742601c401c1220000c2c10010782c001c01a60384080d0580c00b00104000d10303649025500e10402c0c00e03c0c1400c0140b5182c40c4000201c0010100d00113003d02500c216040c106801482c81e240454400d103030191400da2641e441c0c1d0040e030090718000a070480c92f08500e404542c3c01c04003480140c00e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 485356798 1250 485355548 485355569
    0x5130c0f030b070f0201060510030c080f0123030a0212070e1008100e0102070c03030806010311070b070e13150f17100509010209030f150612030301060305180d0f09 72
    0x74110b031038525209502030900400d0201d103800d240c070298001c2d00103800414008000100205034031300003902600244003010300003145c2c200000e034000c40101606040e0345140302400311030103521283d0001c43c44192000303a4544213520381c0c0c000503a02c00524500d060000c0303000e44061450038204180340c03100540103000030380400c0c2c000d115800c00010250440c000d00d400c00700c0c0b0b00e001c0c0f50440340203100c0d609004d0300e1015101c00c08428181c0280303119000d90000e0342c0800510460340c4000e10a40100704d13000f0044c43c00c080c00300e9129817248541e840c1c0404010201880014081c011100315407502c4c1c900b490307500045c00104031504002c038902d001418001d400160700d40c25074132880c1e01d400324100c02c03603810780d81d07003010074017007070b8250305640d070400c0040e0031a8541c025401c045541e0743d48200b03111080da1800000a110350801502180280c80c108004505507401c16006401808005201500b400e841c0c14601c2406c040800030024901342540342c22010203890310300203000d820107801001010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 485358048 1250 485356798 485356829
    0x501020604080307030903110a0b0906091209061e0d060303020d030209010f030905030c0a3c0611070213020a0e011b0f020312030c0d14060904030e030a0605130c 71
    0x20b540c40c021668050800d14001894007064682520b8150707082e01526010b210301615001000500354115003c5c0310b1a00442d81d455540e81246603407540c160f400d0102c141c105200b804a1070505c4006071010100d9103c0b8205c5100d295600042150005402500b0350744e29601c082003410380500070484500c0c40ca2030154504100070002810a0102a1056007015901c5850750306128042c400d030341a4241100c1941d0200005060409852004c01c40c242c0e032611010001d141e4000441c100c00c5000c0001114000c01c030001034a50400078034581d1102840c00c48200481c01c0140e0326802c80e03014554011030010b8035580114801071001d452001044c0c180f002d5400301009012404842c280072551250500c4031400d103d202003420b00d41076030b000c59002c070310200030b20141011000c00b401008410b11020000d070305055211103074003281910201c0d00406000b0200300880c1c45002e9466111201a080382c6900920340e48a50888404503806001c41c040308010b0010080c00c0d511400040255803090102d6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 485359298 1250 485358048 485358053
    0x3090a1106180d030201090602030a0b09180d0513080d0c120c021e01120903080712060f060309060b15040f05060304080a030e0f1c0306080f0a08130812130501020604 73
    0x40582500c501d1040c0c0f5800f842d07408240c801d420960141c0e03800700040d500c034101041d007100900205a4018070411070301e00050841079408036a0341203105280000c0560070b030070603030541e10b5912410f049002000c0080340410920780c10800c032000092503035a02000e2070100d0800604480002d1052001c0000840e415800350780d910a8124806284034111500c4030120310060304c0752550300d200143c1150612090030240760300450050301c41c002540751109690181d04e00c0000301e03a035500801c58000f500880501010780301c0d501c4100030700e210300701c009011201340001549001c14000c40c02d800100000d000c0c041c2c003403a5598200141030688d0501e00f0740c2010340c1e5042030741c05003030b01c0d000405a0350074074150029010000017518903590700655042c650030300420080d812a884500010a0610070001005040051034140d018011800b9002c16421030740e0709950b961020b202d00b00c921b1140b15020807540c03010b000c00c44140c1d2401c041d15a444144115110044900d139111505542086040002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 485360548 1250 485359298 485359327
    0x206090c040c120f090308091f09020628120606020a02060304020f0a03030305220320010213060206061306060906050d090f230c0315180303090a1106 66
    0x8a2490840e0003048002000a0407120010454105a40382d410010130000d003220b25403140c0e15080c0645d8401e407140d91003010007681c8981c94400490400350520000c90800c01540c403180d6110310003454140350810300c8509a026204030022254007032100c51004007015001091419070000b1040244040352034410080d442e0200c030792000e4068880000001d00f1540c1c2c0d511040304000303004107030100080c1c903410014000c00b0300300c84102141c55040c880100c0900b0000310f060b1429415691800e551001d10b590426081c81c030000c2c0c00701590280140741101c542d01503c82b01905031030303009280380d1508000f0815040515407500402d189031601c10b0258030350082c8a04161040380c1001035031b40c0030206071075000b8007100700c2c040c100c0308222841d042007111a00e446d2210541a900c01c80008ad04a500c81c0d403664100b0310165416030103580701c0f01400541c05074135580a650710103641c0e184a144c0b2031250541d0700844400b4040c0e00030104c218100520303c5100780404000340c80640c100341d2241d05161 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 485361798 1250 485360548 485360563
    0x8060d06020c0f030c06101212030902010309021002010e100203150d110d061d01050910180c060f080a0227040f060e150f03032a06070504060f020609 66
    0x2000d868001520b46200001005074a0381e1086060032241e583c041700d40d0782511003505540c400c4a0019640340040c00710502251403042c135400c29081075032520481800d500501048808078149a10b4400541c00759855140800641d203043d0004250449070340480f504020000040e41d000c1441801400300c0329a044100b611914010341e400681141203040a090803024880c2c0183d00c0110900b40808011850f0425003c481c0310310700102d0900745842c1e045080c2c0302c2c00c803556070301540074281500c0002c3c229049203811040004184000a0041c0c440381c0300a0050340280d004580310a81c0081d080d903020005c9540541454000c5080048140704045c51001d4180f01c60222040e0000301c440070358465010740c401c0048060200b207803a68550181d807090341c04480e8031081303032000c2d40c6001c1c10741410201501c1a00300200139501d00700bd50b02d1205080640c0031004400003c0c8821503099005007007094501515a68a0302c545440c40d04400804000315400704008540009003071003c0210b0001d600d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 485363048 1250 485361798 485361803
    0x207060804150507020f030c03121e06060d0b03100c0f02060f0c09131d010c02010e12071e0b0402031902030607031d0106120b01080303060d0609060b0d12030c08060d 73
    0xf16094503281400c914040f07524000c0740c42400001044405a18000001d1680580c0d40c1800f050765600c00d00580007114902610002e03403024400060194a408001484c0383c0450000020b50034a100c40460f18001e02180e0f4440229924041420802d03040b0342e4900c00e103105d0b48010091407501a01980300b000003c1c04800d0380e41c0c070100f2034500640c0c46600d5807041210040e030402200c0180c003c41c2d8540081d114814a0319464140002510351040c05500c00c281618001050807107280c0c01c0c140815805107506a601807509541d04541d40c1a0a1079150302ca4002c3e4002015414240105800e009510341000000c20309a9031030300040c0c0340410300c56400081410000b50204400b41c07040820a41030164010a5117003030300c007103500300c0400380703504400d8050221882141c0c2c80e002c410703540b417100b510001c0c1e011030089000c0e40040c6581d08409401d07072003410041402e07035110f0049000c0c1c00b603810084440c882c0440762001d481740c0c14070440780f00200030f25105182d07042100103d1258890700300302 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 485364298 1250 485363048 485363051
    0x150305060112050316210201050601083907082b0218060a03091415161e0e1801090c020a02150c1c030e0d0906020c0108190905060106020706080415 65
    0x1594140b120007001d401201c0515200358420080d1200c00a000b080115490350103d6154ce020038022040648500f50007441e0003255811082103603c0719522003070524038030303d401004105800005940300c001e040100e64900c003121510700d21295056a2250103107850036002c0c41488845941e4040602484000704240d500584e0b1300e0030200102c000d42002c0001404030000001c0041c2512400a00c501e11a410322004002e61340b1035556840c5002030b5184244001241f00b0400483c0164940e0054804003041c2800c01e820364007103001c0780e051108594503d04400c0c0a4004020715010340c00b40040014051001d441002d4041e80000c4c070914150204c18220304000c604400c00d814200304602c2548680c80c00c11040c44402d6200501904500080c071106000d1401803603800d9004134040000e031003442d00501100c0c82d082004541084d001007194400240c12040186041080d100340340ca001d0084020303160039030410300041e19100c1154040e508025984c0d003000040780c40a600c800c03076150f04160 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 485365548 1250 485364298 485364337
    0xa06020a24020d0e0c1801030c0512070f060203040f1e090b06071502180a080a06110f132408010b030c0903030a180b0309150601050d1503050601120503 67
    0x3070800a006920701e03460500c0c41c1c00e01e2100c501c2d50009250204542c121000b45003010903543c404140c0740284801045030b1280d10084c4114503000001c0400604003400320380640356501025103214405510805c0075800000c0e040c40a040c044103404040c208111455044050034603400000000900c03070010010360750351100d0300f1552040b040340c1542d50030032060f840795004038135030300001d45c01568812084c804c160004403240c180541c00744c0407580400c0c06025000c00b1a1a40d0340034041da420f800b40400300400c66259905640d801802c50404004107950706139080101d94440c3e504080c114051f090b020030040740d08940d00c80b00460540b40c0700c2c54001d0b10381e110b03507602c03147d1350142680083d0b250002103036042c4c800d9070280100d080c0c021680100c401c00341e0b03105419a01d5100607144104142c0020382041101205465416000b00c0107144c000d2411054160003402c89003613540d594058401c00c0c0c4208103000c0b041210601401580160400d2070400e41d90301036030307446400ca034544540090b91 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 485366798 1250 485365548 485365613
    0x11040c0e0f190803030f09070f0b0309160e0f0a0203010503071a070503040b030f010e06091305120307110606090601091a072010020c061b030f070503090a06020a 71
    0x1850040c100a068070142c02c2c40340c59041d5561260002c890700c95045424000080c030741040007583d0011a641d0050142007941030040c1c00c041a40000d00d1910310b841032045000d01008403161103401410042d06441f164200078140c0f620800f0050700d07508409005100520041c1c0d0042a400111001c050002c80a0320011005070f403940500a03000e00103000100d00040c0c000310070710045203c0c400c14412924940c0e215401e6402540050f5035164011401c00002043c00100d0103040c0e115501030800c90f002130708508a00981c582c0b081320a00f0000d00c84480e001400c060421000d0f400c11021501900e251902c500020800c0c1c005110b842600f0710344c0402c03414003003500e2080303860080c0c004050541a0408050103004212050003071030145c560200c0805c82588042400110500b0080105151161300c1b82c3c13a050031030107401003c10034002000018204040d0000130140316101303101030742e1140d818004200c1e0341d50843d4021000e54109491190003e80d200001a06036a0300d007040c0804a9200c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 485368048 1250 485366798 485366809
    0x7050a0909020a0305010f090e0c061b010c02010b0102161202041d010203010906030c05030604020a0e0606040b0d0e0c031c031a1306081b0f04020903120a0c11040c0e0f 74
    0x81e80158000d510005038218025807642040d41a1030071000035003401582e83d084107089801e41c48901c40309400c9851181d10f9403509800900451721084980002c0311181c503007a900311381240c4003200c0507031354a661500d080e50301800090202004002007604091801040c1e0341707510310380ea50092181c0c0d03440e4600d480307900d0721340d6040c24007040c0c0000841d165a15050008024022404140c843d40708800f0001994035000403498070903039014084854161800450928911001e003880354000c1c014400407170522040e40182c482545070315404900381802d000d9590800740a00c0c00c890003134101d042c101c40d00c41c04544a90940319030a1800065002d844c1c100740390b0044000079110f9200c554400d841c0170a1109400520070307540341c80240e6000c4401e15044000100c80d0f141d036540c0100d203d503002d42503490076601a120314007001e01610340845080818460940c0b20010100100e81141105414030161002801c0c85042c1541d0402440001101c040c01e8030105c2d4440a20400d480281d4640c16242e2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 485369298 1250 485368048 485368067
    0xe01090c03140408040602061503030a0c02030709150306051e070c02040902180411060405010e120102250c05033403050d09140f091f05060a0c02010e041407050a 71
    0x48100c1d60a00345444c42107a441445034100510643c00481c4502c1d4082825151101008005500d0a003451800350f40c5048006010399040c0507039000000ca02e010b81c0604914090400d0607101d4503421803030410b04540001c0d08a8980860320954030918101070f8048582040250401018101c803c0c400a0098001076800a400000c40900340151800031490701340a14801c1c0c0c0785002da14503440134002070340154811700340010f5a000040c0418101060403070210501c11b80003601d44111081c100c2401007201c01c010000b0751103000000d080c00348a495000281004074007410300e403800541d202c02c2c00007104001a4100303403006000d0700766030146910f103001154030200380e5181c1c0354212400b40070384002d44111849000e1340c81c0f2081d0030745004280a080e0180040c1445001d8070b40c41c02190340d1420030408031100c26140381001c50640c1d00e002c09444640015540c401154070a44001005144143c0080e400396007400b241e05003080b2841c0c0e14591005161030440e8030b40c1d20109089030390364074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 485370548 1250 485369298 485369321
    0xc030a0902101d0102010b0102060703200f0702011710170102120406050603070608040b04080a0c05010f06180b0a030210120501080606030705030d0206060d03030219030c180e01090c03 81
    0x869030030526030015010403151101d8518402d81203c1c400059003a2061286400c1c0140c05c04000030b04440d00070f80c40710242134103010418413500c0c4000392869141d40003007109038444001260800441d03901035030b04080300070031000c1401941010500710020340d459025000c1191620320b84840c01110940c140d5680d5640508010580e05260421a0040100360380640c000e001c0d00704041100b9000340001030040740d004030211f0b1155140d44940000342c00c03c1c2461001c01a0748284040480d00c240548103140e002c520001603582e10303140030080524900d1a80060260400350819880d5460a00700c83c02c6070340503942c21598000307480045403034640600510ba0400c3ca0b0000108207035000240d070351b20400d41602100e40050700c4a040540d540c8000c6a55001070340a140054003900b010340300c14189034420b04001d4185400051712101611003640305400082d40d0b460310003016588080d01121490008040e41409820941ea0301c0008205008848155442d0071005180a219901480c040074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 485371798 1250 485370548 485370559
    0x140105160f02040c0219020d06090c1818150c0201020d09050609010c0e0a090e0c060304030503060a091a01031d0304060206090607080f060907020f070602031c060602060c030a0902 79
    0x200ca1400c44007207894560140c0c0150314050300c00030441d000060b44044014101c0098800200c40e50070804026040c3c1e00c102e42c05510b9101400000e4404c0d01500054143c50244200c3c0c01014803415080342d16008e08500c600410300340703500102c2c584514920710180c6480300805c60800c1e0b40c80c140e0180c800c0c0d80c0c0c0010ba103460920b4000030710030042038040c003860074a0000d002d500c0b24920112070740c03282140c9a80d800301007560200054543c43d80310340c006410312026980540034840c002100c3e0341003200c0950120b000001041003a1522002e610007500da001010056083d4215242d580300c9894110703141070554031a0723402ca41d226128024001c4a540c00300b220354031611224029182d50040d24072800e0f40c441d05002c6078a480c080d003842d82c85071800002002e0720f952254200010540e01814a5041d402103c5120903444c00a000c40c0c000361006800950781c440700c1d080031000131112070702112107207440c1041c10f00010f540030031015001852010095141c1e11a812800d00810754010001d5119 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 485373048 1250 485371798 485371837
    0x170c0a3506010803071e0c12050c0907081f030302120c0a0c03081e031513020d0609061706010803090d0302031903050a18051c050d050c04051f0504140105 68
    0x3000000017050100d2051800005080e000e58170201101400c2200400100c1c2020040c42103100721008d03200c0c003c1c000d00c200c0d401486c41c10701181070203809441d0100041c01c0c4100304400c25140b60840c00004090b545501c20491858a000b03440c0c840b41c1610300f609000000d000c41040e4401c010030710185801c111a245541d40d00e02e8002135990103844980d05c24240c0c030907080041c00c4003105481c031500c40c10b55a0f044141072541004411905100f002030820750034810306242008038401c61020b04000032000403024100311055481c64034102a5502540c00b50005008940c001300c02d60703000303000c00c7d80c403050501c0141c07500381d0450040840b00030b40c20405070740d0700001541c03640005010707840c440c1e000c1004502c41c000d0a4003181c00031001420690008508030350b40d864107041002d040d01c1030b00d40a403d01454400c5c480135184160b03264800401c0229040c0841d06d40170040e5129030130b012190000038000c551014045009038401e00c010b60135041000c0070aa4040c1045941c00200c00249800c2c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 485374298 1250 485373048 485373059
    0x6050a0f1d1201050901200406030f0f020d06050f060c0c2e0e010f0c02060715060f080c1512150409150e01201204140601170c0a350601 60
    0xc01085400305ca881d0f08060070000c002d003040c22940b0942d1003841d140b510780360520304181e016118816145807155511140c0c480b40170f40a1018080070042c400e4086041c0d4038100c200300803135040d48000b03441040c041160032002880040c801102410036141c05c0000841c1962440305401446107640006d00503400501450798000fa007003800c00401d8960800b111405141100c11501000c5e00070341142080042c074020482820103425102c030b60341400f04070252140486041c103103103030b800f00f00036a014146040992800d5403408840c0d02d4000001c13403e008224060004000002e400044441082204040542c8441c1c10200649802200100440c05800400d41c010f110311003003a4100d510340600740c1481070704144101d03001804048407034201990300490390250540075104030340701d5240c020309100d5524140400741c024203403030665003c00c0000440c294145400c0741415407003201c04030790034013500c0c840c041d03109480303298044d0503084090f4516007602e80513080c01056035903210700000002d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 485375548 1250 485374298 485374301
    0x50f03071a01051302090a260705150f03070c05010525030501081c11010c090501110d1407050f16050a2403020c03041802090a06050a0f1d1201 63
    0x1203031803044040301240915480314010984081c02025804000105001481007040c2c0241054100091032050303010340e078144074807150200750101c460186d00d138003480070401810301551008043c21b540032688030b07020703c1c6826401d10a100e160a0205000700218201e00d1190003d850f040b540203000700918104025403a06d000000011000300b25031510042614504c24010141200c042d203000340b2200d50070381041407544103548144070410680003c40313422040c00f4003900903501d241e521829995400d0800042c0211035801d040415544104061040698451180ca468aa206016a85a0444aca00346003007191001001d0200c0c480d003c0b41201c04000403089400b26401264402c4089650308610101c0303000301041c0284040010311000403090090300249a0340035200181c915081d15186401c0150138a078000c607000c503901041882c41070800425490180ca82800c00c84e050003200500140036a46807601d000806c58910840c184580c20300c0ea156401e40c1e030040024a0402c200c0308241e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 485376798 1250 485375548 485375557
    0xc0c0c051c0c0305011d010b0d170c0303010b040603060518070503070c050321150108150d0c0b03011505250501020c241b0a11070b190f0509180a0603050f03 69
    0x1c1e10046c1124054401c01030510030400c00c900d002c0d01da42030901032138481400450301200d03254220b120401c05c1e2900c51800f07000441c0a400a100016281c5040c004020121181c0d504050301400e01d000d003692030a00300ca080305d50302c07501e5450416500d554010003181c0741100e00340c00814501c00440c0445002c1001c00302502e03039421360700500089641d08a20015440c100386a014045000a0013141441c58038074401d2507600350240440d00352005556078003040040d40c0c5e02c5000e07100800300050050902403140c081034481d0920780135042c00c228071702c0c0f0041c4800e07580d800102c3da8a40622041005030039015601c10165090541d070800c460315039080b003030349901c003045584507805000060981c2188000007001d410790046050800a1840c4107841e6030240074a14207040c480d07048001500e10040006203600190402a802400d007180005000011030291203c00d1100c24891750103c0c1d104c45904212407182441110200c0c4c6902030001c0c01003240f07420107481401280c0c03416405510000041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 485378048 1250 485376798 485376821
    0x50d1a0d080733020f0702090f0f0a05100504020304050703080d06090e030703270906060e030d030b010807030b0a09020f071205030601080a090519050f010c0c0c051c0c030501 77
    0x140c1c0d03007043c3c0919200000d62503980c0d41c2030384107201d48040b96900f495800340c5480c240c40c8020a1820043d82c0000d1010041280d810304c482035131740204480304404e60585504003903105018011810810342d4000030300e81030b00481c2c0c05680e02200060a120042045000954201c001c0d15640c51542c40410003510950140e00381190400030080d01c0070900100700d40c11a0b03003513503c43c80d03110710082285210705075003070201e4040e50120401040c0b07943c040c4110001020382c0d0b2540b4024582d08400d06041a0800c243e40c0145498154090001d0340c000941c43d0b805807040c80e00142010b40000080c5c502e500c0e0b904007410040c80884c04081081d505c4000f42110b50265040d24900d2801c0c110844945c88100c6085d40000c061034045114039801da0090076200c0e00c150140c98540c090345040700c04841c0d0511068070164442c0401313a100100c28411409084403910b00318000c00c40c55100c020010b15644152070003050903c00008440d200300c0c15510781e2647c0401e2400380c80741e590070014040c10340304150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 485379298 1250 485378048 485378063
    0x601090b12060d14010c0203070308070e01020a0b09030c070e04030908060c0706110408151005010306210305040b030117151e07410406050d1a0d0807 66
    0x20a0462030402503a0440624102200380e980d01e03a014020341004080048800080008010504400c00e0294502c905c01300d5000b180c4404143c1401403180102400810511102e40008071040e40c0c045417020b075154210078824007503111043c4440c81e6209002000b481d50096060108003040c0c2980158042c601aa81d03007a40030307071103170b00e81500c0b0001544c00d4040c01404000030400501ca82d000fa49050000114081c14203541e40907150400c3e5082d8012801031105600b00900080a5071213040600820310701081210b080182031030207400c2c06600c0c01000e000c0785204c131301010711460480300903102c0346981546a582d640d840d03c24000c24105828120301a00c1c0d4004c101c0100480b141e031041014000294000700803149003111504007500d500100038450b0070b200030202e21340110365140580f198000310580d0705207101d1078150007520f82d01000303080104403c000640d0702c00240e17015120951800078507801803164031800d0031100306480760030150b40078450742448514005000058040c90700c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 485380548 1250 485379298 485379317
    0x26191109090f0d08250f0801080c1302250c17012a0e03030a1206050d111002150103120f0c03020d11010603060e0d09170c0904290601 59
    0x41180e1a0042d210001d00154004000c8039180c0d803156a070650040d100c0c5820410030200b500c103103040d084051200f0f10200e032601881d4040342ea0f10046a03401060844003508402804000003038010303203251041c004e0075802048401024500700a26400c0310204241c45d21221140d00c3c003003003800110b12404080e0380d41c0324448040030740180140074421030149201c141011112a0040f28940303600600010880c02082044464400700014042e0a1440e221411105c40e003000050a4603400d40180780903114030890781c40020f0000d650042d10481c210740252801c4a1180100c2c6040a00810710240141c2500000144001000071244501e851394441d800f104501d1401d58110001034070041c01070b80582e0742010914844d003841d808010b40d0400200381255a51282e01c1521250008541c45820003200d0340c01540d00a1154402084840e4001702d030605010000c903201e090501d000750065100800103000c0062008056800e404580300c0f407001a901540360104103001202c403903001c20034254 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 485381798 1250 485380548 485380561
    0xc031104121e030804140a172508030a02091f0305070e030c0a030305030c0906040914070c0305040902091302130f08070803190507020a06030f060603020426191109 72
    0x2c00000440e4040e02c0c0c000d441e03100d41e65002c05860040340f200410340100c0d8104000a1112500040b0034101d00aa107502c5c0c400351045007007030380d030342c81c0fa124003c0801c100b42e03200045242c030941c0d0b07101490900040e12030801d0341c041f03000100c20704081038034080c0c2c10008003d1142c041e030040740680101e907602e8001100030f009060380c44000501d800d81c00410003c0c2000003900c65002903a114525194150800c1e80c4140441c03050f802581000084d1621000c140c0d241c550103035007090b88604a4584030034030741d1030b07600d003c0c0c0107118a000b944103141e00042d02c0306281c1c81d0700d01041c1003a04110011992a4070702098844c5800d09409840d007000c11202d00062019000550131050341c441e00040d5180400c0c1c0d00100328041216252a018000d0510904015070b0768605424010490358801040000320110614102d80311900311a0526206110a1200142d0307031221414045900328180e0102c0e455445441c039003441400840300d80d41c1d03407050030410055a20f0a0742090402522013000d10344428 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 485383048 1250 485381798 485381843
    0x506210c0d050a09050c040e010e150414120315030309060703030f1103060114071703070801150212040311131514030d0f0c08041805060120060a0c03110412 69
    0x540040c010360306c00c410140e59031500f0b07031018031b1502081c1d00005502041c0c056107800c0002c002a090b5483c0c0c180c3c4200014082200e1a0f807595045144c0a01445940b501c003c81c0a404040e220518100d040d000100702901d0406c1195000b400041c885e58071000d16150060207032003001c0c407980115040100f52000705c2444010b4030300500c4141c5503440c8024a2404901c115040410b00380c5000c2000d440d1000046508801940607440594640300d04c0d60400d6004030303a02410f030503281d04642c800b4880c21000703c00318042e1420740e5400100b000c0c5d03a8106c000013078094001400760750b001c58a400f0030031000c6221009680c00b00e543d00c6026901c0a6040001c158a4403146240030001c6480b0307010341c070b101c1d80c480c0707501070703072003841441d0032801d080c2c0790012800f521141181c2c03400c64070394500920040c0e40e0085000940101520840341020702d180075202d8540c100a80503540765034891030700c0780c9002d011b500f01c40c0e40b158440401c030340c8540c9c0d1007209038000044103100703517080d2140811114800485 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 485384298 1250 485383048 485383061
    0xb1801150501020c0f031005090c09100b0403020105030406140a0b040b04020403020f0405060a080307050a0212030316030c020304080102070b0a0b0904050a0f03030207020607050601030c1d010506210c0d050a 91
    0x50f0054030441c29a071052000301051001401c1d418042c800514141c00c20a03c501c0380a141044000c0c41c40e070311601c003845030581c4064040d000f9010300840412440701c02c40708580aa03542881c0c801e84a0f02d440c5040d00240c0343c4c102c02070600070050302c20010504040e92001002c0749041300c0c14460507040c0400c0c0001c07840350380406500116201200281400d20b0b4000980024000e000d03240140d03a205619030454201880c11125a00001c000c4002d600e0b200343d1010400c88020003843c594104606040104804848210180b45e118400d040d80e0702d00910542d0010b2034810b009540d110035601d8561240c910072603004a0061600300111b2542c03d00c551240d01c12580324004000012003a00d0344956000044d000b01c0415400f00308c224010f8a0741d90141070082d1183d801481c0715411890006049246904514008400032051b000100014a0242c0c11140103682c06551034030f00d03035014555010444518030301e40b00c082c0c050000b851200d100a218800e2060020405515525602c0095806 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 485385548 1250 485384298 485384309
    0xc0325051b0a03091719051c0309020f041e090c150305180a0302030a050708090d051b09060a051c080f0414030a0807121e0203040302013510030b180115 67
    0x100b006c0c1c01d03020400702d040003e040b502400c1181d0080310361400310101a14180c041d00300194440030384c001181421189540d500c0c0c0300b00c6051200f0106401b1b803140c41480c1c08454901d6130340300c1034a401440890907503600076055946070780188040c10705000e0081c10055035081e271070603074000c80304810b50000700d06601c174950306502075441e100074004101c4003500000f5095842400403c21051305e65556601c00d00d50b540306170060075007981c1d0f2500184d012140c0900c5103001c0d40382c65040200b030ba5030300c1e42d0b07032400d681e4211049103481140b45000e40165a130310800074130000d8009040c0b6036811404000d041141c12803251000c180f224a000d141c1c8481151303100400001d800d1000b01c00052400200c0219a03c0e645401031407024280200a50080d1181200d00503810004040c4159644410b00f802901c0200d271039040044141c04c03000485088840c2c5c1020955640400b04130a264030001d1440210b420599000843c2420f5040b62104192186003c02540c03910104041210080780c000c030482c0c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 485386798 1250 485385548 485385553
    0x30c01050906071121010507020a03081303090302191e03020d080f1303031d060c030304080f0f030405060114010f0915050403020d0b0a050c0325051b0a030917 70
    0x4141800d0110a4000f101c0440d242c0d000800182a151180403c1c1c0c0792814100101c110100e9030480010b08540d0013038101c0c404c5402134008100805d4000be511a081240d503e0a12041c44490904540002458000961203000003260b03c00350003080031904243e90300020742107480940110300c0d50b4000080d00c802908048401400004601050040c14092040044c014034061a208451401809503003003240402c001c808807a42802c1002140341d1a5181501c80510f00b56040107070554130700000300002e00310040080c2641003c0801015180103000324130005449040c02c1c40d0aa48402d400d02445d102021030400c0c6501c4c5620410740641c0400141d1201c00703281d414000300c1008800340d03008220600800300400401078403042411541d690081000e254a4106502e0031416104080c10801d213081c420f206002450b0081c00c10003585914041051028407031a6100b03586501601c070b00c0311184044070400c0c0301f0003500420300c1000707544641d50f00d0b01d10f56204c0c0e22886090030500c00d0543d503039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 485388048 1250 485386798 485386807
    0x15020d050a030b101106070302161b0b0c10050a090803040b0603070b040b030a06062102030406060320040c030218010c0501140c04080115030803070e21030a0905030c0105 75
    0x1503000300020090001180b8022580304a282c0104042140300d200380c0780040e416440c0e041d5a1101480060b41010385898103505d030814107a0b035090021600b6201a010310180008a00041c0701c1e01c0b0f4044c024966000d040da05d1307010a41090792101000c0c038034000101d0500c070000d0412441449465803040e0300800c500c0c04c40d100c0ba110f950109030002c080b103416105152000c2000da9445010704002c14840c0701c903070368900c1c16100c064241c640690015090000c2c0340c04603105903800015000c0c002e1061500161039640d94240030015080a510280c680c003035086074141582c0d041d050b0003801031001d403001c2c08642580c9408034100e21a0481c0080e1202c40c1c0003880c560303588650040054940203500100e00c401031440c90b02d03511401035600440c210400941082140c2080c015000d0407036440320a10f0017a407039074607002c1e164070008025504001c10b0ba000c0300555652000321301c02011480c4501e50138191001600c6540341d01008140000c41c0010000051070701d80064582040b42040e9111800c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 485389298 1250 485388048 485388073
    0x6050a02070816140a080303150a0b0316080c07081303060b0d02061902030d022d0a0516030c12050306011b020a030b130b07020307140d3002130f1502 66
    0x11344918440c010307070209803030f000083c42120800c0a50f0003541c10f8003440865640120400403540301076070010b082410141b00b0428030f60091850b800c0b16803007600f4151200d40e90284d410002d4452268020f0150788049800208d812512a108090300d104800c104001150041005491441800002e502c10130030040364426400700c80a4144514a41c0100c0b03081541c0f00000806a0700f280c00c680c215a80d43e03181c084402c0184030488000c0d00c0324407284510303110000c5030091080c450059020408445071034a01c0c10948550402c0842c903070400d440e40203050009030014001d900540d00305002424036201800741e803c40410501105600800d0388541c5d42c5950b40d010890312000313242d140b181c0013003221040807440030440113100d80601e5000d582d0710318161814041b031f001c42002d590740e50341c071170f50010013055003090080b0015030103100b02c02280c00c800c06000c8800c41848806081c0715001284520040460344003120907075030703101d070034060003030712003489041e1100040178040c010b90200100001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 485390548 1250 485389298 485389319
    0xb01050a090e0c060a09171f1b110309090a0b100c12030b010c1505090f010c0207030f0305040b0a05340312023108010209061213021c0203010606030e10020f0d0606050a02070816 78
    0x20b500c254601a00d091940c000009637003401c04461110b0059103c0290120600e481c00c0d240b003a140807418520f074030240945171a610303445201d0114041c590340e031080d03c68503030140789106200d55021b0680d454201c20303803280001800c01600c8002461190161115846206018820084400c3e900900102c0d141d900c9020315030f442c0a20035810f01c03d0400c40810311000707aa0003000e032101d41c3e0b00d800e961520600b502c00041d4012002115104000d03801000710001d4003500540e03942e8051802060032900203a04030020310407145c0c00f04501424014103c440303254100c94440c440400c25001c542607998580d01400d0b44039908080e64055410808034580b03001c4a400c0503001a66a100c1d00040c41e2507a0210f1080c41c3c07614601600080f15001000c01c5107400d0240d140030300900e24050082840c1051160340e1446140341c6a002e6680105000c001480190103440180c07070019402c4c464240e0314080038146078450280d00d40140030f9103001140c10b100000e030300c03124134000e040201503030b9203031100510 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 485391798 1250 485390548 485390567
    0x7050906070312060f0815073b1926030313080409020a081f06020309060703021c050a09060503060a030204020a0c0c030b01050a090e0c060a09171f1b 66
    0x10040b40da1407002003581780480300f921018100e0b1030000c1085e85514404180c0c1c1000c02040307002002100040308104030803210400c600115600f208078000c0144040c5681000c2941003510340144180d40329000c1550266042c50131030b05041943c059810446504480300000040308403c1d5a01c104080b4132440c415004a61005c5e00910585040644480c1e080d41030342d010800d04170009800600303020901107130060740c4446114010318104024508070021b51a40511082607124520215030b1000f4103000b0b01c480e40400c038004146410f141d09085000d0301c25000306481000081c1c0c81100416842e008d6000c80c0d001d600001c04000c856072035942080003960212140c1c000304011900d1840008108a0380303400590310410144030658104818003505a0b5603034480360240b030a010b41c0a0514002140c9a00c98003001c0c1c032101e070b44c0c50f0800c005841e000f10302e5100d00c42e011040d41c6ca162000c5008151401d840c001c0c4140c0e40301350b011004040069a400a20300150200000c0603441c1b994010140b11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 485393048 1250 485391798 485391827
    0x90b092404050303181c170a020901091a09030109050d170709030b0c07122a020d170408030406031e09030203090118150c1403032403010b1201090506070509060703 72
    0x20b0b0070341058110a4010899039103121b802044050411030030324141045440d0740310040c42d82c110704188070040000d00d08505407060650001260038514805403000b0b00f255035442d40607001740044801894034030307030b05c40e10010801c00203003101d00010b03c0003100d142c20380c0c0140e40a40d1001d40540c00c580300c014900c08042c040a003021002c000070000107a2207902d29000300d5540e00d0b48203503400c1d402841d1100345031501c41d94080d2400c84035800d0060347e07007400d203481340350308034100340c100f52404080300c14103120701d070090403003480045800107070304d41d141d005050a40c60900c901c940201c04407840100341d1f00560310050160b0014400c0c00d906520030032800040310040d0f04000c200d15900c50791348103c10034078170403440001d460311101301c113102e0222402529a6000d1004511f18030340301110741c0d1400080c00781014000b450451840700c0355001d401400030102c0080481c8030f084601c2505600078402e4400c21513490250343c00040415024205880700102c01500c42480c159203990111034080c3c6410300c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 485394298 1250 485393048 485393053
    0x614070218090610060f0e030304091103040606080a080306010c02040b0a1206060f060e1009090f0501170a05030a03020a1704061508010501060c06050703090b09240405030318 77
    0x20402694030300c001c03800c981c200c00e00c8907201030900a0001c0e04281008103845040c1107a00300030018258000f03400c8000c0f1440b403400f50504040310780002e0071803149034405040c1c54140310b10034102c00c1101004600a91080c002040071681d50110b440d1580a590350141a6070418030008070740b035010b251003076440c51006100081d0002400002881079000390000039860f05070702c40130320420540e849840080e004d084560405203203080002061891040352090244500708a841403aa000c2d42360f07079010703003030955041c4669128034000ca40200824810303416210100701c0343d140c0004c0042800415607401001561926a182e4401e40183d802088404108180c0c12845001c00c3d45040409000750311034140440d14640c200c0300c0c4075610710a508035043d240d140c070004106980c1c0182c00e2441c07455020340003207106c0d0744511040d4014401250043c20703200740c8008000181c1d0021620343c1403100c001c0403010f01003480450031032075800103d034001c1882d4401c1001c80c1c905c0214903208510398025104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 485395548 1250 485394298 485394307
    0x6010323010320030309030c060f07050601120201090518010e100e040510140709030308191e0c030c0e060c0715030506012615120a03050903160f0614 66
    0xc0c11030221000340c0c01650042500160240c50402051903802a114124000d5081116020000e03031104100b00046200d0140020080142c089607800c0c2e072038403900320041e202a0340e074230f0415a42c8225215000c03800030700034050114681c640740350202c1200c07070100b0b040049607081c03850215a080c0060504c034001400300000264100ba043c0c4602d11891144000d050752070140d00072001a01c00d56400c412078400302d501005503607503000c0e080108481d0503280507034450b11a8211440840c00b13030680e05000030f00300901900c50382d804028507150019420000c0048100c049411400c40c1e009096034000286281d000741410315011010b0111091010240c2d2689584e500300480c41e1700700030340100003081d19441041010b40c0c00034010484070104070b060000d1381f003034880c8594200000800c80c410f080c01c0e10102d07038401d407100140010300f102d4000c200d950102075814044d0880c0c002c80c20b0381c1c0c403c0c452200c42c40d0040c00700042a0f0700f05c03000003013000115400d2940c1942d96080c42d01000006070340511 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 485396798 1250 485395548 485395601
    0x3030a0507030e0f0705090a020a050a0525080a11030c030a050d020c0105010f08161805150907030609111801080a0b1503010302030c010c12030c110a060605210303060103 75
    0x442d90000c00c04010081280c80e18040c14091f003840010301100d8820b01c1840b45050068100b01220742c8000b003450304503610260700c08079280550b841115102d034604c00c00103400802802c0c40c001d0070701501ca03850f0349041d03c214032441540c0740301d401c0403985580c2040c00003808250081001d0003641038071041c09070500582e443d01e0b03404c551003680200a000e810300410499100c050101e060b210400c03104070f0415600300380c082411410085c0c03c03a0a019910300002d60411462130b666885100010310345030403402c0001c0024090100b0307009065042e481c0c00d40a140501030401164041c510300c3d50406d0030104440010f507003100d4010074041700c068450f1840070403580c1d414220b01a822110006c16142d50450045c5490b000b011101c9606002d81d241000c2d010400d0300c9951b910443c1c0d07a10703000c83c4603c10341d0b500710703401c1c065110714030740c3d0740700d099418010403c460704054103441c41075805459080039a01203511499904038060810781017000420f449504c42e4010303510601d10302c0c0182d4146481c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 485398048 1250 485396798 485396803
    0x14280212090a0c0602010c0e01140d0e0309031006030203210d02040b0406140a081602010207061103160c030801090b010c050f0703020a05010306031707210e15030903030a0507030e 79
    0x4444841c01a0840341e030701c034200700b00c0c80000006030400c1d200030891101282d40103041208800001414041d02103450f000e424500822079481140100080c042d45c180d40340219501e800c6204403a1090040c0c25507140720006c24802c020407070350020000e02a046034403c11503000c02c0c4241c9110b403190420424603400101702d0004000620f030a0355001c1d520b52a0040040525681c500c61000658040007040d160036440703001540c01c1102d4034030080c448174195205070b0080c884c1e8903005010b1802c0480400d4106400c40c081d610405034901800d03809440744c1d000316000360503a000100460010b400620503035101ea40414ad0100060600510600041e1182031502c000000c4c4c0640560110070103004500701244101c000781400e09041c41441d09540c2c0e841c070f10310408001c1054503078001c1b4031101480003203a8204104a003640124490519004000340000242d07180603000340e000e1000180012004001c9900c40c20b0020003a604545405601c5400f404016040a0400d5101d07003860070122000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 485399298 1250 485398048 485398051
    0xe100e01080a2d112b020a050607020315130c030b160e0307120602131719020901060305070c060515011b030206161b0b0a14280212 58
    0x25107008004a51007480c141031124042062103840101c54100c00b07428090b5210358400c0b00340d210401c034542c0c00161020906050301c035020303c0c005a14a82148441d5079443e110f40040c28000e86507003012540750740601541d84a2904000d42652100c0240505128100c80103a008074090004400109480d143da008600c6250000d482c1c01610900780000d40d1903c0c030340311a4017a442e0a1010990315200e0020352104100c0c401c02c2e580000191400081201030350403200e590b802c1914104003551a040d11040c01250f20140007501d00c12540900c045101080109031140e5004003500003c0c2e003409000c0b8064a400b03030001003880b647c2004400000d5060003218032800380081c1c10b041c14850f04c40010a104180306d024601800f009822402095011600507400244200a14644007003101c0c02c40f0b2a070003905100c0f10b0150902651402c000d0202041805902007201c240009900c80d01da14103e008242d030034211404142a0644c00705a800105040d0928655001400d00311009101c2500800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 485400548 1250 485399298 485399309
    0x322050a030e010e01090e070c030302090a0f0305060a113408090301060e041a090319080f06060315040e1504060504050f0303071b060b04090303090c050d05070e100e01 74
    0xb604030311540c03659224408584401c42460026030700740c0b0b4241306003038591000d0040e0081000842c811000e05020750100c0d10119030190002e0052a9144000e1185625500040b5554003818002c65090b0300c00e8002c0624000201c034001d4601503402c00324001c040306031519040501c04007078040802124025260190741c1c003818000303a41d840c00000709030031602c040d000407107a01c8409040c08081030fa01aa648040c06140e5841c02c00f503180d400806185010302e038804562800031081041e692980705003024001c14082820072040e850710400c100141c0001c46001411134100a041c2040d0714207a0481903848d182c16040d034501d440c1818003034413500da007150141d907455140d4080c0000c1000c1004024160610800918150300b080a4020004c850408451190300007681c0d148081c40b556900c200d00d461b40040007003040d8512498040c0c0640030100c4140c07081e4001260014550034200d40481c0d0780340c0c0c03220140c0001800d0110300d10704580c016021841c041c003005808548182c2566000380a0304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 485401798 1250 485400548 485400557
    0x20f300106051e093712030522030c15021615030c0318050a05060f04200f31020c070303140408070b0d0506010c030f0804140607030b010e030606060322050a03 70
    0x5c0642c20403e04d030348680c0e1b21195101c01c000301e8020202c8d500800b5545420340d9903c0e4001d40c00d100860040c060395407900302170040482014001a840d0b404400c601d0b1441d0f40b0b80a64202414406148485503400d11414007030b401c19402c10710100340300e44e003d540a082c2d0341c100080e1150120308038584c05103411000f00c1e03e9612040d84882031080c10814654001c0d0a4030310710300c0d00d1a290340d4000746151b909242c0752001241c901c4900c2d2981d9034035a880740441c40034090a03101200700c000070b14a05540d07400300a20244040d8070005110850007107c8480c0400b40040c256035203566000c403404071006801e0300032a002400003151184041c0043e2004015031840c03191928001341d080821200007504240c103000301c072442c510000c0d800c000d00f82c2e031001407804c02c103100355150704043c110712f5140490350500d401200301700000c441d0164020902c140c420b0b620300000005840034076a07076240645980c3e0744060b0500001d905002d00b84650070030f10003040c0802c19020015603c4a1810042c443d048000c01c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 485403048 1250 485401798 485401879
    0x1a060a0c0c09110c01060905010f0e07050403051203010905070f08010b09040902060408010621020a0608070201020715151706010e04021f020102040e0c120604020f300106051e09 78
    0x4e9001d000c0c01c40a45071442041049515101042140f0380e158841d148903641d0200014400d6401801a900103580100684504000000170b140c03841d0710134020b8446032481d203008039813190702c9140205454852512451050b03403c00d800800a0341012200a5100f07480710798a0006866010240000700409000498580d0a120b84010800390744c006041c440300f007920b50030015a071140d14010440b192070801c04190345844101f00d01912605070090021001a012288481040d40c0102114112141940c0005842d07900790100e0800c00180651554000801404010202c45a042d00940b00804108074403c00100089202c030310455104090303540450104412810301e034006621005e03a11440e13283c900514203003120300c00003600841c003c0c0e07400318960039611750070800c0303c2c401840900da040d00000c2d603082c9140469a980c154800d600d01c040c5c0000b4030390340207805485406022484400155501450070051030304900841a80f10b075110904845056113455403040b02500d413900e46282c0d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 485404298 1250 485403048 485403067
    0x50f0105072307060b04090f050c030c150403110105040e09010605030106060507020d0b10050607061a01050304020a15021e010e0106050303160308060301091202030a031a060a0c0c0911 81
    0x30b0240012500c0302c000c00044100412a602115545035002e80c0004516030b40f0300106005100401004120141c50440c00040c400c3c0014448200c000440032200d0f002d0081040c01504003400e1408009008280000d000050b0440628101102c041c9802410f01d5030720300441c0354104041d00c510302141d6417030300148150b050030f00030317000039008504101f460a403071940401c0800900da0700c0a40940c400300d02007030060101c0c1111038001d090051a007503c828140c1031100040081000100c2c142d540c5038411722140d401041541e10594004000c1d1030841c0c507000b0b454641c00240741c0003d045000b8150820018610140138810710300035400001149031408c08000d0840d90a034100a00c47e80c000c2c40f606110201c0f180c0a030350250743c03510300401e1a4484c000441c0c050603034104010000c41801c034400c503180740c1c0013028003419101c030f90301071000d404014060040004074402c2e20740c0009041149010043c0a184000f0141b440380300400510390703a400416003210b015084070214841c001449100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 485405548 1250 485404298 485404307
    0xb130803100e01060f08070f021f0c020c092a190905010e090405070b0c0a0605040f0b180a030c1a042a210c030b07081803070b0402010305060a03050f010507 69
    0x240c1014101305c4038010306110090248240142860100444020221042c9200744502c0074060590382c0e1403c0c0e60444031f8a00e2000e003456402150051140481140080c540300c511203020304048441521080c00d40b9052511801007080120100b000403c0391040301100540c9407101d400e0aa81e9031002c0a082000044c07100810031601d0748281c0030003081c000480c41c00301c0c0a0301103034140c204090752101040b26650911110b15000b07020603240000700030900c60038000700c020700352040d0701c014581da40d88460880c03042400030740b50307969500406e03003140088d004449401742d20340074a4011282600d441d00350000800d08440c11500307008101c540030169201001d48010f10051503400e8568a414401451060110840c6c2c0380c07180351606a050b41440410f00c0032502560300509441c640c1e203040c00e809414064140c4101111410000c404072120b40c02000781d44200e1744c4070302c0c076603c1d6460360380044020b03000c05041b142d0f00000c00580000018000c00c800c0701d0706115400041824600094060b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 485406798 1250 485405548 485405551
    0xe0f03030a2f1e040305030301091a092202040912020609030a080a0c09090527070e150a0e0f040203070510080402120316031106091603030807030f0204060e090c04060c0b130803100e 80
    0x250782851640c4501140d4cd50b038101260300002807c0122101c01340303c0e00f00c0c60b480305c04140c0030750003515200145043c0035114408000c1c9000300c2c1c080321800d4070340748011544c0e0b120b407441d9600000c03039603400300c0d114204030b42246040350140c3c0b4142c143c2d0b41d111402c9400b280c4080d989a014110445008030005003100c542503200003a540142010500d040030700001e285008002d440b41b40101400b0051541d41c4842c1c00c0050100c824418a4602c0c08103038140e000502540c2c2688a4450740400056614020701c4078901b194030f907602d0030b41076200e941c00d00c030110480c0070b0058490701040c001c13105a0f002280d0082e80e054026a10046c800c0c000300481da09190020b00103000725040484d0740c81c008070613020120112039143c6400b0240f540c4004c0210f00505102c1c400c612041e0000400150056100607170820b002000c5400e0a0561110101c2c83d80501c02c910486001c20101d092074404650003c94090b0301c500c12604445841c1c1e081d40d01e80d0072603442202c0980651003800410b00c082c0e8401207545 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 485408048 1250 485406798 485406821
    0xa080307030e0405104419080a030c121b0e040203060312070305070b0f160f1202090f060f0408070f0503120a030e0f03030a2f1e04030503030109 64
    0x30062401c114400b01860b6061b8083c00326800c40b000702c2c040d6148601980b1030150448803100b80c0e610404481c00340502994032121307451612541c80c0c0c61715050041c00311800001ea0003810700740760480406017a000741c44024180d10a001c0e13034224001440030180034070040c2585010003840507420707149020700401c403003c3e440e5001700c0c8180100021514000b6201888019443d99035071140207614085071144500c180c0104181480390030301c14118400d010540c059504101034035080265014201c1e82141584080c00c00520480c0c03900e480601281c3c0200340f1290b01400c2120603a80d0000894120f9003e6445030800c080001010004403d0a102c2180542480001312420505c1d100009940d0300c6216014481d650b40003900311082c50082d0300c417080c4981c10b5070a07070700c01410084000d5100c0d0011a0501e002501f04101d150556585074401b6200c1862085840c0c180341001004502c660402d04454083c0001d03925000c207810340d81400f400043d441500190b90342d60400100074107891500054 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 485409298 1250 485408048 485408051
    0x6040c03020405090406110f2d070201020622060e0a0507080708100f0219020105160207061e0e0d05070617010308030a2d0603020a0614071403090a080307030e04 71
    0x14450b030799a0310b41380ea40040c1c100d80c0c00304114030f196000703202603c603101150f036003220000342c004035480101d00365060201d252140350701d10500703001d1405002c4c03140d10030090058100000081d60130260740e00c8039507403808680c4440c42801c51551b4400490740102091101c1c1e90280d2400c408004040101c080070301300e10400782660b6458110302640e1440d46180c0c0c0b059864440c8100c1210410680c15500368070101c80c0d0090b6208902c03c0003a000302800c2d9084015420002e80e0782142e2800091101e040316903580d12446002c1480704014980d00300e00c1c2d00041007103117564040c603883e51210032120b500c0b401030025210703941c64400080d244640301241c48000210700401040420341c0704059a80c011990000400c03807540602c1e50080e0301c01c01c02c240015280d0f01401243c022482c95001c0020303648280e0700494580c0d1a0282030720100d518011040180030300300030b0308001480c10300d844500327000e11800300c0b824806c01b42d00148000c21950401d956550002ca080b10038564000181503201d841a02c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 485410548 1250 485409298 485409307
    0x150439090501170f1e01110307050702011707050d090206070c030b0f100b0a052107090305010506041103041b12121209050705150d0f0510172d070e06040c0302 70
    0x31a032224031001141d14102e0152030a0003070542e0a4000b40c0c7e20703282080d8035903a40d00c0c0500020313100380c209082c203a000410321141c810782e200388a5210360141d6101c4e10748508181c00c5e0b45698020301108401203030040e0060140c040011051420300c0091441013051980524140c0c0c404404820300511440c11031a24100030070071030011004a40d100c5c000c2d480d21030ba5419034505241000c1011014000c10317112041e00f005041e941c0428808143e920510080c8819201c00b4208002c0d1032511020140c0741c0b004101241c00a0904030003e00203920542141c00703140d07a554080d561440300c4400a032480d4082c1060300c0360003640101c1d1290b64400383c1008202174010340d00c0b41980d40d80305002d468082c46016040050616a00054a50320300601d6001e021001643c21544060002600e104502d800e0340c1c280410040c825003d1010508440780040004207000c03a04503c0f40201c2450340ea0709400c001441041408061015601400d4158215091802c20609100c00c0302c85401240c41050310501 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 485411798 1250 485410548 485410573
    0x2a0109060b153f01090f0c05030f060906030a08160b1e0a0c02010f020708090f0108011d15120601030309050d051b0105040b07030e010215043909050117 67
    0x50f20350721003d24441c1e030400c01030400383e50700c0b441c12070012070301c1c603601c11000006129603841c0c104141140058009108141201c40c007602c55000c280c0742900809101d90009165050005c6115403000d4010202ca2492145440d60b41842d0f0109900814450700300902e1000e201242c40d41a030041040c842c0b9442c841000d08070300d148441d020b04080c0300e20382c81d051844c078000d04c01d4002c9004600d2000d0210346e41c6011b07190000303059000b8a881d9009461082c0380010703e6001d41d070071034105c07a404810640c84484001001c680f00310001e1044c14022a15a11041d50340c480b8440740a110b16100c00034481c95040d4200a000400c0740d03848580b1502040103a01d000131000304080e20000e00c0e60a0740703500c010900006841600a40d00100340e000c5000c10b00c1014980e002d0641d0520407401c1e02a11740e0fa0640f030305c0b40807207181c007124050011000610b460b40340004e00d0a07000805c2600304816800841202d04551071200658042005641c880006001d1440f4120340807401101e50301c006c140e8840323030b079 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 485413048 1250 485411798 485411827
    0x18050f1008090c0406140306100e01030f02030a0c141302160f060b060f0706050106030b0d15060e0114030712030806092a0a0206130302032a0109060b15 67
    0x4200e424104400803000c140c80318000c002c50828000020400c2c0140340d2245040d508410390007040c0d5101e032003100086100780392011441c40c00c1d5801100111139603801c50316a00035881481700106d805200b964610400b1800b0420703c0d002a00a100480150409140c2000706400500c091400b400740b0411540d200703404107113005807400350700c40400c90311490141440c0d4003c10704034000c103800070030014110141c00d02c01c1d8010403800c0c4c40b5540810a59807140b408500b00c07003100c90701d40d81001d10b00c91030b9004501400030a441d8049a43e03008129a61141000d0304140700a900400a034031059000800525003800440c000d4a103552340700031100041d40300104041300150220b4014504480071031526080c40d079444040490b00c04445030003e0401103600d100ea405279280030014000c41000c951004c000414101c556034150380114140300480140610700303060410414069070165074150310a03807080c000d0b919110300528001502d45203d0050145081c00103036079402054081050500c42a600c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 485414298 1250 485413048 485413069
    0x1c0501051c0206040801060b090306010e040209180c0a03060c03060803120c0a09080312040303140f01030321060e061009150503060d140f100606090e0601091518050f 73
    0x80c1c086440c0001d04a0012900512454100724801d5003010000706007100804002d0901c40e2003503003240c210f82ea0f141c000e502c145030107039802980300c1ca8140110380100d803d141c9040e514004001580d801304401800901c58a25540c0101e5203580c0f01c0d0342000310660107100365002031840d640910f250003040c0498080c0c0c082e00804c6000700c0c180204440d0405407090078401b000e85104000c0360b565404000c0701001c2c0030000c403012400241801025040325249680c0c03e401100f43c0300406946908568041c4c40b4940c845544a036008800556190034003054020ba10040445226140391824140280f11101d2807194400341400460a020041a004e01d141ca48444089140003926601e405000031900360700c2c0d5501920202d0f6201420302c080b9404106070000c10160700c2196542c40c1c14038084400c0d95124404c000224a10034410003c04200c82c1c0039581c07103201450014036443d201c801082030b52090309141800070390480440c0140d00106030098019050031610124140c4924001aa01c03460 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 485415548 1250 485414298 485414329
    0xc0102011b08040204090602120a06090c0e01050712111603060c050c0714032b03060603360605041208060303091309020118180b04050702150714030109021c050105 72
    0x941b113580c034043c400e150307064819024088518403020304003502c0030f1010f460140203100d4940d1500a58050340c900904480c00400f0041e10b50504082c2d56440c1c00500e07498039440394080c40380c1e105504001c54400e0022581c801c684007000c0c82c91904505009088070011000c42051100c108016401940c0c005141c80880e8244c002c918000c2c8828004603040a00700c110a01148001c4503d001180030094031421442c0c100d03541c10450103644450032400d456a00c2982410505001248041e0a1a0902c034030030462036224a10b110800c0e0340e135107808850045600b91100c404d80f00c0d42e41e0b041c992000200da0841400c90085042454070000200c01d00b0494130181da180c2d0303443c2c800c101103902540045c1001c4c1441c4600001e0700d40e42e401140d5049454115901d400d501d080520382181c46d1038480c4a020f0030480d4010890955010f11601660b24041e01034018040348407111a40d8450580045005c0d00c3c010a0160300c03034441c1c102c204a18100c602e1a41a150700b04401804140c031003800f80039034600c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 485416798 1250 485415548 485415551
    0xf070506090705361014010305040803060607060b0306040c050307060c08030a0203070323011d011d06181e010b0c120f040b04030530040b03180f0c0102011b08040204 73
    0x44030700c40107406002c0240303464074003138210a00304002041181814800c40b507268050480c2001c40400440c116134044400810f580010700105085003428009840841e01c034000015904450900280c03402000726012550050654404e024604060003541700602d85400c04804c01c070b03480e40c0c4007000c2d8000100004880d541c0840000e8506c0c3c4070b03412080d0300c1c5a0310102000d10901141d507e404400e4240103410340240d001800340861030008400364100c5038440c456180c07000d240803c0380301c01031010b04040d50010903049d09403680501c40c04c40a0040d030744040c240c250400000980c076048070059221350754034a801d1241ca00314513000308107422441c08201080340e6a0201d40c0340c1040d1030040d038004441400b408140030042142c00542c210000003408401082502e8041101503080c07030000c0d94242e8680140410054080144091508042c1c80100d00c200c0070100404289021000342c4030341d446030300c64040481c003541c0a06c00c0000e90309038070788008a10150000c0240001c580504003d0185 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 485418048 1250 485416798 485416849
    0x201030b15030415060b07020a050402030c210a060605030f0f0c0c03040f09060510090e311101080112030507021807050403050d0906090b030a0b04020f070506090705 73
    0xd80d81c503811100c00c41165030516850303060070300300007100b4801d080018101c146080d0001ca0f150000704142c075600d079070007002d80c3c44443c1004180b0020750405000c020025000340403c644403171503612140481300310000120b04500d80100e551080e102e00d07502c9030040c000200300740a10301130100c01e000c0d0b02c031540c5800501075403541e00344074406204446564105000110f008103810095020310360455500e6a170901120380c5074001c000038151102c1c004000301c1c1c00c14404014035a0000151907100f4502c9640503111601c08030382c2c0340400e03490960380450380c144255500401c00c82041e2090208030030301e030152166051185020800c010600b000c0e052000125000045603910401c82a60941840d5094594101100060142c2d0000d00080f621740c010b0030541070456204081d8042268215901c081c559031414811000b0380e440503081030326160f11580391070410344981c0010301c910034440c07a0942d83c0f06401d0405509203040a012070641e500031003004c0000d035403072003511100000a001c101c500c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 485419298 1250 485418048 485418071
    0x1080c041e051e210a1e020402070809040f0b090114060c01150f0602060403200123010f170714120105070c030f0e0a0b0c0304080307060b0427020103 66
    0x160465070320850780400100115111107a0350b5000c2c3d04129003e403131150810010440c3c40d64201d002110b000c0d01684958059804907103001090032115078040c582000b03c08958004c103090341e010362401d64005400052070200350070903220b41060308071030b00020010000c0c03440c001411550107105021140001e90359803003096883c10210b41c16112450b000704001182c0d6040742241c20514850b40070300400708400020014004501d1510031945583d540000d4280b001d81921b2481e4982d00010680d0359480d017103610f111900c4000458007802c490341040700d61500d01d40c2006820250018141d0090303840008410107000100030040c1e0349843c0000000400c0280801c0d580b48600e0700900c0190700744030030f00001c20b80110060a15500907541e04803455100c440a590344880b6075030307151304004d099900300a0300d8148409014050340c110280d030300d41030f074031030520345540c102c1c03007041c1d40c120307642ca8640030a8903080c42403025900451881021141e420406903880070340482c0d0180c18103448001411a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 485420548 1250 485419298 485419349
    0xf11070614040e0118060501140304170c0d08150d02010806040c030212040308090c120606100306080d05030108010c030e0a08090a0905010608040b0a0b03210409020406050a020c01080c04 82
    0x9040ba81c684403585681d508032540aa4041c10083c52105c0d29051021840d540b048101c0001010100441840c1d611076030382c4c0c0b001e25010800f00c0e80000c14107000e2003031420320511a203a100403176546c403c0c4060074513104105100d1180e9460340d10a81444030702c600140d030080186a4003036030460b000100f90700c03002400c2c3c001e440799810621000301244100020150054642401241c2c8282103d030240c01710814403100c2c0c950603141d8811544814002083c41c81e10244112020031580740120300036503036000052400c01101810320201d0804401888000c6d8244075034501c81c00e8500d8280081c2c8012a04261121003511001d0950710001404001d1a00c1d0300c071000000307100c490340401c403540e51003100800e0160140d800b25103007801c030008030350081044d015000000e803004028111070121003042e9230344120505000c059082d41408002003039007541c405040180b445890300c0c1ea07119801c0300001d06000c801c141103814080f601c010300c40c0307901c2da41c4c00342c0b000d568507244c1c038400d6448070254003a03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 485421798 1250 485420548 485420557
    0xa1404060b0705060403030507050711040203041a16020609070f050904032102070201081026150906011a0a1d030f07032001030603050309010e0111120301060f11070614 74
    0x1040040c001902c4000c028000800720b2049010b80c2e0100305507141c09400300d86602c100d070405000000140c1042d29540303056401540c111b07220781f0310310700300030b06640710084185c0084609034580d0002a6140d19400d4040c404643d106d5120b2024064803801d00c2020b481c0c00006010b214014ac44d4400050700b0135001e1507000318101010b002410010101502001c0658810740c0100e0010301d005000c103104180440091081e50300840c051110700c401100e82c00d105100c96004c2e500303d803003503481e0800e40f4403011034418050006a0080c00c3c056040c03014464040e5400d0360102d2ba0a0030402600034041c3d44001e020f10422100a07000000d00c108130300191030004210b41010480c0180040001041860404030012000b15058000c400021600640c00c588207884040e000e50000c200e1031445600c03900e001000c45d10705041803917040b00401312040c070b0b004604074019410500080180661904614415081c0c4003d10700031000d400c1007070040e9100c02280c4100401d200701c01e110160300b0740200c8241da = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 485423048 1250 485421798 485421809
    0x6110d06051c11210d03110a0f08100306110405030f0a0b040210090915060f02150c22090e010f060506160c0506180418231c02031b0c0a140406 63
    0xc0101c202d048034851700c031950b42d2810004030b0325020301401203018507016944100e0307564a0701000012076000503158003800401c001d138078a2a036400400040c902c2e200342500d6002d909102d42d1181e0801c400d151803c54050060380b421b074400080000012980100194080c2c0d0640f030980c1c40651985054901035120b80103090241d082038048000642402c03205800c44800e50303125044d140c83c004042c1c0e01c03100d050174401103411140c4002001c410511008008000300341c82c21114079512000f010465244a4002c001c905488540030b05203407100b4040c000034810702100170401c441ca4400080d10900c11640084101081034510a00344110460841c0c004c00016000c0317540c039804002203ca0419680704041e201d03519200100355014000185122417075400754000302800d4041c2403525458100c1c0c030740c00005100c0c928420178811035441280340c1c13881960f0001c50f11251403002102140710700b503d1000701c0f68000d00c07444019940c0e0161440c1201e231b00100114410842c5008107028007040d4004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 485424298 1250 485423048 485423089
    0x60e01170a12020a11041109010305130605100911040b07020f0d0506090a0203060108010501081222060c0521251b0e1503070b0a020a06110d06051c11 66
    0x203a00864000c84d48400981c82005074504040500d0204012101324001e14003401805001d5045113501075404a030b0082c40030036040d60419119900d800580704121181d511040341d0000400c0083c1d024000c0501d41c0380d490310502e05003810403450300d0f098080c11001903c90010310300c500100e900c503d48031035207940c0c10100b920941e160880245030307520011300c0c040340244514400095042410721580703050310030400141410301c2e0542e002d0801500a100650410701800c1c000710f4400d0032101e0080c00074101a151000c0822250800506111010f9412001c41d403450b5404020840d40704211103d5040000000c209911414130100c1040c02c80d503001011900515921220524a01114030403207100300030185555652003100e08404651000594260b440001d0074014030f040b00026041400701c40c4110740c0d140345142c4800058a0340c1440d0007000c01c0e00055100d01d00500c90080d02c010345400e0340c49025107040d0b81e800105001d540e540150031001c481e40301191950f070f66014000c10f14480c0701c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 485425548 1250 485424298 485424323
    0x81608090d050d0f0302040e0f100e0f100518040204020f21220503090915060703030614010203090a0312030b060c030d060e06010c1403040b16021003060e01170a 71
    0x20b06954440c110309010000c203840070b0320b110400341729000300e6040e1004110304801c1c51720740d90080000940080d19000b01d41d0821000072941e119081496803142d00c200008a180d820820544003004650f50400c500842004000f504d0321840040c62507009541a07500594034159000303c01c5c1030f40103565109a0b01c6030a0703100c2c00411b880f041c400f14065500c0d44c0580c0906035000c0b2000b070154a1940c001000e80e0400c1c0130a4a551824002080d40414820712001c0405054000500168440c80317044000ca59039680512401c01588901c2031450130a0000318684100440025042c2960340320003400446101c80101c0d00364802c0d0040740f40008090034090b218030110b4403d68a0390415041d8400c420b2500c200001c88515480e0300502516040c2c6079101d04003165159948480b9407002c8582aa200410000a403d001407008080518400e11604444411441008044044e80d0386050415007004814801443d5502d0424110b90503246580c002d10f08081b603040c186680304a0141415007001c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 485426798 1250 485425548 485425553
    0x30b09130812100807080a0c0f031e06020712051b01050114060c03070605040c0801200d0b01140c010903030b0f03120a030b04060b0301080d032901110604031e0903081608090d 77
    0x2002c07081f0714400d150710b21040d07840d8000004842443c2c840606801242109500182080c175107000509004000c0503103002c44546a0002c80c2d10154002c60020320300184c840285540d100342c0f2000b02490400030303c0b155140407507088150590f500014030803180010040c540a40400c11201400e90100c002e02151809081005128002e0320604900d9400c0c81c02c0c030829404010b1203c11040c1501c944c0c00c0c03d200804031200002c003000c0442a043c0032403040c0f0500b01c500c84902500201c0304000000c0381ca00c0007494010142e880b0300e903000380503141d0b0101d0b5410b40d0303401040b15452041e81c0c4006603210040322001b24068401d88408035000f9242100c0407a40d21802d80056040c2d80308a022114a040b070308404070115400d1040c1c4960002d610900344460036440200e58a80d0f580501d400844007002042c10b6003018400d4904a012030701c0132080c00024007039401740d01240841820500391003450f540311310006114044040700340c0e403942a152400c0004030b04c10380e103040b44080c1c0f00c983c0100451 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 485428048 1250 485426798 485426803
    0x14040306140910051006110c09191d030406082509031e030804080c030c01050a1406032a06072a170714150703030b0913081210080708 59
    0x1521030100b107004421468540c401c0c03c1c003e850090b14400d04035251246840000c0f546410307048010816401001d04401980c2c1c7e56041c124000c1c0080e0000c0c04001404800c06001c544240c00c18550500c5030341350301000c100c00030041c0e40c104e608070b0a004180713a0325030b00200f0a58510642240031681130740e00940480750300c44000001e90b4403400c60380d071a04901c110708501c15000d81e1342c014006003801c40003500050402c1c001c0e000181d07000c0e0859041c6900040410309541040350325150243d0b03148040c9102140040d1060303000181078029103142201c40b50304020f13901d00e040002d0901d18812102c03108030b40b45c0b002203801480d0026000b01c1c44021142030009640b0030348411800c0030301a03080106000212a84880300301a02c40001c0010a00c0c00c00c042c14500441c044590b8000d000094220003e01c0390001882c1c850310035036001400c000808101308405402801346a0042c1405002e040022050411541c01c5501100682c40c2503440b05d0b00140c1c3c52100e0380140c6401e0060200003c2c101100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 485429298 1250 485428048 485428051
    0x20a050a0b0405060f060f21010f1415030d05071b03120815010903060b0402120408030a060e04030c02311a191a090a060c021c11011404030614 63
    0x60802d540240d16000c0816907040785c01e503511035208071600d15100c0c082c5450304284600d11207520a01c3c01c620b60160f00351b0308542201da400341d00c1c592642d103400b41101941d10340540c0117907103032890140c6c103140e000825610307200c0031282e070180100040d03c007083c0505070000c400c405481d82c4c01c4140c0c158036403401c82e4005607041d4011011901c8613000c60040075003c10500c03203c0300d06035200c0b583c0c20701d15110b450151984554540c0c200d0303420031010f03804207044e501c0c1714810380c0070302c01072a0703641448201e0504646040d0310058810308840306000000e54080200801190101d8500a241501d1404025102e10400440d454a6404425181190190341045031201804290140c4500080080c0520303500c40003207004c050006442c0902a0141c0c0030016014440004a441c1c100221030002c11080341c0141c10200101d0581082d8501310f2900d0020580196005400b40154102c0b96070f651700701c8000d03e584039062210305009800c5006c0d41c1001c0d10001c68002e8024000c0e0614149240f9400d00d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 485430548 1250 485429298 485429303
    0x10608010e1b0f0c060a0902030c010f09080a0f0b010f050105340302011a09060604090c05040902041410030e1203131505010302120d120f0b060d0606030b0d0302030d0c020a050a0b04 80
    0x40d00c0006040c1141c6d51150700340c42c80d000b401622542110b0740044815a010104950912015200c040b414410800507280d59910660505061066504150007203840583c0030701924a03a1031300900090b68054290741d9841c0d40580411550040d0ba00b2150148840030341070300508403c03801da1824940c1c150409500a0300002584102c0c0c110030080c4415118211049900480304110401c03408000d44c0c00008007501c60303d4078238205521080088207a0b406580840c071289892041e5000c149050000002a07440e40d080400c02c80c0b5a072250b0b00d440b140f02038000445840080005801d03c0382c1880d1660f403c42c0d001701c03900703000741c0c0200d5114000d11080c00143c0c010068014420300b0000e00241c84210041c0d1610342c0d00315003140000e403c0160000740003d00c01d1640300c0b0000c100d0381d00c907000500b1800c2403d0501140701400c0c14801800c032088a03641a10030b405030760380103000c603401000b11501c07000489004242c0041580003a454031402c5400140144266224101400782d50301c400f40c010340c0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 485431654 1106 485430548 485430553
    0x120703020d0303050106020d03020a0c030e0102070f03081215130e0c150c2b200d1d04050103020117090703080c0a1a010608010e1b0f0c 60
    0x1070308034012000300342c03610300610102d5014031545400d0b0800e440d0444c00c1c04000280140040081403001c0e0602a1001d191030b9240d10034007100d4060103060185000c21592450004020307030040300fa01541c55003a0020480780b10350364250218516004040180300340503000260000c00d1421541e09161041d2a0250710325110690f0070260203141092440c3c640364160212070034808640005102d09550f04044452040101d08003054a10b1501d402540301034502c40403c0d2028020300401c0b84c601c5407040640d44140e0101502c2129840090901c1c10050801c0a1100303540d400e02009010404c8d20108080f440702909080f544020fa0348211a40c032507580d201c56082c4e41c0840ca6034421600070b981104180000402c801c018422010905000d0b0b40c900540244030503410300991a00c4a2051f0204481d0b000703541e1140c2c01d035014805907550b0350106096119040d40300124540150 = true := by decide +kernel

theorem cover : BRFrame.Cov 485251798 485431654 := by
  have h0 := BRFrame.cov_init 485251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 485251798 ≤ n) (h2 : n < 485431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
