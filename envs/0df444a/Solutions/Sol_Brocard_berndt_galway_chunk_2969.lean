-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2969
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:16:36.38509+00:00
-- url     : https://prove2.me/submissions/897d2323-6c64-40ce-98ae-b63536ef9444

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 533812949 ≤ n < 533992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 533814199 1250 533812949 533812967
    0xb0a030f0903231c0203041a0903300414010603020411133501090f031d032d03070204020403030224010f0603110c07060909060b03060a090c 62
    0x61034051a00c48480100342d44440c0c0c00c00001080440c0a0710380950321820700d407603c504182d0000c4e10028080c4641c6800b500d402545d40503018a00d80e040f01611440481a0600b086940314900d40000581820720300021450a2925040340c41d03a880562100d401802090340c045c00181a108250442c010b01c12002d400c030b80042d41d0302500500003081100e0102d0126005a00c154900c0c511185010907680d65140c414401100004070710713a445000303001c0c01401c050605070403444035500d81a041c0d010910101642d0281d030302c240c4d661340400c1c0080190000c0340150340c0c505031281d081321a000d401031040000541c501c42100d5404500000304800407842c0d4429258020740060000c02d00100b41500480d52210014080298140410441580c00e1151400340106542c801c14607406102e100c0c400d500c80d014a51f0205042803174103210300b05580c6007003c240e0200c400103801c030b44140241c0304103004080081c2001100c45056007094400a66110391078003a02d90010b40d07a00d00400309a115900c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 533815449 1250 533814199 533814221
    0x827060d0506190303020d110102090f012a080703171003410118030c0f0f020442050607210309020301110a020a02311b0215010b0a03 59
    0x80f00c2460f9032850040e4484040000240224001812100010038180210b40c1030540c0100000c0100941100545403c1c10340d84400c1c00d0744000620311303200c614480113101c4285018030708058a9003002d00c0c1c0107100f1803801d56417641c03101d114802e205803814100030326000c0e130382e1114045a0b084501040705511410b2142d000c03061000480c00c2041074540c092219003d8002c07180244166941c850410001441c2000010000760714040c180002ca02030720070a030749071441880f14115540164000800b0740c0d17035000d40030300ea04203418901c815980d144407501041880c1e44950029800c881e40c0b0312010388000b0320815001c1e1b400020700fa07080002d0009001e800e00f10300c1c1c111460401c49000300130f0040104850880c00f941ca020b448110007002c06050750244007071070307005007030900140e424041d0092100d40c074000c103084224840144025805404203003801c42e4040050604e40c0100104001c0d40f580b101c5100355001503481031450410206058151481443c000341c3c0c480f2899402c500a1400c4694 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 533816699 1250 533815449 533815489
    0x9091b161401050105060309030301140a031a0f15030a020108190212160c0b06040b030a150207020109050609010903080307021923060c0a03090507050a030827060d0506 74
    0x10a03010840301e07107016501d40030310300020440391303072101e0510a0b6072006a5842223a80c0c42840100210a0001c203020b20300d1002a00c022a900c0c2e0329079880c44000c0072058043c0714810044100030301c5000c41c0300c0c0d40b0360054a962524161114032404203490300c02d81d02d0060704100102c000581d100003601c1c2540da0320a40030008642c1c0d1850016020241007058807080c0081e6116050300f00d500b88114850201c40e0340011205480f61580000c1000a1400c095825010300038984c45070b002c240411034249070314180315005640d6400324030004005040682020303124190a124142080c0d0f440305020043d039038803000d4550703203803110390003a4507160505804d081852081d6540100708120360104541000c1c0844240c0103140300010401e0300c440040782e410181c41c00c10301c00518030a11907003012207400d0251050383c510f5034803480460440345081d0016180000005180101c45030310881c0c281602c2c55403400036081507400c400040c0a4032030130541c0201945c072200440c00740c2c0d449028641c9032803100c0742 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 533817949 1250 533816699 533816737
    0xf09090f0c080c030f0105060307090509150c030703150311060906120c0a030c1d060f0705121312030e01140904020a03090201080703061802030c190207080705040209091b 75
    0x401c43c0d600c4640c0c002a138041e0103985280504840140103140c003070301006014100c6d00c0d080c0201c1c80b00a141c028074284130351142031003440c0000d945070005070040c04401d68032640d87c40c24100280694800e003500340c1441d29400310810100e00842405002c40004a415039910f4904000003500c90180c80c18031000c0fa2403c400380300c10160304000812000940e900c046c44448030000c0103440101c15001c10080100400303100b03009500c0c1004c024060b00d15280c4800c1e040045c44c0c0c440a00d800c0042c1c1e103004903410300045100b004848a032040c001042e12801d4803c82e00e02030b03a802041d02410619090601c04c4d0403880300c00b42036445003501c4841c03001800440d00d40c030034082d006024104100c01680420414000b041c146d92080c0182e00c00c0d034444040302c0080300d000080242c000e40c0300400440c60700c4418015014010048a000119140241d000744841c9040140e0759003005041d40c071042c49036204201d0040152100e525041d400740c000c1d903c07551024606400d907000c92107218082059810114 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 533819199 1250 533817949 533817959
    0x1a091e0703020906040515040e3310030312050a0615050304020108010e070203040b030c0903060112150c0c110118090e060906010815040c080d0503150a0f09090f0c 72
    0x80d04604590003190307038403680c2e200c0106000840344240c0340c0d480760039151006080e40d810300750005c0084a101c00c0888613140b00700380810b0008000314011a220042d011807805c0c204031100d250f15000f01c51003810854a40ca140d03406002009020440841140c45e800003412044280d48000014000405d0740f1a01d101c1c0d20030020320642c0220b8003240820409000400c0c1c49968074202407058406070000d42c50715080800102c03540d00010410440003008115585003510180b040c2c60003400300d14401c083c61105480d09443c100344541205810615044807402210790252900581c0350b006421840707203400d40c0e07004a82d00180f00d582000c058488040c00940030b002d59100308180e036003190586400b03403a518900c0d6283c0e4400c0c480c038203a42d840707280d40c80c203071524240724035410500c1050400d10440e615100c4c141080c25020401021800110810100400c03c1c0e14020481c001229078142e154102024403103415414002c41d041b00d035903090313400100015001d40e4400c0d80c1c3c00c440300505c016514 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 533820449 1250 533819199 533819203
    0xe0c09030d030b033007080c1005040213090203151906180c02030711010305060307080f0a0309080f060f0a0e0102070f05120f04030b1506070516050d1a091e 69
    0x40c40f855070280c0b08030f0107680d10600c8080320300fa000325030701d40e140404201380c4500c1304d10a030000391041d520480d041101c141c404104005c1c0401c2e280103101c01180900d0180104200303448007030308050344c1a00f844103101c0142d8020402110070305c02a003400f042038543c042c195004000070030008101d107180841c0411140c0c200c03554107032051580742c02808001c9035214100d80368040e0280041480c4540003507481507600a070003159009a01800b112840750b40c40701e40d0b51030404220022021504002030040c24144c0c05850031000e00944002404c0d4207901030347c026664003004041c521007500c00c001040a03464aa040101030400c0c0d0300c025911000542084040464000700031601441498044120245081c050346c40d0304051820711401c191031a100d01c14901d5004002e800c0300e40c05211600044d40d42c030000b41c05102d001c3c400030158070045050030070b40114a500454811180c2d40f8051001842e41800702d280311400c1b91084034580c4500700010302e042d6070480652805050103c1c1304c05034580c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 533821699 1250 533820449 533820461
    0xa0e010216020f0402040803030c0d0e2e09050303130302160803030915071e03090c03150e010e0325050303070c030207050604060c060b210c01270e0c09030d03 70
    0x711810781c0040c080904000881c81a4401c7d404e03d034000b400014040f220707910280c2402190304c08041207814075481820f0800300d201c102d5404210300710944411501c00021114640d000c940c0040000710065140d040d47c0e400000c020710b086186c5800c2200c2017502c240007240c50303606520030041d20151108002d0303850360030840e1000701603c5004d203803000d0440c4041581d401034503152680c40485804401013a5611100540601415101c0f1503240c002041d8401c02002103000b10005548e22062400002c16212207050f003818907810100c07841c5000501000311500b60f41c81c0d1040318081603901131034222a000740d100207040d501010041081c510703007102440f00d086119078250f610164448040003e140541d01942d00000c41b52030400d00003510590095200c00401059507081d00c1800201c042c01e03081c0d0142405e0300c3c1d000071482212551308061034100010b5400c540c6c5481c4121844134403c0111284580c91421108901045d0103000c1c140880b010b860b809030541e4080341c0102c4010300a020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 533822949 1250 533821699 533821703
    0x6110703030f0c0f0c050319110118030f1206030c30050d05220305010b19120210120e0114070e1e0307171c0809150a0e010216 56
    0x802e0090140c201003161186810318500382c0c0b601d286035030060340111441e00400c00202c070244410031461a074001c4403240b40d9101081070344d031035405420403083da03400d6807109940200c920407410b00d030400180e04011010512421442c0c45030b4480c107c40002c1d4040c088560001d4120200001e02003520f01d01c0d4a1208440310b120981c09038249508442c040300e801281d84081c0c010381042d06686102842000204403410080c402080c0b021480380340c005410b502c542c412103490703550b40340502140c149011080c2c101507281140c040904e1800c4984010448180b000034840c89006108040c654003c0b61040140030952404103d40c0122601c058020486420040032800c5e090000841c1d651064070710705002a00a400e040340508900c5400c8040d000e4441c0855140c001e5030400f186244c112000c055001c5031000040c054143c50b20400c003070341000310501c2020803e000041103110340c070003d0302881001c0c4d80c0241901036601d51035040b000304180440c8038580d500008400400702d004c0b40c0e440315424 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 533824199 1250 533822949 533822951
    0xc010e0312090108041a0727052b0503070b01030b0114060d0e0111130e01060201050106051b100f02030f1f030204091403030711070b2809030611070303 67
    0x4412001055901c0003080305424404408000315469035214030b07050380d041031040300d0300c00c030b89800e0480080404d402140d20070300107444240d2111202d11010307001c449080782052443d070034504000128030314500380400c001c150401c1208000e044400a50301c621840d8111302681d454040c14034100b55241d10a1000b030354414501c50001c15602c000466601302403800400f268680410041c1c10300141081c400422299540c0e02c1181c4150713409900203001021402816404507030a08002034400f0300113803c2042103a140c04014803004e50080c0446054201c600382161004102c164410f140188070000b54013014100204074a40c0d400c0b07070b0055030054500b0341c0800915070383e1310482907102c141004103031820f2030310480400250400fa48120f40c1c0b1802010203001207841d07103020521f1588140e0340180015004492a904203500b480007802400c040400700340b80150211000c401030900d02c40140468040b00e1461100c04e018081c81401180d1000b420310a039a00e0b84c50000240d004004241c003ca = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 533825449 1250 533824199 533824217
    0x20303090f030909011e05041b080129030c0d0603060f201b12180312040303020a120e0d0b150402070203190201140d0516020d0906230c0c01 62
    0x15038800720940c0c1443c00041c00c1c8800c01d80ca8610000c80d034401c0c84c90442000704441c2c00100d0562105e0080c410601d041c070a601840c15402400203028101c142e00c81c540c280c0c0785191104ca20603084001c820303110110395080741c4030307262003004480600c0b500800d40c035400e240000000030481c5d142c0090900941402c81000038180b00e10001504002100b20700d028030704100310f1000c0101500030f2440040c2002001c8510f000b0711200c00000f1a03128640940d05001041a2940716103010007203081030980402005041514540d001b039138030365500307000400d60030000b180010780034801c0218121180c40105082c84840d803a0a2441b13070614242c59005d5030500703c1c01c440c89a0b041c540220303103c031680940109525036110090301e983d211862070890400683c45072178000d410080c0c0c00750041001241e400100742c184104030707042c01c00c0100240400d41d006064680f400c00c1d00003502900f182c0060400b038120000382c4c0101c0f401d80094440b0744187e03072008a440c01c1d2404d0b000030075881c1d1752404c0e2179071200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 533826699 1250 533825449 533825473
    0x120910060b031614161103120f09040c0c02130e0c03010b0303040b0c0a0c03050106090b010c02031507090b070c08070f080601090c0306030b07030b041d0705240a02030309 75
    0x1291200321020f91804545219900310a8440c42d62000b8401c82d0305841c6040c0141c0d518000d00c0d16078689426144074841c4013841e83c032881c0900058400b2800f0044051400c07110103040070443c007580601034480ca6807852000883c40c00343c0d285020840d801040c00070070283c0b444040008050805c580d40c51031185010101181c20144200400014014011400c052401501811b264450007015405001c0e1001d407000045d031000d50180511302c5040080b0302c40381462100421205400c0255042094001d00200035171400b00391480c001501c2e110900c001ea0b502032060301c0122055100e80d24581d000950b850911111b92400001d582162040c1c805c01c2d40d4410510408000c14010003160740c101d24010420000107078064540007549080c00300c0c00d00c2d80e90300c0e00c60340044c08456042c0880d0703c403d6001d400c0d107000c0c41070b80f600f0b951100600141d5900e2142c3c0507500c02e03c03400b8030340c0100d41c200344900400036001c084407100e0f1481568280d580494810080d08c981007607504d07010030711824003a082 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 533827949 1250 533826699 533826719
    0x30307021b01090504050907050613060e03030f1c0b060c030c070b0a02031c110712080f04050309010f1407030c05070603110a050d0f05070e01180509040f020612091006 74
    0x1c00840165a120315250400d402c0000406001c0c2c031101451189503400586500e840000e0081c141e03c1c4c50354407800314075100018103554045280c0c54801e4004020724032a06a00310207840c02c4a1418410100c545820314004008010100340340c0d503c420b0124100030381003000002004810014815550410b9072480b0b4100d0f140a440d40e1180980c005000ea0755078485501d07104041c00701e8124010503041602000800035030302c0340805031181c0c900c0e100c3c6007004030703080300701c2079004207403c203c4142c03920700341d00d07003907103034099200114104202d4450728181203228044041401c0310054040d90354294914000e8003421018400302d40c68040c0341000034456000344181e0701d040309001c03501b40c9400c001d5582243c0b9a441003501221031507840c2500c458181e040d1140605c901d0741915140b440308010000940f510140c0d00c7e143c180403030365000034403680d00c0b81e1100302e80080d03102c06004044605440001d14a000300400070040c28984020018072510006e4a00445006c1000402509440d801d50721 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 533829199 1250 533827949 533827993
    0xd0b0604180b04060b0a0f0605130e04030f110705040f0f0e0307030504091d0307050610050301090321110a0905190305300c0615010e0109120f06050903030702 70
    0x1401070b4091100160105142d5000400312001c000d240071101501c40301008400b595076000300002440100340030301082d10300c1d00e008001e0719414428ac20340d0301c5c0c00d0350000c006078002c9244030704002c4504400c4468400400c400c1d0080c0c00c00a106000301c000e8848003074024690401001c4c1d40c50f081503c29440904040304030781031150180e0f16240340c1400e040c10500580400007601802c00266a00e01124100510160401d284614041d0030a404d012036003071401d400f150404ca1013030b407506151000180d0810040d0a01162040e900801041c80c1e03217100000f400083e01600343c9400c00195000601e07408941702c0207031117040341c0d804241c0c0c3d40d0b194036140c000200d003c01080c50f07000c800050040d488000c0040c8407030381c1c41f031300f4802210091040042c0702d400030500b03c18036602c607a0507c0101e01402003151681103003803803c6144050310b000001d0411a603840b404c0c0c0c1810740d0009000030301001101c01070f100c9400c001d060040b4207081800590340da104640c00401800f444020f400195120010b00c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 533830449 1250 533829199 533829203
    0x410106080f0a21090e07020309040504050c01020c0303090105040e0604020c07080a0b100b0d05041103071203120e060106050c151603051014060d06120503030103031709030712020c0d0b060418 84
    0x5004c203040a8a050300c0c060083d207102d00303612080c85080410313907444c06031030300c030341c2c41003018001090342500064035080040c0b40e41c40c0310fa0401d00011000380d9001c003c0c2c500305c40109d0218078454480d48003040081c07150f400200d406010b490b101180386d26001031a02c4e00e803842401c100306140d990341d40301c0440c000329018801a04104002ca2400c0c01d2254028a411a00a26076003132003040076000a4135042d5207a020109180c0082c082d4410b040d0424940b48103252520320601000c01c1c00c144141e20b40205002d144103000740804c2000f40e03d0010050f01046030342c0300030303902021b04248022069461020514800190614000580448400d404c04044400340d15204003110212000c214032500200703040c4e81d01d256640300c00181c5120540c51000c015000b2800303582d41c1e50450400500d00200d021282030011168002e01c00c900000000300d890458203c601e0301d0540d00c03482c50403400c04c41802c400741d51084101c5844028404660044c0e4002c5400316000c2141090f90b40ca87c8403248504580 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 533831699 1250 533830449 533830457
    0x20607021203120a0614010311030105040509030c060f160c0b04080a0c20040509070e04080a03110c01060f0501020109030206180c0d0f410106080f0a21 67
    0xa900018200744003010305185080090300d0610004441150201c0000c40d1101003d980380e8030208841c50640b400701040c0c000a10301404440b40c4481520b00c40c2c401032107140d001d940e5407000102903035410302c03c2d20148404c01050b0b9a4900740000d102510392016a00c01d1034041c00c0346030f0780b8201c5004080c0000c0e0541d225040400e6595641c039112b849030001c5d08580280314940c03845000280391121501e00c0702511208450641c003c0070144000c90301d0040040719070344d00600061144082603125646c2c0654400032142e1b545442c400301b24060b001c4444024691440450b2095a04606400c41401c4d139501003055a07074281d079013004a00380e41c0d5080000d005a0440408180d07000400d9103403500c0c400710481158404c10300000410304000a0310029503501070300340e00c0c050400003c1803055020365001c0180300a01d440d58004c100b4100382d03411020000b0114120039500380c03030080d00158000d0110b0800d50703101140d080802030300c42d0300905044400c0010045510b00340c04121480381614141ea81d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 533832949 1250 533831699 533831707
    0xc03020d0f080f061309050709050a110409020c100903022b050405010c0c030b0103080307090f030c0909031106092514011436012c010309140d08010807030206 70
    0x7000480300c1c10141105420040200c404959215140500304100d8401c000801c0300328230b000c031454101d400c040d10500310700d4140030380c03144050331010980b815100200801030303607130042c4102c56140407030107100040d40504140c030900c14076402044122696080140e50719085110a0700c501801900f070b40a6800300301c080c00144002c0d440703900d0384111244520b58280c1040d4032910345905800003640110b1783c5000c0001004406580308087c41c009018000401900700c0c11940c6204810301c060050001c115541c05003842850710920540d1091800a400e4a03660309001c500d898454451400101174240b40d46503441d01101c6130140c2c0320071141480740c3c54003284200001180c0500042c620b500a902c020f01c1190007903881145031462907412000780b0302e800a41805803000c0c3d156034000c05030510203024804400791018003607220400d54006201d81403e0310300c00040c1c00034000003201503c3c50710004035010710411300196444244c0c410381c1f0750104070782c0c0c1c1d0a201030b40c61a55000c020b400200600c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 533834199 1250 533832949 533832961
    0x2060709150908030d020301082a130b090411041a1e010908030f0a140304030206011413050c0703021e2509022206020102041a0310150c03020d0f08 65
    0x410784007044503161404182d0b035544076039440c0d9001441c071118041d43c00401001070385001c11803510700046c5017909003070a1b054409800c600302c1e5841049801280e807800b10444288465004180d81240200b650b003003414241081e2511400c050692409945088003450301c0da202038a11085042005002e40c0c4e91294000182490104d07402006042c4460441c2c041006a41800541440003084c00d00f9916000741050084c0f2092030b90310a0620030500300b05100200c0d9001c41c40c039040da580415802200c000c00e0000c2501d0307010141415150502e00300510206500d650000e03c05c80380207901702d48081210401e00d01244021402d2009594062180c029000d2080894680714070411440e4412140c0e40d003640100340d074000982845c1c200102000301010b41c007140803440146c0410720086080908094814250440900d407600da284030110000c1c44040391040d4071805040e1040ca900d40144508a02916084582d0030480c054003566402240040c844c80d1808541155503481c800561208 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 533835449 1250 533834199 533834219
    0x1a03160305010b04093c0b070e1008070c0c0f120b011d0f0606072a0e0606070204020f0d061805010504050c180a052205060409030207181e1a0102060709 67
    0x10088018211081d1808000d500c1b09080074406590090071900e21601d4440c2004180100100103507108501d50b1041c0905a68010305042c1e0248103420711901d150759038140814801080c1d801507600a030722460218a0940c035061040040d4803030404208942d80b1075005011703d05442803501036410000d00001c085025818a0942003500540250301d0318403540c44110010690010314688021320242000d2409144d810300030040007204090900340c10300c000092210712034000702038031076034020074401a01c0c2038a10444081d100b000104008081d661201989032178200c0300040d48151600000141c81c0c1000e002c0c06200d501e1101040b0b10b8142d03071802c1d100015043c048101c2c4c000c50b1455010800fa00c812186420080030500e00c0319040c2d900103030400607504000d0030380d4003a90a02a40340c0010b5000201181914603c2d00040300104a011039900100420f221460700c00c3d00600c5d003c00107189580c0f2055094040d102001c0030f2200040069903500b0b401c0d41c264000901c0480d00704900200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 533836699 1250 533835449 533835503
    0xe0a080d081614070b0609070e091501050c010c080915041707050a0f14010e0a020604060f021501120314030f0a0f0209130c020c0a0e07031a03160305010b0409 70
    0x40341c20072007403d0f00122250702158001c040f08450a5212030203000051403c100103d51040c0d061034412240c1e60040041403164101600300000da54000100045c1a8001c00a4070f0700b40c40200002c011030340d09000010030002c0103440e844158040c1c03180d0006d080c002141d01c0f44c4520707003103401e101a00b00740744d10264043c4c3c04031b07030280c400e07005081843e400140b0700300e0542c0405018055451a20b805880e04a0840b02103504090099108480361001603c03041b00b51003c0b1052810a6511800c1c51107040e8100140c2d158035106c01c070b207440d002160310031036186840307920f0f4003da80d0075200d410400b00342415071000380c40814107032144a0000700a80d1168000103e4080c040074003504044a01c0c021940b40c8410308140c06540b922843e1a174240c07581000440f5422508a440c0f803285840c1c81c140829404e0090400c50400d070700d034449844102d09410f10040741150203821600e41809401242000c5035283c00211810350a15914005524240c082d0320316158022a864881e210304030040000e04030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 533837949 1250 533836699 533836741
    0xf031207030605030105040b0601030617070b0306010225080607052506020d020703090513020301120b0901060b2d04061d0d02091305060f070c030c02030a020405070e0a080d08 77
    0x6201e900101d03e0380c0b4280100350095103c0c3d0759480319420600000b500307480003a0884410650703900310b00040c5640010b400401c031106a40242d9894850900403800d024180413004c1c2c0c00710740c0001083d02c60103504040e000b1108000256005a00e85600803079080c42550092245540c0242d522910382d4961024042154460308005142000b484c8120043e604480825000300e00e03a0b240070000b509060020321003000b010a000c629560424041c03003001e103621100500300c43c5000f00022011282544210080c2964840007521942c50007a42203201205036102001e0908610300200b0109040701920180d4085443d04038905d544880048550341404203001d922143c80d054207070150700c62410080c0140c524621843c450041420028944039003e0810305810300f2180030170203007550002940b400240d05d0301d0070024014a40c000070b49001403c81010b036100f8500810301051507002001d0f01d601141c1030b43d900816564034000540c48412400380c0101086101c40024400450540d55114102d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 533839199 1250 533837949 533837951
    0x80a170406171e0114031b030604030c1103010615030e06040308190f0509010e210711060d0e011d030304021011070306020d0618020c0709020d090506130c06020f03120703 75
    0x1007240350400d000043c080c1c5c40081d110080300d40c21122400d0178031103030250000b02203400d040d032103031b500220f5681c01d002040901042900c02c2e82c2d1017003003040c20b40f04042c04c4006000f44040c685034201000e0014082c1e01803800700f4600060030f0b25650001c28070620030390b015203441c29a0742c0d40021501c076500307402c42101422640e03815040c3d00c04403170b481080e0049400c4400050411000785601d490601000b11100d13040c429141c0340e840b80c48000040341e00096000c4c03640c425094620003c14000d0050390804500c050801080124260055110070380c0008020724441c040d0300c01c600300f56124401500c02941290900d800c006c4454040c002072010700b540c2408984c402ea0381d9455280898000061035034180fa100c000c02c1100382001c5001070b5a0841c1c1c1a001c40c54106aa184995210b03005c0c07245014440e00450310301f02c41c2e05160b120b5249140c114007654824078090030118a0031402440484a07005030803008680188000b560304032220315140207500d00700d030165442505000003031144c0c0400d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 533840449 1250 533839199 533839231
    0x3020d0311120f16140d0b0423040b10180b0f0904030c0b01060302090f0108060a0b070c0e011502030403032f15010602390406080a17040617 62
    0x484051030006105100003000d00100313040420071191080c0140d400f520030040d09480102810501c04110350380703031500180018000c1d08000200c0c024080030f04942d1f50804c8814411498603121803459481503105121003282903450f240d0031900102240580c1c68424141c00703d4180030300c1103030300110500b44003d0038a42d035000e9440011f100003104880440000721489400d4080084005980d40074100d43d0405508007200800403803600f0b0400780e08681003100c1c50307012031207076260a800d0a0181240c0b8600326915442070a0000040d2400c4c03182014041014000041c030180340d072043d0011142603401386183c14035544048660703400880d0003041ea00303180303e10300311400d203000202c1c04540c0900c0040c1004135440030000b90b0580f4141d01c418290f400c860079140c14440c1240340b007090312071640126040d41403911408030408498650858201d40f40500c0070032803a00004020300348034803d411106036840c004550040d180194801c65000c60b220681808440d0001203003194803121a80c0490a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 533841699 1250 533840449 533840467
    0x1b03020705120316170f0a0c090b040611100504030c020915061206040515010210110f0a0801030516050a03140a060603030e03120708191106040b0105011b03020d0311 73
    0xf50300613201102e900b402404110940c50300800041c0c00304909000c480090701e0070200d04101e120000f80009041a905d0307844820450041e02e0803005070800f04103690304c0b2a140e60004d89110700340c00046603e480307060280d110034141402114800c50385035598690000996007802162140a030003030580910344400d141c0d094a400025001d0355002038500da415080400a01044810181205400c00200f0012031030590700095000c0802d541e0180000b0407204c0e0001480c1d5a0103468000d4403005070018030000c007280d118400c01e0689010784141c41501c0c1c108522014442294032030681c100c00a4401040454009007080000c5040c2005139004412540d9461003251229003040f008595101c40d0a42141130030003117039411b01c120516041c500b1409440e11034440c05503130002e040309808040d6416805110b40d0142140c0751303c00341107a05030309062422050111007402590b0000e450b140350740307c820120340000c10805070141c000e001c80c8041c102007180542101e0090b0070041c6010004251 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 533842949 1250 533841699 533841733
    0x9030c060f020d29101b0f141b060d0f1404061a1e03070503060115030b010e0108040f03030e0d0201061e030506010e06040603080d0b10031b03020705 66
    0x4110101c000010303503951485815030101d81c2c0d00224101034404100111800410000648092030340c2125541055000c0382402c80b071854000680d05021407041500701c00b00440320a0544400e48541c080703401d20b120403561640c0c0c40c00040d03446038680107000114211400d00200820700210b00301c0c00441e9449905c0006425a8030800440700d10319001010441807024a00c40d05601d03502c42d00d0f80b07202c07000d003400011b034462200345548010034603c5034202400b95001c00c03094000309400fa003034401035070b5110701d0700c4507242c00b03540c5420120b07003130880d0150b00d580310381060034003a00161101c0c07080c2d84464076007a00310310071103400704c1c28556984d0710120310741c80030407500354074024660011070780b20304208441440400c4840c1044807a00f40c0031007480001ca011483c1815280c0d10302145007250303513403000100944226400031f40020f000141405003c0c4440c0c00895181c8000e88031200000d03105039040f03044414a260b0b1060003203914045005148c401d800800459010b00100d850745000008559 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 533844199 1250 533842949 533842961
    0x120d18090908030c03360f0d09140f282405030712060807081005010503121e0406030614180a09051002030a0507140c061617010e09070b090a0909030c06 67
    0x1140040001319202c1c021b9000c11155035809482c0014080700741c1d12010242283c0c1846c044d61011202403110240b842d1580c601c84409104020144c2c050310203d030758004110794030004001314204070134201081c44071504c81c04905084c0302c0013041c0c60801c2d80d8030307085030550009000c034802c200c150001048017103402d000d103e01405554006c1c009807454841d200e442c1009405050400e5424600104543d50f00802c01e600c4281a100e10360350345076401c16440d441141c10912407131006201007404074045034990711000c10345444c624900c1400308000c2c1041603514040e04d240d45880d45442c002120f940b40d80d041000410710403011240101103003801d250582e0000c40d44503031000c0c3d0390420007054560000d1810000e00500410520b41038010444544a004c028000001001c802c422040102d200d5046d0f20340b1003c10808100c0156100e102d15a54203005580300343d0588506540850b610403004221070701807100a04408420340b900345078030083c0c007140d002901400413061100001c9080e41c003840c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 533845449 1250 533844199 533844271
    0xe01050f0108061c0c09060501080c040905041b151205062b080d0b0301060f08030d02030c09040507022a0a14060f03070806040f05040f060b120d18090908030c03 71
    0x10a01d01e1b030401044201319411540060b040283c40c0092000d0b40c100a000c40f420b40d03107640c40208045c5e0315401c0003611161340503014401c2c1c45a15000141c0c0408070319032507488920740d6070fa0349815003100c940c0c8803d4401c2a20780ca5485a041c14046005c3e480030788101c4180d0f04000f000001020407500c60025580218a08603801d42d11480c001e840d91500b845624042c004134295040082e04207030000f0341c4c80c0152042440d10f00d41c00004074103c070202100790b0b007003d8001481800b81e07107448900251100a90700d202e01c080c0c1a075440343c1c03404012010070b442407040050040703c6042c1c9805103a40748400e800c0c0341c05070000345c01c000001e442c0d18440010340c0b14100c503484454403420240f0511040320030203001c51a03800e1a110600c4005140754000c01622a04203d020070300140c00c0b070019045404c200400c0846101e00f980102001b41c00030f00060040360210716401080350307202e181d50142c50b40702e00010300c1ca04003040021202020394001c3d54000d142c03a0b01c911800c150280089070300107142945 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 533846699 1250 533845449 533845463
    0x40f0903050d051006020a240608010b030706140f0f0d0204030c0617071d031e1b09040302060412020102040f0609080f070e0a0b032d070e01050f0108061c 68
    0x5100e001c0c0388140a800d07000010b14008401051030400000c0d10740e440b00b180201041c000d040f07140400700446082c1c030140708823101c08000c0103a90701c2c0118000c01014080a001e0b0207518000130b0b03128091050380c0780f0080100d10b40351619079030322119003255116046095000d4000e1111100419841c4087c00185208058102c055820404090100200c141e0340e184004c0d142d030b04100e1844c0d0f102054078642c0a001c284008401b0301c810009003820f03002c0c6c01d402400800f6807200561980000340100652588c04a1b06403006001400d0240070030040f14080e0159215801040005100300840082c02c2001d10006050503100c400c490914140c5501850008568000522001405101700403005502c60020300b02d0354602010034421000090a8440280c0e55054042c9903032410f000007040410380b00742481185488100816802c170401103040254442c0c0c09000c90072a01e103082c000c0c103998004055415007178541004640002d801440680c003d1300b81030396007050a241901c2c1d41c0c040e52103402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 533847949 1250 533846699 533846707
    0x129030a1e14011a0108060102031603081902090d02010509150403030509120a02030a030f270f060801030b0406200c0604291b09060c012304021e040f090305 69
    0x500078031805002d03010010a900d401011031410702d4904552064070404c0c05d10001c5039450a0050f41507004d45c1e6600300720a4a02c5403010b0406500c0a640303403090038035644e0140f884606001e00c500324010355a00036001184031705044003642c010307005010b1180004040c17501107040802030034a6900b0541c400c40115901240000d92032404924142d4117141c03000c02010028204c0e000030350741c0c5412041c040e003070214001c14040074501c10303031400c0454240072045a00d0a5400c0280240c20034403441400520291003901181c030900c140405030482c2e800c0703802d264140c0c136907488040081c148600c0703c40e00e401e01288401003000c600c20146c00f9489105014014900e8103080c01300300d0946900c154080d5070460060091414030340c054868111881d00c4002c44c03906451224000144034100301c02d036000701d012454203c00f010541126042440c1d043d030f00440c2901c40c00d02d21001d007400303990013075000a001c0100124041e10041324803d6220080010a02e06020200d090031948603207416800104002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 533849199 1250 533847949 533847953
    0x3080907050904020904030c030e0a03200613330201050f0108010b061e09030105010b19030506061903290306090a0b040b04050a05060c07060b030129030a1e 69
    0x11008500501c4150303000c807240e1525900183d44407100400c0201030107005100401071510600c1c8020300940e014250100321a2241803e400001c4580b03024000100c4e002400d410f40c0c00c180f000c0c0c0d03c00003449810300070140c2c28040c0240440502c03445154100e207150303488a507501c1c03c2d5140c40b9a0400c1e160000a15400d061500c4400008141c0110040b07078140244204503403a02012651820381811034402409452900c62030300344240c5080b1581907091800210307811034036030010184208581c008018050b4401d40980544204444440c4d0008041c814030081c038010003100d65013080c070741c60300013a81402c1c4111150f4015010000d4000400d1451070402d007420704102680d003005140e00200007042940c4e403090580800188010701070309415000c64100801040494203a640c801c00f0f03101e66190107202c1c2c80054020313481c11759009042c5015000b8a04042c41101800c1c400001c04030301201440d00c1c1901c0d40c3c03801c882c40a406100c2c00c01c40e900880c1c0b070149500034590310095203000140c094 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 533850449 1250 533849199 533849203
    0xb090c04050f0f0901060303090501051324021b01020a1722081501050f01050f0d051303030623100207080a0602071a0f16090b03160207080f06011806080a030809 71
    0xa090060686c0340150900c082900042c20b101211030034a407142d6100c840c60220070074041c00394020f166224140130700c0c2207402840705004c04044070755402c485004285904454501808054450240c2c1201d003000c0302144414004040c4c81e941c042103207203003030a14030443ea102c0601c020040405100030b8400d0013038900903c60540c0102e0651001e00c01541807000058076003c0040c0014107001d0001203481c004000001034031030400c0c52079400c010328a03182c0c454581c00c02c5010402c5001a24007800840e000d01003110199014011040c1101a07240442c18004181b09515151041d4414460002801407040103080c20180c4070785005610f410461030040f080d010090303a0903071002501c4040240440008100e9a44403015500c0901e481c0c103460390540340104150810065054000100054200a01c4803042c948020b50308841c40b40384d41d404400d8032110901c08403070098009000404c210044544060195403c044001892641e5420309900d0304541841c2100440c0001c0100500c686007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 533851699 1250 533850449 533850451
    0x30806030616120506030a050a0302032101080a12270314032d3106091802220e0403090504230a060504230a09050303040b090c04050f0f 60
    0x40c24050107107030102c1070181000c840c44440e001d0084da038030005540d5a50030050014850382110641e8a40b00d43c6040c020746039841800300304074a4600080c0170300862006540d1034101c809400140c102c100455a9071007402106032030040400c00c10819024420580c0940c0c551940145101a11020324500e4481c07444000100650807540041c000d004c8082c6183c0c030b9900c40342c49e118101d5010810719000003007090040088051201c0c080100502c10500c500c03031040c200e8209600b001c4003180e61484200c458007240c3c042e9026111100003a40041c10709600540341034289800b02010581051400306240e421b2903001d46032008051040c0414180c2015444014110945090040001d1114588125103500038041039150401000806014840d88110040c100c01441481a40e940907055500c0314040c01e0403140d40001031012984c1a209845401c0d0819401009582141d841e600c03820034a010040104007503005200384d8843c10f54440c480d45100d00c42e24031007104c09003024500b00f095144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 533852949 1250 533851699 533851711
    0x6052704110328021227100506011d130f20120703050f0115050c0a0c09060602060402130b0310050c0409061e0e060f0a0b07030806010819180803040308060306 70
    0x841046842250b50400000b02e81c00f440490203020303024640d6101c24a000c0061031301b6581402241c104501c040e00a81045000306000d9840f54080414000c0c00c040411454000c50b9001c2405400040f010b495901722040c6204005800030740c0003610b0903013400340c10002550082101c000900e0720b200304200d06150707802141d1031800300054603024201043d100018010703200e604070030102c0d0b156290300c1942240d0300c0c92141002da070101241c6140c400c01c002680d0040440c407906000011421620005a083c881e680080c0302a040b886240e00d100000c0000452250b01400f0f040e852074040c0c2c425001e0503000780790301a04240d0300c40c5000038440403108982c002e80071000e090700404035a83d00c1301c1c41c650140c6d0410116001c550320703440006900c400c8011051030304482e11050015802403008060400140a6100c0301c0041e510035004407141c0004603103002c0c0911100a01c80c201e024258400d41503a0070003e4001c29404040c2c8075002e8a800403902180000d407094100000c1d81800c4c051141c00c04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 533854199 1250 533852949 533852951
    0x30f040f0e0f0f0403081512060108010e03130b160804030305090a1d160e10050301030515091e0102040902033615060303210106030606052704110328 66
    0x814850446400c5903c040d0000c0c08000242c40803568202c140075418014200050040180e10315402c0f00f140c44403800d229903201c5510b008040c200090000c4110340500200c41420a0004d042501c2c10700030760060501c49000c1100c082c0741d0b00002d022036000317002450082d152a40c4564400f010030036200d4898012044800310b2500800c2c1d1b02201e40c19490b00121247c01c180300342c0803580e00031a05692203c4c016940321000f05011540ca0341c00c040114180d0f80a84161181000d11141c01040e00754295240f46440d0300544201c00a4900d829064516040401c000b500c1c0035600c40b006810f0b60420380c5d038075003c0b1094150340c00030b008403406c5040240382c0196003500c4800074990003988a045010a5501148482c00024100c0e81e0034022180303809405041d41e40c441d01840d8814426075824014080440d01c1c140003ca0782c0b074003a6050713980c030b400c0c0c18804807401c1d010301400c00c2d90a0050303403105410a40700d5100042c1089403074007951160358a01c1c52002a500040700c000320904240603144202 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 533855449 1250 533854199 533854201
    0xc110c0604030c060e040e06070509010e0a0b03040f050f160504052a090102071a0c1b06030c0c030d090b15040e0a0206030711030301060206010f150e1002030f040f0e0f 74
    0x82c22005040088a1300d42c10142d402550300070105014007015501d50742107000726401c008140c0e070090050719070080c0c00c2c0d0300c549148411200b801040f1102d4043c01070400414000100058481070a500410784204c003074480078a10420075502d0510554940381d100c00d0500428031080c2403034440c4590020102c1c1c0044001801000c01e40300705000b0702604805c1c071100103010000f42c6d000304551402807203a010746803001c1011f8900f10b5001d80109010440c00d0040d541c500e07002d402d010390720f040034035001010700740795441d036042141040d84605c0e00070f04103000c2030000724188031040c818088800c4c01006034001514200007840107143e608040d8610841c0340000761341c44e03500001100c0c5d44a5506079070180e030381c0d201c085066420245a4a03801001c1c0f00c0000003181103940440c45a04031426000e041c1d030451b0f00e4103445280c8803400d0300c16100261018401c4110341c94840501142d03c2e0240c01500e00d031105d040c406040c41d50241c0c2000e40d04c11220941001002980b01c01076a001540050303000705 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 533856699 1250 533855449 533855453
    0x3020108090c2103040b13090c0807021f06080604060e0d0903110603061804060902132708040f03061a0d080a03091a041a060105030907030311030d0c110c060403 71
    0x2a042c2401c010b940c000103c1064100700800700b0882c0c015080c0600c0349a11401d80030040c18040c040790240c003094038101500d502c6c0d01400b904400c0d000e00032a4025020062451041c052081a0701c4034050845460b243d0015180005020550249018800200b02d1003510f60b15a031a0404041005041000c04401040455840351141220720030850b03405940c1d489610018521a07501c0703004003c01c40209050104000d850380c0140640c2d40f00340e400d00d9120600701c01400031600184410880341a00024800304001042c4000444910529045090075180c41141c589a046034004940c402d83da01d0003038078900b5402c03100a50441c402c0340e801160841c25136604400f0f001744541181456200c401440401c500b0005804840c42a2060501180703400c5c207041007802c001210308a0709090201c0401c1d12075106804803445003654034020417802e071869030101c8403501c056420f042c50b0300061002101c4012503005081c4901e91075540c807007101c0240c050641c11b141c9044540c503ca80810842000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 533857949 1250 533856699 533856709
    0x509060312031e0705130f0e0a090201030e010c020c0411041203050309070305012a0e0901050d030309050706031d160504050901090615090e0a172208030403020108090c 74
    0x21010742042000b52a600c6035203001924081e152070000d82c0d49190010820819070200c094114030031038648924100e9544c503001460340000303005640c025400f280c00a81d0800040c0c02000a10344103250008501d14040525401c4840c41c40f145801608029402c80b45803802c0d001704500c850001c00ca1030b2070249004000c44402c1048200101803010100c0050500b400234415000216000310091040c04410b40c40214031305000c0c041410810f0301290440c0c402e61103107080c04000340020300114220307420300b001c004801a508004804064440292600082e02804a10001c0c40b47d034601140401c6010880d03802c0740c49a440104140c1e01002ca0030098240707110104044580603a0001507585484e5034032405420f0081c0301804050810004159103146254081e00708c0d070806804100071180003841e03503103500c3c604101815840c6503a96403010110700400030210a406848020030000d116420311014940075444240769400115003007042d9600448001d0b4440303030120161014000ca500015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 533859199 1250 533857949 533857963
    0x17060108031b0f030f071406090a060506040906020c010e190317190e160812180d0f05060a051003031d03071805010302041104081b0402070c0801051005090603 70
    0x40401280701003844040c10107200203d101030801058a41e0346a041e480c115032580b0600c001ca40f145c00d0030b040c0d04544030000c61243e00586400010b00f003803200396241d940c060800540100e900968030255030001811502c02407040081650002c2000c2c0680d071000c1d0b0400f4810030401c44041c0c68921070100180e4411200314150b45c1d828030450b0325480303c0d111040c1d55841400b8404003c1e150401c1e09148410018441c2644160803100c0f9242c25111400c8a84504c00303948031010946060110040559500f800085c0f08103010b040700c0c001c4850754444c0034955000490907140c5400c030b1000e00c01c1031440d41c0a41a403004c0356849140f0060320b182d40040c280c22000324503400382e070301d50100c0c0d42c000c3c0d40622440c00145400402400035009a640c000b00600080c4412813013903181a4619155038050000c0e10b00303c506000c050006420302c66000e070168100e0012880d4401c0c0c3c2000520b0004c0c4280c010600a080d0f8072000103035070b20341010032900d2003959401540c82540e81c03000700310007a9000207004d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 533860449 1250 533859199 533859217
    0x7030c0c2c070c290106050a0f030f0908120702070f14010e0f040507020d090503061005150c012306030610090905011401080c03060109020315100c0b0a02041706010803 74
    0x21107915559110308841480055400900401030039451011070141505080e95403850032400002a980c0c6480543e421700c00d6140d040d005c100144503031298a40a80d02040002d00c0b80803003c18076042d66564030351075030300003240e00d000d0240b09018800c0e007550402500c4c000e032461036200005941085988110802049500b504220070740340754508940b01c510018a80182c0940280310300c4c00c1100000c1c0d02c65910038640c800040c06100300051718540080c01c240214034544403081902d04010500030844003481844003085010451220304240912455446101d00c018200d04491640590b10901001508135031281c0e0102081c840c0c807212124061003103c5003c81c000941c03071080e01c3e1a034054924441d10341e20800f852400056040404600160003c00840944040f6a01c40040c00700301d010982d0007480c3c20070032080010403404c0038450754010030840e041c200e03464900c564900d0250b40085400c0800542c020504010f0b4100c0560941c0750701004202801466042c1038019a4038010441c1d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 533861699 1250 533860449 533860529
    0x603080703110f0d12021c0f05071b0b070f050c0303040b0f06010e0112051302060d0c020607020f0c1c15090606050406081015030203060103030521010b09040e030c0307030c0c 77
    0x241f84960070010508006081c2005204000c03d40a854005102c11605200842c2140000030403070074240c1e02c1e20074a194822880c12440c3c4540004680ca0f2100e003c0d120b0078010200b2111401a03010400303984100c7c42011400100d00e000c1942035100903002d4400341c1803100010088403240e030842002028a261003900080340d980d211000040ca444450010790080d81c00100a03d201c1c280303801140384e0101d039800b1205e5a445601003280e5455403103002c00c5647d0007040107081c0c0c074034080c0900b0700410b1128000e00b1205049440c0c403490080c0805150421990780d8100904108803809400000c2c14101d4040015501e022a00c0761100f4000c4040301040d80d52780d15040d02c090310803613103030040d42d00030301100d41c10b6859150243c550360015800501c8861f035252202d0041901074400383c10395826601c0740382403441c9801440f0241019080882c038a000a000035100380d0810800743c41c0303440c025030b50170006600b43e08200380c07278000035008031180c140814900003800308804074043c5d20b540d590740 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 533862949 1250 533861699 533861707
    0x8090604150209060a0c0506060a0b0f0c15013c0e09010f09080301090b0307051302090409210305160f1107180218030c0319060603080703110f0d1202 66
    0x1000710000d1189120340c907441080032801850095201c0e514010340c610481c2110141d03200c020400c1071918162040e40980d1408000034509002000c001d0110000c0d100d088403c0a01e55941205c4104002d070800e06580d40c1c44041c40109450381d148e05194407140a00f90b0007a25100790383c43c503456060340544000c0c51920008603d100409501811886500901c10815019107150000c0d06600a10424205d00d040483d06e041c640b4020400200312040104404503c1a24414110194120001481d8440c0d07603078150380045902e4510300d0b64030091103101d036607030b28990101c09030440f1009000e84020300a0701029017000350300130414100c051690304010580913595841545404e0454010005540716449418171015054000d464a00110041580114181000d1503070358110000c1542e41588040c800e41180030105092009030f40c002c9c030300891419229120035426078440d04040b40080e036141c440500c04d2100f8490081d01c1c00d15400074103c00c50052400034040c14151a44504460f4001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 533864199 1250 533862949 533862983
    0x1c0206011a04050a030c0e0709080c010309020f04380913050304170105010315020a0c02010311040e1608100e07031d010504110f010302090109030b0403020102071a1608090604 77
    0x141c00d450003000010260b01e1000d03213174074150540da07070240300341c015100800012070207660150603038500b07a1342c3c1000203100380c0b018000110f0162109000580c4c010982caa010462a00c40d0300074422074100c00c4442020313003901442064100388210031904040305c800301c1140c03003507901c00c1d00003a0030801c20008910058a18105942940b055510802c0302982e14950500d1043d819000f640c1280d02859488040c05100c1500d20181d1040106000015a40d90350320001580254000c40d0768103406090b0b035042c540c43d803814004011003601c9440c21106202c0000d00443e17400061640d00c400c0304004040c1c0c003850881d800341601e02c0a4048410705807074400201c40c440458101c42c40060105000b4421030030141045007641038400c80c45070060500d05030742c081650081c00ac03a00c5000041c0d5680820b0b52464036048003009020303004604554007000400b001c2201c0c0040340c81d40c2044c07015940c105040c0151541c0200400700c1c503400c1400400400c100a03c0808102a0380c0700341c200016450500d451 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 533865449 1250 533864199 533864249
    0x4050c13080f0705060f03160302040906060513120f030311070b011d01170d030b13060e1812090607020f090108030a030501080a051c03110301030b06031c020601 71
    0x14000030115880c0e000000100c089000032070115054244040d9a80640c645041c080c40f4451b40200d030101900800c00f0800302c04400b46909031508192400500701034482c041c04007a506aa4040b2000070404105051300d0a1044192001008402855001030700075030741e1040420b20110014007859a95210070403520a58070494551942c80700e0300128035038480f0b84071880d00880c031042d10b10080252001086400042074100410348542000308141501c0f42000c0380506840c26074150048e1000500320810103450154201400090441402c14074010340c280e407011015500740f80c00d5500c9640c1e5100c0306420041298400c02d019500150360329624000b0420b40020b00601d550403031a0170000140d4075201202801c106189070341c00b8041c5907610102107540382d45168000d40709403c810081d0002903040800d51605003201d00b404501d4180800c10480150001d074010360f40d01c120101081158501400500040180c542840c41c04800e0740000a580316814006d54402204040402c0c45d02128 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 533866699 1250 533865449 533865457
    0x22020402044a07140316080f071b030201090515041401060f0303260906060f030f06280e01060f0b07321002070227040308192a0e0307030204050c 64
    0x1215204d640d0704e041658140e03641500c0b9005e0500003650301d0700030a0150400b50b00c8c103030181030340d9941c00700f0380c0700344422421203030030704031404c406540d030b9100e1000c000341041c01300740c02d90b080c5001089054600750424045040903101d1403409a49051414400d00314000500c10540f42c0500d00a0482d0840007200000c4211b4900c201e038500c1041810014035035400201c2c90310895040d2008403029815030141f50b9114043c041009150300000b00155070320390308122001d04174031b080d1301c681c086020100390f0394115021441d01c82d00d20794442c1d806000c10344110140750020700d80c2121051511804c3d1b143d090712600b00c80440c90201305070168414070300c15040d4102e100480c020050321208003001c035408000390b10916007240115508031011400703c0d13000f6003002d07080342d038401d03c1e410580c4d4595041741c46c5803006100e01025041410319601c100310b1880384005440b400d902c4400e18132120310340b9030400202e810060b03007000034201ca51035003614042000b2049a50645000c40d454035034031042140750003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 533867949 1250 533866699 533866727
    0x5210705090306040b181f020c03041a0a18080a140c300a0b040303240b180f0102030706050a1107050a03081e22020402044a07 56
    0x85418188414060a4014030b40600011420b09440c07081a06c90107032140090b40c480307900ea034140d030036140c0c2801c03140d002485040c1400060340d242a80f82c905c2c0610350760642e5210b81d103182020400c101c01c65082010f80300e1595a494001e0b54003403620036003070340c0c507090315200070700c201100e0b5046070365408100a81c01c0040c100610390110315661602151b9422402d101c41c903042c000c100c2c0504904e580228a8220080c1c1200e9204444d40d65a01c05074050910001e00414003030440b50007080d030644400c3c805014280310008195201c2400e4180032080001291079841048074960300491030382c000048440569102801040c00d45d1001d44140007801d080e0024080c2080c0091010704100000c039031400040e201e82c0300e20400d600c07400d801c40300102e810141884050300e040041502c6031100120900105050b80c0c00802030080c1381c0c003140503a00903501c02480c91465400301c0c800c807104401110a08009050282003000300c4410a01303056070682c00050010081c000880d400340d00c00c626a4152007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 533869199 1250 533867949 533867953
    0xa030c0b2a010e010b0406031a0c1201060c061508030307030c020f01020d0c021c09032004090302011b050306060a050f04091a01090608100509130c08060412052107050903 75
    0x140c1c000072650103426124105400c951030036281d01c0803486c4c01d00c80c50741030b6600841403141c020440d0301e20003031022001d44040403d420034000b4070354401c80e41240e140a0800303555120300c40c0b616850070b14203843c84c00f82000c80c0d990b00c0c18001d100b41140001600c1c0e0001240ca0301042260b401a410b074200444031401c00703515400010180320916040d00801e6400219900302c500000381500d000034041c85d04a461000265103103400c0002c61002e0b1003565040c2c0c01c1c40c0c8400c0100031030f00001011554440300440140c2d4640200280707144d1000c90b004403d11041c10300c6072440c40d09100040e00752280000640902c01d010602034802c17408141610045c0c01101420031004010407420781000c2c409110841c0022071800c804144507100d40406805401000b144074516030408080180944005009066500e420810140842e000440aa00a01040d0080c0120303090034100003030150075145010042c480208030054802c20520219120390083c2802e00155442d0f50703000712118030402d24569454 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 533870449 1250 533869199 533869267
    0x605030a0f140d0504031b23032e0509010e03070803010806070e1008040305090409080c150709060c0f080a020d02010f270602070602070f110a030c0b 66
    0x4151014081c007400c0c00381d581c0c01c040a070000c025903a20701001c402080010800e102c01c100041b080c4034040318044400000c1c0440c80d803921155410200d1000701e80c00554154501d101c01c6003800e10030803825243e064450002c1c0d08001c503034448064024120312580503035030700001c1ca0142c0290f00800e11300d1011002e41c0d940e00e40d10b08282c41150028024220640141c10104002c10f0140e132400c0001d800240810040c280f007010142c600800041050b801d1180410456009540d180715000d00c2c240702c1c1850742c4e2a080448122464480b2040b5040e9044000c0c00c140310703416030401900c0013100c1710385c541301000c070002d460304840c280070403840200505030205107030000d16008101c6040c1182503030300030004100400541000c0c1c8400e601a025008441d20030001074221251542c803996000b80e8015103485070640e40c8108076400b40100303032140c203048100c04041240a15110216804c1203440320821411511214244e12151080c0404400c0014603021600c1d204459001c0611003030040c4151 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 533871699 1250 533870449 533870453
    0x1051e04030f0c0f03150911190305010b090c03160509030312041e03140c16030606050a0608060a1502010b0a060f02071a1b0304030f060c0306080a21030605030a 71
    0x30b60440c2490480d02c46180940100340c0c0310900c4604421aa004024040d4021201d4807440090101e41e0003078400a500032845143c07522010b084d03000a009495401c08454035508160303003181c50640d00d1511402c0c2c0c800901c541103000c41c3c240c0f50440740e5100c7c100d5400701c048a0540e494817400b07000c03a42501000c181da003c54881481c001e486540140b1009001001490110503080140480140401c2200d400e820181d511403015121407018001250044000400e920280540b154012104180c541c1814040d5040a01c1d040303001b803100b0b0901c103000341000301c000b0b04000114021492101540d51074404171602c00d4004d8070309000701420082c4201e48407680108082001800100503100784400012001d10300700709141e040c200c5044103806d28044010144035650210f00c1c109451105000200128000c103190800503031068000054000f160034002d4147c9200e41d21180c0b054000d04501008922011914030104880c0050380302d07050100b24003075006007516000b081c0c05100f81000081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 533872949 1250 533871699 533871713
    0x41401030e190c030b06060304032c030f01020406030b0d110607020a170703200102210c0d0801150306030203030d0c05040801060f030203011107021c030201060306140601030606050301050d0201051e0403 89
    0xb540e000303c0d0320000c0c80d1b85a9040c03140782c1c030080da8010000b8a030748041c0c3c1040c441084a00c00f103d003100e042200c110710b604000a1030200365500e41c04503a5800503080080c640c1601c55030100c8641901d003501642c5190f01c5500364400d444003034900801c000a403600c21595031245090180020b003c003070a0388100c040a81ea034402150000300c1c1c01c4c8690b0915030804031500318500410440507070041403040d10001000c1e200c0451001000700600381807110b105803c6081c0154511030030700e40d441d406107602d4503820156401100d22050300b4145006c40c10f001580b000300c02c6a000c101c04010100f001c1495103011101c030305ca95441318800d07511740400812650b20105102c011240202d0013130040c2401d00440d03d140388140a8029840a54200018415904040e10b00a0386010f400001541c41d940d4640000b603603210400c48840c0040f203020800d0329038140c40303030303e01600311407403c0e07400d56040101160600c0d0061300041c3c113204020039401a440400f072504810f0310540700205499030781c0c900c1e01c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 533874199 1250 533872949 533872973
    0x7051014090d14010b01020c0609041503021005070507150c0308060a0312020f07140f090702010e0d0804022809020705190f140c011b03230a02070803041401030e19 72
    0x71540c0d4244141e842c960f40c4005042c80c12140018079042c9400550f00812008cc500075040b800356203085400040543ea03a040c1d0035000f09103c1d1a01caa44a2141c5007490410b1000e03080024400f0194040d40b5556522a45045c051070f03160528804503102d0310001007454215501c01450700070390f510701e005070a6010800f81c03108440320341224291a01c4a41100c0800003006085801a02016038056030780f400e11782a40d041240c50000007081002c4c0c5003028148249001c5c40350108400b00e0920046040231072184891000c4040c4500040444256102c0c60194070b20940c104541c0100e245018000144034481704210710400e6011502c1c603d1400003454000318100750307882c101c082e0070900c4c45030300480c151850050595400000c401c40b1415440c00d69145581501040f503405000281c1c10041d10305200700170030b903100840e00c40b054100028909040742d00200540d80050208002000406290b020250303003d00f400300300808e05100c16440c080c2c84004120b8200006175090041c0008a400c00d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 533875449 1250 533874199 533874233
    0x6180a06061403060d0f0f0609060911010f0e090c130312020724050a05120711160602060c0307020a080d020405010e060403200402090a080f06070207051014090d 71
    0x20078202c0c0c281c03540646035020440d40716802100500d00b03200026884000400c01906c41c4049100c0c0380044c0d1900c42c100c8154100444a1554496480301444803801108441800c01d203004910681c010300001c00c3c01d0b0303c500c0218001c01d800d6010030000b0044e202030310110ba08240600704003903031324100001d408100091240150003200d50100b0003501c5540d04564100386603109044a8070000c10441c1c4607409001528100300052040c0e90f001d8142140e42030107010103a9030444c404000000c01410008207116000d41c840c425602048440c1e000314a09502c01000070401c2d03201d6445c00f2040c0d06000b8511070060828030005101c0c2650032507507000d0030a40e0400c0c2c0c3ca903900000220709000041c4110300015054151181d90300341d24159601c90081c0c0104041e00c007500b031210b91400701d40029659044020150480d203003400341c0100410a442d80400c29200815950b840d082c0864415960001c404007004044010007207090701c00720032160040c102030003916021a0070f08000410b1030041944e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 533876699 1250 533875449 533875457
    0x309120106030b100e01151209030f120510051e03151e010614130e10140a0e0105090c12010b030603060a1e1805030f0c060f0403080f06180a0606 64
    0x40780c00c0e55000500b1006031001700041144590900b4490088841002604401c000890200e031503084503d01030f000f03041d44261100001450a00805060100d800b250341201d1032030203040007038881541c80910111041500d403d01480c05449440b01c0e0700c4110404581c00d40b1845500d011045411405244100218640e0030701801c2c0e0f055600e0745e01d1000707204100000c2d200b48400503c0808203002040124061030100c05400e6a82c29203040c689001c6503000c841c03c80c0b60904010f000c0381500e040303a030094210390040310107003410144144410107005090217043c03a103002030a05140305003210030b0544244e607408501c1da51007001c1216540102c034100d000e4044c0901050108186016071802e000f82c00307201e01d510340f1089200800400200304054440641e251168000c40d900b0f02c01000c2c0340f4408001c0036034400b10200d5107032410001511072510302d140704d8100800300e40d0162500d0303001810b0705139242d8540c860b280041c011181c962440d1069400b0b030002d01c5003500c0c0a920140444176039842d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 533877949 1250 533876699 533876701
    0x703270c0b1b0d110a03030c020f0105100602010b0402040b0d1e050921090d03080601181202211506040b040c030c11010b011224030f02180103020d140309120106030b 73
    0x1030100e41044051000e003c15a002c0740798400002d000345c204a484d010348c1d10407600391205017031001e420b5400940d5070702e2000c40c6811060140c0d550a0059464031101910158900b0f440c00c0c00212651051035464200c5960314402d1100e0810490024505810521024400c80c201810095201c211555240150b0034101d200008003001700001d4504020008000070500350383c41c0c0f015649240000d15850400c47e1007150040295a02c40000c0050a50800420780000d0710748107008141050001140c810046180c8181158000145c22881c0d04440703160010039032281b40208004d0008842c041c2da225090a00224010303074103600c0940381c0040741c1c0e2500d42141d080d801039800c03240500d0020340041c0c1003424000c100081c0f5003000541e911010240f0200040f02d0f4800c0701022242d4204540c01c1000b170072200f05501c0d0a1901800c1450759581455155145a00280788031042103001024170110300040f070300c040b0040c41a03600c3c801014007030180c580e0320035400c24024601c030302003285c60303900c940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 533879199 1250 533877949 533877973
    0xe0d02160918141f060e1f1202010e0a0806040204050129070c030f05070314010c050301170f030f1309020c121b070e0f0703270c0b1b 59
    0x8021480121404a404030ba1040ca6440703154030305001e0620500203202c0c400c01200038603001011444400504603000070b605051401c62444200040d1010003018410203480440300344940d08107048071a0844034289941c0b00c5d02c0180c030141c0c1548034150788070b54809800602d800001c240b8070710840c400c480070400b507a01c6000010142402042c20320007001014007a0350441581c100800109004201c84604c0c0c035981d56400fa0080742c070b00400c0f100340e0400c01c0c042082281c9200120701003510f5000034490000e11820043c910700051058507256043c511003610100f8050040c902c029551805984c1d80c0c804e0340c042508560b00c01030072510609140170000a24550b81d10030344540400d004040d010619102814103441c2e00b0081e03035461103c003180800c82c0d03855010051a0300030900584420b06c98a0054248480803d00070310716001e05040c00e2001d0300900c64140c5002201184003540c48404070241081c5010b120f2540044c1500384d000200c4d46080d1100706803a4000454400484c2c0900800c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 533880449 1250 533879199 533879201
    0x30c021e0c010507060212011d09010203010e07080705220f1205102307021f090308060105220305010603020a051801050f0607150b0f01020d08010306050a0e0d021609 73
    0x200d1400c0d26500316a00094096202d00000e0104900402c0d002d030070f00e80101d1002c030403003400f80c0c400e55400d4045d6030400b048500300d45034540e00217840340c0218110740c9024045075502500801000400c001100058903240c00341c41940c642401210244d5210445602d480c004806140078280807800d81c1c50b00000c507449842d5140318490b501c072001d04481c102200c9006c000d40071041864040050400700b011107009070b940018030031708003580100041e41002c1d00f059002c140d82c802c507820050402400390b000c00e03040035440707402260078039107540c0d41d812035220758410b1814500c80c500c40f5581c40b4000814808150000c60540380226803008449560f031040142ca0000160700148a036020b200410880c682100022418a0b0150080c0e190044580e1401031440380b050311b405031182c2c0c9054500e5581400c0d50040d0207180d0038002054502044903001d4458241480006d0540b034840c1c00040310a10303140c000460380d8481c20100c4c1c50000a151010b522220799203185000d00f00e038410002666111 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 533881699 1250 533880449 533880493
    0x20708030f2703190e030610030b060406030305070b040203030d18150b09130201120c030e01110301061d0f09010609140303030408040306200d06050109090b060a0f1e030c02 76
    0xb012000750714001c10b00101003080c0100700038410a1184400b0342009030f03142400000d20840c00c070030170204140e003107241064140c0c10180c5840d003d10301e030103800c3c80040d41000844034840e4101c0d12568155a035440020710b948070f4070080301c00c107606140400f481e1143d124505120a8454045512100400700c3c024040741c0c101c400060f40510310f00c0200300d82c0c042cac0c0d800500c145401072520465001c2c01c030b410407081d5040340c000d0b2000039507112030b1765030070800a1140b003084440e0103940782d146500d1310000400d41c0602d0001406a2054122520340a9a561200d0441481c02a290703d440c1d42c0c0d01e185c0908140114030030b038110041710b500860018074001c412a80b090b83c1c0120801e052504544540004049a0184052810800c1c2d1002034490560010b04501c07800c6920124200c6d08180004001150a43c07040b91107034104025820142d131028203130f035030501c81403078800c1410300c251400300c464890f10490480e4107c9014000007815038150448020245c1503001c030342c400c040f00c101080720801 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 533882949 1250 533881699 533881771
    0xf0a020d02010c03110102280908330405030a020d09060c0803150d050309040605040b062b050f061203090306070f180810060506041503050a020708030f 67
    0x45008403001036000382c1010050710300920b001006504181da00d5030882c0e0154103616094440c0700000f15428030300b003543c518080c405241481c481464285110756a02034140f9403403000080700e06064900543e02a07018034506d29001892090805040c2280c480e03200e000288014050b44650740446402020510100c403d04d6644515a40c1c0b15101c0902641029101c0d000d4159007588243c1c15a4030324218100e05401000a9a40d8101d61020401142d2060303000500543c10011901c1c865519913003580c050065031510f4210091105100001d4202c4034182d140c11140340c0070a01a0b080741103010140309820954000c4000511390782c40c3da07601e00404680d503178554000d600107151103100302d507801426003035400c0400444038421041190a1004e400c04d007500d520540b0300c5540d500e80f0340614002071100340e981d20302d032505018409203072034022545001816103590124004555560403205141d4104845c50b4a86c104811860740b141c606030754844001c0c622050518110801e4614041603407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 533884199 1250 533882949 533882959
    0x12110f070303030209040b120c0103050114091501030207050607050304020a0e150f011b0803040c0b04060c06022a1b040b01020a020108190e1e0a0206091c080a09080f0a02 75
    0x5480c5030b8045010303500413501a03030050b48071100c01c0440d0700d0b4021a10000404d00000e401031000f04800101100c8050303000881c02400c25203e42401c0d00e92800303239504603030780500e000c0b120b00320000182c01921030144010118410441085806940000694040c0c1d10881e0b070040141e039111008a0908001d0b03d003021411043c0c4802540c40c81c0000c0c1c0001080c5043c1844800500c140a816642921612050b1102d031000801c2104209099221030007510088561a00b02805c0c103400614000c4920001082c45900150b907112041c1080c00c646130700c10703140f55480300b21050304c3d95076511506000d9114102505207100d5034464a8a80291004c0f1281a0f00414441700141c00448001d01c000d0505984c00d5070a2042000310704107401094030301c407483c80c001c02e001e01c00d6001114092030384201c28041d6410a101d60801a81d8000455401c01d82c11600107000030024440a61a071491030310090a410000818519803500320b861807040750500d40c02e440e074030320f407515031a41c442c92140c1000b9800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 533885449 1250 533884199 533884213
    0xf020c06030c030f060406030c0815180a080a030204051519022a04020c10020304140c0d030509061b07050a090509070b3610020318010e040b0a0312110f 67
    0x104e0410300c895500060091022482e00c0d600e8035a03800103e8650460110b5401484000311045080280d80e80c000412180f8800f4031070246036100e0301d035030344210010400e19001403015041807043a01a00d000c0d00c001403c0806401800c0f040500f0b9501000050048410513445050011300220f4200080d682d00d01c0000000701d0340d02103245d401c5641d60806903000b64207000c1946945030800403030801040507000107950b41058100500070040c81c2c100d4803032540c0b18034810011515000d1a92030000c2c0d140c181541c807581a8000941c0c10302502d0b8591402e60403440d41d0b4031454100154a408403481038410309a02e507110342e048802e580d01104e061b6490380c8260420800f112150006203281068071203040700350035030030842c00d8a5039076481140000c03021400142d00d032481c0411142290800e20b0000314034000340040c0720869000311710020741c1405040c034182e00035502c0f20303000800410710040011002948034500b41800000201e29000002d03644000007011400c00504d201100c07007500014100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 533886699 1250 533885449 533885461
    0x513020a08010c14130e0f010e010e04080901081e0403030915180b07020a150c031a0f0f01021906050906010b0a08040b040305041505030a0f05160507051c0f020c06030c03 75
    0x480da000301d001c5c005503400142c001800095003407a0f24040c10905d44040007035450400b031412103140c1a041100400428024407000070a144111070200e4000c1c24040f10f19602c1c41c0c0c2c1094007032a069008a01c448200c420002050ba25900a840711407007042d0340036550035525940422550889580c00303003c00b48440000100d9050f40d241a0f00c1911071040364000c2d2010703995209080b14111001c50310b42c0d00c401d0a080b8241e01405804407103c0300099481d4a018002e0004000401c14143c10f40078414141418060383d100f400716400b01c0440b4060500c25080c0707490030b00010070703085510801030f000300000803560030740c810216031394807245030754907100f6448503100c504412001400460601404000026884461170080207414042c2e40300d0586a103003c1e0747c8241960091a869042d4034136040410900181e075000001d16900a45015500c65025180c81f40c030301a007090001d458034006041c0384d032840da803111001400507083d9083c0c0d808a540502401600c0c00107a4514502010034000102 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 533887949 1250 533886699 533886737
    0x415120606150e0111010f0c0c0614070905040e0f0303090c0a12030807050309010e161409010b03070e060c03070c2105211c06091409030d09020604090513020a08010c 73
    0x40c0741c807000c8000036407c1440f5000c8002c07a60001501000318071080000010f0202901c15a40703058061140c0c81683e16001500414890060080a00c00d50f40d0f940140c0700818100302c1c1c103200c107820030704a965a00703204111540c0c5080d00b241ca50311130758000401003401d080c0c0f18040c3c0071950b45900c1c3d250141e110070400351002d400041c2500704540d81d4a22648070704108100711002003030091004011075003440c0940e000c0b10a040941401000000300400540444c0000c80398010082d260110090100f03000050b030911883d10710250910022800006000d502000c4204036940b107480c1d140c40c0c0c413000100805007034501002410b02d401100d08850b5100980070145004845444000e181c10342030300b85003140c0200380028500c41070352950305020400c42403080d2582000c140c4400b003028030b041e120780740d42c911802c400510380d6070301c440c0070008544070f042c107890250001d04030610413454040c0d0f035241d01d81040d040a81c407650802000150000781840341c0701e542c089950b646000d070b01c400c1c1e01e805 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 533889199 1250 533887949 533887967
    0x80c040c140f0a080603061905130c1818050613020111100f060b0c03032a0703050d050c0909130c0f14040c08010f140415120606150e01 60
    0x4000e0041ca90091000344400c0300040885075500300314941c484183e9680100840030040c00240240d21400c240400080400368041110b440544d0116482d0b80700521290400040705009004200610020510001d0b0a401400501c41680c003080564480100381100b070991b548050003d4000d13402060203055a81d5100001c1030041c10583c10700300c40312111900e0b11119942c0000c04031303600c4282c4c1c41d001d14103009450045c9000001c560801c48040c0034903442c2c9c030025000a04980d1180404504091000702440d482c8495080003611800b4500300070b89142d0010134401000c1c1e18043c0010700d91185101900d0030070001400c42c80e07150b9111403114003c40b100c01002d80b80500c20170000600b8824070580030f00900202d485000e1264406801e0000f1345a01003040b405100101d001401841080c8034454100d81c00c0c0c01102107207800e040080360090144665000700041400c00c0828450005002d84640520a140421034903540c0d02000010f8011503003000c001079a4054540c080e58412000c01c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 533890449 1250 533889199 533889221
    0x32a0d0201092a0b070807170a050d181202060103110405130f050a0203060106171308030c030709030204020f041d06030318040b0904032f032b090c05031204080c04 72
    0x51183c1580398002c05030980c0140908a078840c600003608010014408014008111b0840d0018103042c001103002e03116020f004449062581c0c0c40800c550756003180c01603e234425402036184510f200c81217038020b4491209000a803030101d08594625040d05040c03084501c02c0d03a000308841200c01d42503030341120b0034400140644082c032075007130340d02c026036011f2242038000c000302d448000c03c41c0c0c1440c06208030041c0090600780f900000b480a070011607000d0003265030141460048964960b2040020784550380d440d003011750881e10201c1c0c91420f1503020f00c000d00941c0c203d01611991517001c6000c03140010011103846406410500c60207094041c612545d03150360784010700115044051b40702198008500f101c00780c1c00036034080040050550480c0f0138500d0340320308032900e50100b201103c015030b480c03050381c01065102c5010000151000c22b6003010300c011284440082c80185024205200016514000c1510a000b81f07082080400d1a0104036003c40340090080c14507d503d100800c40101000c0c110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 533891699 1250 533890449 533890523
    0x8040503092d0102011103010e04080f0f04090614010f0f1101020c01020315030f07060516140607030b0316050904020a030510090308060103091112032a0d020109 71
    0x107001a0344404092255100c1d281440d82c0340c1c0c45039411000c5800840203014190b91415460191a41100c41180d040d948054000c00807511549030100307a03485407941040c1071050102d002400200690000c00446000e0070040c00f08030b4545004403000c01603541c256000c103888010070541d00d8000c25130190f255229003002c590707001c1c1e8030b4119826684005174075020303a5800401c0054580e42201480c818603000e13001270400501c0380c15103030798440b190b01400d001c0c0000030506803036071100c0040300001207901c0100c0c1c9a001d80303c03101c2141d442c40252800e0707003c079050140b00031260400241000c0000788030012401d21520b840d0034050b801c0406041aa0089003602d40403000c11010003a401001c89903040000d5106000c2c2030040040c60702500e40c43c1014208a581381c00b1441c1980909031444c01222480903064840d07030780e28034500c1800032180000d01c0700c20b90101c804815142c060340010705e01c81a9106100031100403401c03a144540700034050040184040c1d03161881d020a0307124000c2e9810 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 533892949 1250 533891699 533891707
    0x3060c0a020a06151e1d041a09160303020a1a070e0d0c0b031f08031201060315210501050c030106051b0309030a060209040f0b09070c050106031401020a08070e1008040503 75
    0x100e2290424a4814000010b2441c0c05d07040101d00007a1021407000c030745c0340000309200c1c1083d565110b04002d5000740340382c0070000d0380080f030003800d010f00c51403804800780f0078412400c45d680e141c0070751201300ca8201038401c03149401c50003c0b0603075100c48180c8602c450ba902c01a06105120070404012409070b0141c50700e0400f031101180c4103410000648c01608805912290080001954645820300e0b82041045400c00e100705040a0301c820b940c541544e100e401d0100c1c07142400b4007000d00030201648002414140c1500058a50071000018128180198000d1016903201c59406056220a02c2040c000420030070804003040058144d41a0580c50b002c2500e241064250000741342c524404800d444103540001d440d8240c0c9030500c41c40c0c199002000c014403019640c6000544610030040030035080c000020b4100040043c290f010390051a482803504010010702d01c0c260b4000d4110049482c0840d11040100360600e0150385c80e0b11110710010070b40284940001803c61303102070b020b0300c21200707440140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 533894199 1250 533892949 533892959
    0xc02070503062511030a050715050a051506070b01062708031b0d08040602030a060e0906061914010302070c09020a2c090f180a1103060c0a020a0615 65
    0x10058038007801000036142ca858540505082520560a1031032042c420f100d213001e00888008401d4403000302c1c0303500740b00e070700c8000c1810540e4010030341480710101c1c42d1402c410480700840c0d0381d0045000320b207452041e4800c0380c426018040d842c414140c029242440c80001080301511820300c1d400072089805200c0d904004003407082e41e40c8840c43c0c0241e15960404140030281201c646035100c0940000720040030b0007480c8000140c642d20019101402c00780e00080001d000c0e0300a908418010106002519102c1c9840300c689915a481911080d201c0c07608a13111050803214402040152198100216543c6a8203070055000354091f65046401048110000840a00501c0580058062a242c03a00e0100e0f0b00740350818000c0011201d12000d00e00d103c0c9840d1191510000c0642c0004080303c6580d8a44590bc00300f4940c4c410481c080c200e074411441e100c000c02c4940d4101c045e2400d000d0b401c0710200e03141c00c038100c0d446000301c1140800680c01200c1d403502240c442d42001c0f00032a14080c01c040e045890b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 533895449 1250 533894199 533894203
    0x6140106030e060705040b031303180e101202131a090c030a0c051305010c0212010204060903050c0a0e0c0703031b0201020a08060316030f03021906051503060405030405040c02070503 80
    0x3688400003003692404214038071202440503d51000143c07404078600381c20301840c1031150101400e952034900309040f104003014010040b00810000c02c03264a04244d948a581064244007100c1002400d105501c0c0054200c01c00d00c005510182d000340410444c03220215102c00400310500340110111484031600e52540b114003d140c01340384d9820b1002e03524581205003100755900040c2c5001013140800c0106444a404211103080ea8003d20b0201204a21800040c50817214a0492800383d440000d000550701d8009402c3e004580c0b0400c161101c50003c84108911018a48a100e0190a00744002055140040d0050025910a00700001d150480300303440400808031400c001c015039800603410807030b40d070010a0b007540a24101c0042001c0800210300c09100c442a00c40109150b00405512041600901c064400800003242101400c4e205040a02c05000140c0e600c00007500030180b019107038180800c142c2c0c40786801000031440d1500d0b000c1448001c10500c0324040840c0210040402d2590b41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 533896699 1250 533895449 533895451
    0x2709060903031401050108060f0a0e0a06030210020c03030307201b1309050d050c030f0c0c0103050105010e28080f0a050c06160b060a18060f0504020909060d0614 71
    0x185200295250551501400700c400200e4804840095800100216a0301c01c0e24070740c0c48003040d10084020441500800c0092016030400d0711144464400c104516444c1e61040044030300850742040c00084490041e40c841031151450b5401d41c02c1040001c0d445030040401080c01d41034040c40c01400600150200d092400186440c0c14500c810622407849103800b8051303541c0038864807002c0041112a58501d55580d090440e45801d10401140c0781800c1d0340d00740160b82d038049007a921240d0350008038000030b885038840d00321305011a103818004125544034014603070803040082c1240040314070390541c0451860383ca40e01501a19000c02d0040b03202d03141800b100408100c1e090081c8401c1c2e6140c6041410700a0445501d40142018070041c04400000f01c50400c61580101d0607210580311400800c8004070703613400455100a00f49004220320701c0e00da0040048a502c0b2100003005134a410030002a48507038280668402d4131200032600d10701d0020419148148260720001d00b500507000200d00c0000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 533897949 1250 533896699 533896703
    0x50d0510050d150608030f03060f0a0f061e0504060804060b042301050a0501050a12050a09080304030f020606010e011706030109020a2403050402100e150f040501090b070302072709 79
    0x21202c3c1d407280c01206008100180c001200998200390200c62440c0c040d00001700994420030012140c203040742c54a8140d000035040703c141034140a40c80d042c1c040e0001005903051501501d244444030301e51440744099a003940c906950344c44582d103954440c1d0b8041d0542a51042d400360b500c1a404009840e003010746c065900b8a603403001c0d0198544010449440e40c0b9521040c1400000c1104122482d0b00540911004001c00c50001b203039112009800c00030700100100800b004030010501c01810380158024140320074550031100a6a034000c01161004c40d003400c00c0d40811083d15400101542c25034626920140107400014040c0041d000a0b403400002c0d4807050f0602510309543c0000310b040150812141a42e04090202d81003d501086501031043c0708082044884441d0804e20743c0e1341c3c02e611000c2da0080c0165a21500450704010140d8810b108003408902014030000c0c400c500041540c000b030741c041e000340c0800c2d0700d06148104044800040c1001d50202c130101c1c515540c2c9148101207103d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 533899199 1250 533897949 533897963
    0xf13061b0201060501090e060904031202043507050a0b1b0714090a180b0c0715050a060609030f081b0709061409270f0634050d0510050d 60
    0x19240c10005048441ca135081440182c202404020310340d107603c00c0141d0481d51500d4000c120300d4503042400300a0141c2d4201c0c195923f950b0b03d017010206200f01d844041944c000d0064030307007044010302c26030362200f07580309180e00700e81c602904009103114030019200c030544002032101c5801e003468880341000000d81046e03034a200c1c140707004042820101079407a4441004802001060900ca031010301c461038007000284190202c030001407000c42c8640035500701940c0f1102d0300c20707011000b4414601030b11045030002d01c82d80c83e141b000200c892098000ad02140e81200003e2442c004c01c1d140c06542c0c2d0312041c1d409096101040700c883c1464003c0221a009042504002130624241850b8503401e104817201203104840020500414a0b0786e407c800b05004040c43c0c415503040e409419040c2005000c040c410a503003d200b040001c418841e480b141800364090440341c0d409400403084426078104606980c00103030702804200107e218a40c07010780c100c100d041c141d0a944c3e07980c20028006035090700c0111084 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 533900449 1250 533899199 533899211
    0x60f0803030a05090d09151b0311060703061a0304031403011217192a1103010608010c0c0609020a05040504120e04060605070305070804033203030f13061b0201 70
    0x10011486070704e030400d1051029180c1245508802020204140603501c0c03002e048641c2c16110b035000d036001000e1003541c60b142001c581490305000e000c03203001c4a205000c42c000c00d0005132070b6910a100d1041a11102c100030401d033107000401c013100c0e4000400032001d008038060070038440c0445501840c0281802c00701c80030300ea100740c50040da5400810f406a080183d082c0000034000050022590400b2000c1ca0801c0b038028203070200181c0e005520602145990084401c4424040b900b62030b91901e035000d4000703004055580e400300742220508544a800200400031a00c0003c059801175043e090000748109001516000020708852040d1b508035180d00740a45103c3d03440c2d420011418525400f1102040030501c0e040b000380103445aa42e0081c20004009a910104000581580c000c0c542001000803a41c5c04a1450203111040040c007055000d691002c0548022000048074411410a4010403407078481001201041600c060119845615010100019074003c640f40c1d05244030395002080c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 533901699 1250 533900449 533900461
    0x80d0e040e0a0b1e0105061605011e020d05010b0412020913051203090606030604020a09021303060e0d02060a0e07170f0d030b010e0405040816051606030506040b040c120c0201060f080303 82
    0x5080c0a0060348140060f0750300040046c2d03076501c0705a9191a46004403055000d000c1d14100d40140040038800c00c2d0000720040350b80010380c40764041e08040d400100104401e90722148448d50500070741c41b40036001a0103180c40401418a404540d80104242c903a21817a41c2c41d580c2e40700c0c1001c8803031072481a0203c0100800408400811085400081c1940502a9800c00c1d8004c10741c9007806005000840b500003480b41820903010b540c2070001c50700414100070a4212032070454896110704000b400520400000c02d5061702c041c4981140740a824000305480340c60b100803075510840d211980e41490240b901e00780c04000052003d94548145035030000b4070010040005481c01100b02200c0d400742c2c0c0741008100025000c0000c0b5002c101e000000f14035080441e203040303403602c0418000304455510312000003e482c0d805800881c000c0b0011580ad20142e0b80c0081444110352565150500049201440d00404c100310752003007880280510001c1070b01074581812400089a41e400000154400070410503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 533902949 1250 533901699 533901721
    0x30106030f06120506060f0d14010615090b120a090b040501143d051908010b040e0a031206080304060c060f181b17061609080d0e040e0a0b 61
    0x5000740c16051001d030f0140d07440720340d62880b0043c072070ba015252034006000a40c0d540180c40d0102c55110682a28030b102614881d406005603104031549a141252170312701140c010509102982c0700d400880d03050400b80307004141402c002420859250390703500d10000100b5489451140310300d0041c0000705d04146000540203480710020420b62554003240f01d00c540c001000d41910062042107046250301403500040c59507030a0032035200d15800200b1001a40902048030103610803140c440c0c0007005032808541c20700041d100d16440c0c0038041c0d0010911000002e0145020b180c40004100e80040c0d802d03121111140765074855007103c80891000345104c020417035140103803000020b0500c41400382c0a40066251030242010b0402008500301c5200b0082c03603990038603000c1c0141418482481c42c2c03004140d800791100700c2640c051030015988a000d454890082d0091812241001d006084051000c00101d0309080c00c1d0481d0341c4d11548444181412070000c007e203411660162410260764141100e03286 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 533904199 1250 533902949 533902961
    0xb1e0117041a0903130b04050a1a2206020d020c010512070c06111806090625060203040b1905010b030c160c151d030309100216080d17060a12050f03030106030f 70
    0x15081c000c000510442d25040a0702c803c980c0c80c4652b07448003854140c030200035030085030f00074602c812201c030400404c02011000c400c1124200d800341d900b845881103049845a02144206010038801c003c0d1030000c4035800581544000145803411200407203a0364401501c0e101007034404a214017251580c0d07071030784843c000070030304004803201440c186004000c20200e02800d210b03503191600da14901405042d9040d084000142d100c0c400b15500d1500741342164540e02d090350201c5081801801010081e1658458035058621026a140c1169600840500345034040e0b185080c0c11581100d4010002e001006513401821f00d109583c947ca44402d08024001a0341001c0d0394041e24100c101071009840200c01c40711002001d950010290920300c800b03034030b02240f03881e5a000d909651100000c0c440780100d802d00392241581c1d0344081d50b401c2c0300d0146c91510410303103450340e10002d4603500300803048111101410f040d10a4054550034405285600e095810903400312000c281c9405009500000b1482a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 533905449 1250 533904199 533904209
    0xa0606020c0d050706030203061c080a080604020313060510030f060f29060702010c0b0f04050105070c0201021513150204141509012106090b1e0117041a090313 70
    0x401d0282d125407a03030341d03444829201e0740b0217040d80080862400d8541c490440e0720500b4106003030a0308186031500c03d050f135004000d40300004541002003401072515008032030042080b095070301d49038030303c1d9240c900060601410780c20351104071040000010718402c16000207240a100300086109107004900141e400741801e1810030700e81c1c000103a4a04a85609012171008252103154541c0c415100507110100c0190020700445800020400e1003805c11090621544c824002480680c4884009581175200154024003580102100da8400c41c00b14820703a42c460302d8140304076400d602645814111500c4a041c141900f078002505100b0702480c41913141e0800010707140407080511000000300c460140e0031100d41041282040c0a00d00a4680300340419a01140c0382001191350712260000180304021405002e00d5440c1e03901d00f80229103e114550f40306060315601c0c0502414001510706031070003082100c1c02504407050102400464000700c2c402c56040340216980c041420601021008503809 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 533906699 1250 533905449 533905459
    0x1014070f0503190b13020703030b0a1d130233040f05040b03010b09070c0303110a09060c03020a0c0f060818030f090a030b0709050a080f0c0d14060a0606020c 69
    0x80920641d0744541242d500540ca04141c030610705148200201414070420320f1680300d1041c0080d5401038040368001c1c510140b19440410610710002c0034032000c0b200500c207294105040c0106524604102060706a00a2162a21100c0c0b1402540001c0010a80001c1810744900484e40ea134030005c0c004042810040030b5800460030546810002101c42185015507402541c0701c01038540e683d00c094011407440302e0010000d0406107418a0020501c24001d04103500080c1408045403011070403008540e1180010b90700c002c01d039420804140c0d07441c0d02c01402102140f007100002d8010030484a2008060030841490024107454204024501e0384040d010502c089000043c640d9000400001c13a00d0b00103003c80d0158899940d400050800e040d81c0c0c1c0b01a010440c50b2080201c0c15611122217400d44e08121041d40444d521202007039500c2955881d4044150f1010317181c0a15441c00b50821500288106d0400e504030310b0780003070300c1e04001094850702e000c59150b54041c4400d0341c040c4044001d0b04001c2d52 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 533907949 1250 533906699 533906717
    0xf042703021b03061522050907140603040615030506040b0f0906070c0209190612120801120b1503030c010c23030a02071b03050304050a0603092a08101407 68
    0x2c0000c0d1603500c003034008041441800ca0032081e94980203180e10158203540810010f00300241d9640c0d000d000c0072240c1200b2030207540400f0695402c82607151816050180c405400c41e43da48d503400000b801c4481d0015008545807000000154003001141d01c21803150380010880c0c148035a800e074000700c0103400c0b02c0107900300700f040000e401c0d1f01c8403070b80d1110780e0115040f420680b640f1030f501c08880c40303018198a0141c00c10f0b10200d204a4102c1c4801d003e00e1041c044007071449100c81d0100da052a003801001c0c600340f40340307a030031010440c541400764014501da52140810000359002074a9030b0320a4040f200242d44460b480e0380034036045002112047c41950440c60680451500e612540c4401866880c1c8550b02241c07000501c9140c0d44100e824040420401c3c000b03940742e042c030035a05c2c2c01a00c9a613206520030b54010400750300c0380c00f0749030480390b019000692204001d80401c5070b003a03c2210400b5214070a69000072107080801c12207024008081c00001d103034490410780030074a0700c000c0140042c00a000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 533909199 1250 533907949 533908003
    0x510031e11060a02010b0f0d0c0b0d11072003010209150711030708030c25090c181214030c060403320a02100c09050f04270302 56
    0x1880c0c000a440940151114140c440c60038140181e44030180701e07081040498201c030000d4055003c8144800201e69100d09407243c0c03410454481481100107080c0c44100f2800c100d032560b90400352103440d0504a01086203c524940d900b81c54001d003100355010f40700802403003541000b0625104803090b080d0020b61030082458049040f507440c404019801c010300040b007109100030502c101198030801016150030719034440c1d01c070741e81b034020b270144285030b0003002514541c18402d0095480c40125041c4400c0382c107403401d00b5400003064580301c0c100510050125141c00550550f03e650301804103120700f204c0e01103450074120700d5000c54080b000c515a00c2000703c040d00c0ca100045066001e50b051820641140d90001c012020032406050000d4444a4051101040c018100030b8a40c00c0d80640c01c0350309900030043c20703c0568600c05142008551808014003560410b00048c40c00d0000162002c100100c09004296818000410010042900c43c3c40c040030150f05000c090100f2040c0c7c0c00e64114942c0704 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 533910449 1250 533909199 533909213
    0x110309010e04060b2d04030f0314070b01060f12140a050c1606020307171003080d020f070606030c060206010609090903091509030201030b0d03050f0a051e090103051003 74
    0x926414000418101421565140c0100c0c014000c0d101d54180c4810b41d405a202c69840603900006001c9144803110728142409400d440440b50041d600b85c002d59445d0714242e40c4288401c0e56281000400c00c44040401c200c0703410b640c000d01869491401e20244d058000780603d801c4107017a81428101020f1900ca42904864141c03c03201082000800c4c0d01e0300300914515201c0d0403442c0e88411028020070b42440100c0d400780d4400c0c00280ca416030740d1140030800800c082e13402c8410f10f69403110007070144046640078010300b5034440c1001c001881d200304812065019044074404542c0261148814800c100c0511000790050406000619295051010181150010380183c00700aa42c49084030b05040c421110030005240100021a0211080c03000828920740383c0000d9010a040050381442414840003d0b4185c41e05035458504009000c103040c040d59210810310010801c0900483d5100e0040e90344110340c41c0c0100d05403e036207000340b0002406441004003003402d00d50484504201080792 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 533911699 1250 533910449 533910457
    0x30a11060904090c0801020a12050402061c0e0f07080d090b0301150e0607061b080606091c1410150308191202030c070c0504051e0717040803070f1103 66
    0x444003507880760181004640140404070f405013014a81c0403001070b010506500078107001c00705a030341e2103103980040000d5095541c241d800a41000c0704001085002c032a00c210011503000c000c4001c1108502c69200703910304901ca254071002500b04c1c4504015103a03007000181503001c500d0070510314040c81c02603580550301051144da0600384d0300080c052a0184910f0f000d60300400001d0a094682c0c030750b07090900003015018003104040d00001d1001c45803e00070003005204180051580340b4140d0000144154800c0079607100c01c104125480e0743c0009003508060b42c042540c03250082c0540e400d14036880e070079192540041880086040000e2002c11802801c0764400010912012042c480601045035100034040c07046100c1c920210512464110003401810a203010320b0b00c07159040e44820420040311010b60310007150000745a4a5480c0500031030075280d111125081070f4101b0060521200c401800803541241c0b0204e0010400c21000d03007002400d510400d4916104581d0303003c402e42c05907248a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 533912949 1250 533911699 533911733
    0x12112a040b1c03050d14040302100605060406050702130603060207051c09030210051c0b030c09130209040309170d0906180902180409142e0504081204031805030a 71
    0x12049201c1010305002d0001c86885c140840001c01404081240c07021144005075402c40060207240041c0c0403801c902e00600080c0c070002440c007460a0301c0d0900c242c40c141d12400049030070080010884818180d54130440c4001d5004002c0544d403407002e45000340c00c00d00280f426921507a18654504040e66000b2896002c0d41c1d8140c1c0c1021900f0000607081d035841c0503115000c412030341d48803501c4890340d5040c0c0000c01100005e03822500d10750900700030400700300c501f1103c02c0030000005060b0400351034200d030940d40250080c00c0c40b654041e2100120459420b051710221656444082c0a604569111002d080149034a2900042901e0400c204409160035482407500d016004211510900045840007a0503072000b00308100d10541840e1010420300c5a596004550240310300c0c8281022420b0a0301140d100f10280500c51055440b09540041070040c0c015101864140803507209404100f0f03100340124020b0300c58810340c960010545910702c8440e00014020341060000b040052006d07040600010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 533914199 1250 533912949 533912989
    0x11032203050406052a1f0c0e130e15040b0601050301140409050c1201050108070501030e03070f170c0c09070302090d020f030a0c0f08010609140412112a040b 69
    0x340e500052081480c50700e0030b900340e0250000c00c2088002c2e41c0050100c400e4007003503801806d609141e9000341d0403180d07043d003900c0204288050418803850302d82e5100050356484803000502e481c251158030b15018480159069610540f410b00040c043c00b450704960003078091074854915170400c1401d03821007441303910040c001ea40301e01c1c00340100070080c84801d50507100603000840d50f41c0c52a00c0d01c4e000e007001380b1414403180269000407903d03511a001c0c401205065000452074450603603914503d0060110040c0d500c0398a0810703c1501e0442c5a006103003814010b0300406010b980c80f03040040201014100b0b42c1031520400601c003c54550000038940035404980b40f151000303050011030700b8941d81e0750000301242e4510345c0c0450038500c3d20031b080044d501101e00800c031054942c01c100d003c0700c12030050a03020f0800712000800042e1680d1408c451540c0900d003420420000a0300546071184800e00b501c41c0c69094801258980241032040c0d49106040302c041c0200540d1201280040302104d51141c580 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 533915449 1250 533914199 533914207
    0x11e120f0f02040e01090c0f0302060406080c0c060a0b0f010306030b0a1109030a0305041a0909010902030c071202060601020120031812030405280c0b03100503011103220305040605 79
    0x800001007081681580190050081c030500301354960003400b400000320f4130404829404964141604408030640c3c1c0d014100d1032400b4209442528251001481548a21010040441c0710307441444498090f11118101040f050003e804000035800c1d080c0c00e590406d4a0110100302294040c0003054201d4034010000462aa02180ca44d819203e507581245d00b62140c00102d204050b8454010300072600e5440060880043c143c481c0082031013014049540000340070010701078400d06500030340d04008940c00f020726220703041e694021403007c500054000340c1c00580c10007000c0c3d60203014074001211200b9450501a203580541080c3c2d01000d0852480a116116081141c070400c219076046000d008062544a160924060341d075002c000b00701140c502c4500c0c2690240d03903000500c0c00d030065449840f14090b1810b14207000c0075600002e1103c0c444800c07440d0001400e03202885414000d545d1000702996a15001c1c0e00d00c02205110100203c12042400010011035400030503a01511628586a60381d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 533916699 1250 533915449 533915453
    0x2010327060c021515040608030a0e060901031b2a020315040602040b03010e04060c0c050a0303050712150f121a101502030a08060406140906180f011e120f 68
    0x380c01001002c0313241c509000f1052020b2034140510409214074204e60610102c0d0319040140d450780a16108040440c401c55451403a070702d007072000b4054199040c900081c12201c0c04c01203000d0344851042400120b201c140c03c002160520007900c2c0031030004d2002c0001e060b20700c0d42c0442d03540e000c500b070b006a0007208140440c08001158041341c00401030a0380713540c0c49584032000c0000340d91b0142c0f03040f07500d20301d080c09100e582070194440612454000025107102c07102d50301c054002d8103001f403103d400c00002c0480c003c42208244500800d1b94001140b03c1106401c0480303080756201c00d40c000c08800408028070f0000a024100328000a00d1228608003050301c03102d103410800c04240c0c0000002c0c4028144081041c2d500201401c840209a540c620480d00ca14040c48120b5425000341d00b003089200400300365504240300d503140c000c0800b40c016003089026046864040c5000d95400ea4460001c50042102104114103507800c02d001c45003860015140400c200d000c0402c820000300b503016008003000c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 533917949 1250 533916699 533916703
    0xb0a0209042903150a0906060924051c03110703051f150e0a09140d02060412210f02090409051f090f020d08040909080702010327060c02 60
    0x9680094014040c1d14690080007905001c050890880c032550b080306240640360010302c0c0501c400507a072485070703103407540010300004e448058010740d03080c0d440c2d4000080f400c12920902e03135200070201242071000b010f0f02004034001410342c88948030701c41010000d40300709281002ca040003a8541000b1080300540e00d840c5007401001c1c0c2c0080c03d103001724407011000c10140c181c00710614076110803c01240555180400d84042240a0113060203140c00008078a00c615a00035000c1a001ea07490b0440c1441c80b058803403134120201e5826005030001c10503c01081131440c02e241e0280c8007400c0901f102500040c982c40e031020802d82c0c141c880f5403540380c00070f118005a4110785081030042d100340554001c0c1d05180d030f503482034401c089020201c0080c40300d20441c144d06c6031601e100c1e4404c0e8110700c101c1003070b02041506040c0070380550b1800300400000884405903c00c1200c05445000d00545400e580d000140455036000002003200c80314000041c0e02140e221023101ca071540c02400015070031b056440480c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 533919199 1250 533917949 533917957
    0xc1d0f06010305041e060501090506030109051213030804080f06071412070c0605070e0108090a050a1b150201050103110901060206180106080d0809011104080a0305090f060a030b1f09030b0a02 84
    0x6031001d04085d004400b40403464121906840403940d0610058581c04241805c940490f134002d031180d044120034040c007486e12001068218001200071100075126100e64881da03005611180b80ea9022140806081d02d082c01400da0001d801c0c140091140751080d031200300b600c1598000d00059882000248415018490410009401c990100074514007500c0c050960348e2400f100c1ca0102d64003600054080200046c0b01045a9106010b400390f115980d80300c00b44020001404034070400f403403001140900c064514003604c4141580045850352650800e25640c0d14200304450003441f4080040c0f19241e0005140c0e034000b490400f50910750f40b5134501c41c6004014a0700f02202c0e500a4000e803441d600d0340107020328010002c1178001c2090b0b5002d40e40e80203842c81544100c4031035030407022800300424060310240c00c0121014040d4817008209000149140e400f03c0c1f03140c404666903c0a00303005080210400ca5140989541c5034221220014060220b07052444004e04d03502070350000a00181040e0152 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 533920449 1250 533919199 533919233
    0x90203010612080d050f060d0b0a1b0807090b070b04150906051302090112170a02100603030824010e0d02060706180212061303050f160c1d0f0601030504 67
    0x800382c000350034a4000559070120080610190800001c200c908102a413500d009960041c03c2c09013815160341c880d070280000a15006a29658180080c3c3e0318a00e52851040300c3c800d55500030382d6140c031100213000f151145d040b030340000c2c006000b00400202040389140d00103401c80d200032800000a14200c000d804044001069103040006014203419010220780f951803080390b1481c400e03078031210f45400490f2040c13000f420400700340b40b00b2690042210010900340340c3c0e510540e42c4082001007042c00f619895402100080ca0080c00c1002c03520b44945410304031104c10940001d8170345540d0000b03090a420310f140d907120b072540a040380e007103564420803510f840b58814401e0091104c140e03c0320107200c4030414280d00440104007800e814040100da43c2e8420012070740d03008948032003910b04440c150803440400841400c204112101d20b446075000c400003d02c50a404c07802c4604045071a54a50b417940707090302c100c7c940d1501b4840c1c85110062079903849003082c07030005541d5445003003414032a8584560 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 533921699 1250 533920449 533920469
    0xb0a0e060706182105091c030903060e06101508010603050c0412080307031d190609050f0d09050a0f050402130b211e070f0509150d050105060306130902030106 70
    0x8030300b0400c81000c0c15900402a100c001e000c4113013043d094640b48104440d441c1d005000404800341c5503881d410601005010340391180803a038807540e0324421901c0d0800d100603640d100c042000045004da00c0c200c00604035000c002c901203c05032001814000042c000c2c1000e05840d9400150309a07841020340c0d00406c0040000c2c2034000040c2081801544140d40040000f0b0a0580003000780f440c000142400907007202c000c00d280d1101701800320381038007524000c5a401b030322000c2a5000c204c08100000d0b0141d080005001024984540609980c00e2079024600070b980b20102040a0710140c0d90084c1203a40c02d880c007603a030344891050705803a4107580d0030410840ea00802d0324443c070070140010021041600c01e0040403510b4070343c02600f4005d81da894114211044c02d0000f801d05105408900103a1b4050a08500707201c1ca080005081090308000c50100c840041500c1f1500220783c082c2030b00410080d203240e45541025070201c2c01403c00740c8400300d5581e071540003220440d2025481040248801c4003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 533922949 1250 533921699 533921741
    0x1a0d0b090319031506050f0d022a060612010c12020304020d020a03050a0c0803040f050f211f0606051b030c070603052a220806010305010e06010b0a0e060706 69
    0x150150052070b103190520b13410b40301400045003880c0100101d030f42480b50020034071305007030783c11b001080030354812103d00040c0c4d850080000050003040c6485c1000d420800d029002e50b14215052002d00303021620b18140c143e04042c1428882900700b18143c0322003120349000750f560303551400071030241c0084540003504040344c50000414010702042d411b907d5807140351030b003181565400041c1c2e036a010718000c410103c0840302040006103007202840b9050070000c2c1400003c1c00c10000d20011402500e0001650764004d00010030244c1c0142c8031818240440c40c2041041c14101000100386006151404428801038660113004d0310041050700c000b400605c0841b805951030751002006454151201d0b805c2090f01d4000c410740686d240c070b59040c0d60070950a11802c104c0c83e05c2c62036001058080c44056042c00889001c184084148a0343c0d010354064400810031100704003d480c98008164044a01550248a0001d0150340411800b100d141c080300d6490700c41980d818010700511800050800034440c0709 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 533924199 1250 533922949 533922997
    0x90b07031a09042103020705060a0902010e0a080d0e030708061b0403050708100f020901080c030a0b0a15020d0c080913180507030c05060a0e0d0512030703050105041a0d0b0903 77
    0x8003044501307901c680c4000341c00b03a40a1000b5400e900840600403ca0740000c00050868402ca80c454000b10b8014545a00102083d00c08141c44084941000c144c5801c4020b0805425401485101c1e61000c198010702041d468000801d0b01c590002e01540310414030007030300c01d419400e9101501c0156804c84240d504455031500c003e9a80c0d03610001940d40e40303040660414030030926200b1f40e0120f001c180c451508554a101c1d2003862680001c21703c003685640c030f0695a0b801d40711045000090400183c1224400c0d00c000c402a18006c8003100c00303020008007901c08000640c0034010740348144010358021007680e07614032200010300001c00c040516800c10320703034000a0241c0040c010703086030b00a405030740b03140307032200305002c068460140544081258107080c403285081c9901d010307585030b001d6420303600c3c80e0b8541c51103118a5401922008006912a0014011854184950760301443c1b80c4694032220000321001c5400300900c6000500220f1101000032103280c011f1040b0b4071f18440c14034140460f0030301b00c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 533925449 1250 533924199 533924213
    0x4050f240318070f03030206070809070b1215060304080403120912030e0a061e18050301020f03010306062403150513060f0b04080304033f0e010201090b07031a0904 72
    0x107808018450f1107600000101d00d05880f003008103498040d80030b486650b4802d1015509401c0140896200c3d00c1085000901646103070003030880c02c412200c1d03080050900440d420040c08002229510480003001030000090a0034215800c6940c000c42240300c0c4100c610007590500103503480841c000580d041400101076009840d00d030840c0c030445401c1da003151070b4102280e50303a010059102034103000c0140180514013908040b45404e000580c0b00044540700d002017420790700054100212503001000600411004d4040c01c005440c2c8100c00340c050985811100f010107000a0041c01819a0f8840100c1c034400c006801034064440503000e000d6200c48992690020400c03449010490030010001242d080f64003000ca5040b61507090045042c0707425a251451039405d403c01800031412a04503c1780c12003103816081000c11405500f1801c2c0380b42c0404d0240c50602c04881142c11a490b1880040009042001c482d4220085290009101c000900748003082014150440c1c2d00c140103004100c100014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 533926699 1250 533925449 533925481
    0xb030312071407020910170a0320030d0608071508100308090d02041d0c040e0304050424090603060b010507020108040b09030403061b0e091003031202160c05031204050f2403 76
    0x20400c4070f0005042c0d514840d114441c08d0030080004800304200b002d01e20a0a141c46102101402524506258080d2100484440e036204510780e8000a108210071040b200020402e9600c50420060300c1c90000c7c41400b10300b03e9404010800c201c0822a56510b440b11046081d0030340c0e015204016104807042d00441814046400c10450f1007040c0c440798603810300d40140030011000c20015400c0509090410002d007950120142920340035904020707000070010742520040550300000590b040c114203001007503405c004c8415050200c20072800300140d9010401c194043c0e00080c00d0503060303e801020608500c0303294400340c030143c103040e241d44656100c13002204c2100c000d47c0300e09418141c14000d200f9610000c0301d5141260b86141d00810201e40503100700601a0b103128401881c20703440c040f016801e03000d4030b4004e40310024038550500540c1010040108a8084050310606062525000560160240000500440c0c10381e2610b51551244508c0091120420700f00d507442e440c01c90504880510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 533927949 1250 533926699 533926709
    0xe010504060f020421020607050a0b160305010b0910050c030d06080c150a0e04140a1a0910050103090503090a030813090b100f0207081f0b030312071407020910 70
    0x4900b0441001c07485083c801c58003103900f4010155500c20902000c11041e0701ca0040503a00142c0800002e0f0001e8001d200c01014141f02c0d45400e081070130300055040b60401c029044a00740351070500140300d081d0030a07050f10311050044858a14982c0303400d03170880c1c0d640100c44d034030741482c40082244040500c2c3d50300420140c6840400b100c98240568040143c05454041c403c0644001041310b003000030300c03c1e03414a00c02903025102050440000390481440c0f0b40c01c49561865503500d00b0045a209150491569803c0e41100c80d51402d04201c070a51411000c20303c54035042c0f59951a00c2000c210090080d103054840090000049603640d040c150752030303400401e20b2400041c81040102c1c009056104949104802030a2040c82000c200c00075100c414030601c00300c00b035100d0303540002043c2c5002c005034950b81c21080c810f00c403c0007076107500e801595104c0944903c80d401c24800b1030b59510b40050700c5644007445140100082c14070ac403441c0441d20a4070340103504201c0803401c11a07450101640703181260 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 533929199 1250 533927949 533927951
    0xf060703020f010e0c0f091e1003020d0b0f130b190615030c1701060504031e020d0516140310110c1207170c060708061503130c06020a0507090207060e010e01050406 72
    0x6480201001664041110700c411804108c0d40c60750784c00341450802d56841101c86001140c09500d80d00024610312500c58110b4810410104001201c84803280240d002b1050034044c22641c1250780d9040d000c01e2004040f00d95150400c003050440da40c0c0f942000300204840c41c40040c00c1424203030010040e1000040e0500410842c0c6822202c8401c4805040c1c100c9440e0b58031141064156500c40c121503003e1030050000c140d1400800001d82d4913600001d1059104600801032421030501a003241c008541c0400c0e150400c100400d1615103021403008008211034400088028580c0600000382c042d24242d03090501c03440c110241c080500000070001d4900500005901c2540c144a11100d44182001d400030343d001500840d10440c094403100c0e8000310024240c291281c0d600180c5260703504103c03030882c51450844e80d800240200303042d141c8064080d03840603060340f8800e0780320700ba80c6018510415915640c000745100600146500813000d03044048020b000a0030002d4081d07002c4c01054030155901 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 533930449 1250 533929199 533929219
    0xf090405130c0f0608130201030e1608060901020406050904050a06030507080d02010506120d0807200303150f0a0e090a02060304050c04060501090609051c080c0a031d0f060703020f010e0c 82
    0x41c07003d0300d42c0c1408035901130751041d19594807011010a48a4080d40032814980c880b07000305080c0a0500400b00c40401668411461a140001d00d40c50320101074079240c00c60741b0400c42800080d80c084101c03891070f4030a4a02050640f9000319160003001e080e88090b080c1e019501c80882c42401c0424580c0440c01c06a00902064481c80d08003c1d2241c049000c0b014150b201d005030500481c0a8203055602c00d4260a00c080c800c210b0300200d09120008040300074041e0000003c00c140300245010b040e040380000c0e0380c0081100300c0240440c3c009d1401340100150242098001204010104004604143d019005c0d03522800d0a207010341d03135a403141e448903100c0e0f0b02b80360002c0303119403041c02c030750f41260004c1d91802c0c244ca1504007884200300300e000504280e0301c501e402c0480402e24800050100b10b8800c1e0092030a82400e042c018140080c11003440c01c0c190f40601001c0196407048100310f00400110381c0956508418541a45444107104000c54207508002013108074000110302016485401d0f5460446 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 533931699 1250 533930449 533930459
    0x3030f070f1e0306050411040e0f060d15060503030a030e1e030d0b1c0c0f0b0f0417010b030703110319080409020306033c010c0c06020f090405130c 65
    0x281c41d041150032400100b81503101c052820701070080c12254000d0b0b0800040050312200403a0036074040030305944500000040402c0510121641c45500080f440c00c40c40c2031307041c11000510200d2442c0b030301901400110034000c00c0106281c0c012401064010105c030740d42d50300c0e114007402425268490340d1582c003a07540344034820762901800ca442650040040c41c602100f03104508010208000203c1d009008225011283c10f0080c2c92402498080d80c590500c880c9040100d501d4100c0030780008011142c01d000080c60700303461405a0b4160303802c0540c4604116a8140c1a0340100040c480c4151b0511a81500109101a00e8401200d00b0429019a61503030303007a9211100c03501c00018001c0c0803250421080010180c542e01031500000c009040c1d90028102d2551600040d0111140e00e40020b481100651406803890000c0100c405c840001e210120f085600505030780305100c40540b84035000580e911401c05010210341144c0001042008a81010031860020340b03034500c42158401040c000101d9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 533932949 1250 533931699 533931707
    0x16031a06010305040b06062d0301030b01150f0f1b120915020604022e050c0c0411030621010903020606041107120c0c031719050f090d020a0e0903030f07 67
    0x1100345e40114a61290b500c0b0003081c40b03041e51000010070b81e00000030401e200e0000d5034480e2070354401c540c3c9a51940307a5066082080103090182c1c001e100703008100d4140c041241d0458000d035602c410b241401c2207140e0368548181e40980781c81c010603c41c1810303541c0396810450320710356030b800300c03482c0e036507500c00d200c2d102c0c8110f55440a1103484000940c3c4500000f90051030100305c6092450701c0051409111100700e210710220000c1240c0c010081640407032002c0b08000c04100c16500200100c409103c0016091107884107480081c0415000340460030000b03103107500c0307000c0c4441001240d0000704680e10305400d0081d1100410b9030024071480c24000b4103039000c2444800e0f1202290806180d8010581c0ca11042c1ca01d00b80c0180116030604400c440080456802a150070310001580b10b140c1d03882c2410302d201c40d00c02c00e200c07901e5001e0080c00e00c01d00703054604603010f0f00d412103410740f51004205d015000040c00201250b10643e80002e0440811044143c00320246000d114071000d407041688a90105907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 533934199 1250 533932949 533932951
    0x3050d0e010614060c01020d050403111209090103060209032d061b04050904060b0414011502010623010c14010c12050402033c030408070801062616031a06010305 71
    0x12503c0907840701e40e00407450700d1401011280c00b440f00040c5849000995407007912000c8400360041460703001c0c40c001ca51401e011402c080c22080d1032180c544a201c00c0000d40804044c000075000590205122241c0d4808208100105610a010318125201800100c0100350100c11800480c0a2103001c514500305040007100d00c203200401440c1020300b00000e00c4060100180b06540403501d4040300710840d2101d21401c0f0100740610300c055000e42c14080c4400e07405842105001c21a072405804120300b6942c1c4d41c18010707000036402221103a50502004030340606052001901e40d80240982c0680540c05600020b0b50024507100c282500c2c0341c9421400c101c80c070847d0065010303044a04109244032401d141c0b00302015078841c400001428181446007043e61150308480b0070781c40081c0c1401106c904100798402007408000a210792414860580704c1d003c0294074001c0301080042d00c0c0c10307032820140001c0140050001b124407400e56079003400848044142c008901c901c0e511030104040307510074007500d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 533935449 1250 533934199 533934209
    0xb09210c0312060d06020412030809030702010c02010e13020d0225050303010e0a020f030a0917071a0c0705251421030906040e0a061d131109010303050d0e0106 70
    0xd0350034908001a0300b00503420003084030341d01c0600035000d0400900c01e4409400a017002d400c0d89a4028140d1038040e0040c8400f52840500350300a020800060f13034051500028294280780813019890b0880101d840f000c12070b80c0c3d80503654008103210781801282d07800384c0901d4400207110f5002081d00c1e040c0c414051545803000e42260010001030280305040070500303030052020b42006181402c03100700055a500240c40c03003111107403600c21480a115030340b581e9908901c204405280342004590701e0b0400214140c0e1040048203560002070304040215094411480d04042034841307480041d04600e0320b207017609080b1603c422021801041851903200c0d94641c0303140c06007a00c0c3d1721440f503408800b55030140c614101c0350303403000b00000f0070261070f0308014000411011300100600d081c18190361040c3c0da40c030b410600e0111402440400142443d116042d040610352403408502856818400c0c0f91001116515401904030b100000415500c0801401c124840714010400312540603061802d0740d03a07030301c21 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 533936699 1250 533935449 533935453
    0x110d05060a0605041512020f1c05090a02040b03030d0c110601150906120f0c050904061a040e1e04240618020d0e25060c0305190c0b09210c 61
    0xd104500c45c000034140c028419007800c0341591100440342d01030381e0100c440d405140901040701607401c0f002010301040351100305030a1040d031600411407541ca03502e118001e40724607220011101d068a003801100e4044400e0602800700c104c1c3c0c110042c0000f100744030f511356544103200000840000c000500e00603a0f41d2507550324445890300c0d50846102181207464111995216a0700705600001d04c18000144a55160320391610b04410400007203810960020800c242c41601c08540e11805100301c030b00342c03241c00046540e0354403002d04d07080064007040d07040b0100c00001800c0c0403c0c8001400000c0c21595510381c40c542203010035900d04260340040c231031200e08404042c080e1820f2800d07030b0003801d4850003101c000a4403051002c062031500080c1e0710101c1d2001e00004e42d0b50520a4222000030180000d4244800291100e50700182240302d2206000400301703401804681d400e12401e8000a40d58000c9042c4619082a8000796150703841115025a8a0b079a9003850b00341008420603254500c0040b00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 533937949 1250 533936699 533936707
    0x41d0912030915061206010306061401140405010302250501021911121c0f020301030606150905130f020a020c13090507032003070801020a020c0a03230709110d05060a0605 75
    0x80d0700700001000d08030940c00104901031701c02440c000c021a9000754090140460388515100a0307400001c403484c40c0a04000408040419a901d11030031107080725028a00160fa07595002d1500e0341c09a040c1504e841000c6407910718a080c424150054007110a50f00e10400b02004a070a0903240b40c2c030020140c80c0a42c006c400301900d02c0510340046c00444811024450310389403c20300e80301c202c551104d46c0380c1c40740d5404401881800503610908025200c2e0183c1045128400000509040154031030a4800d01d5886942801842907802650540303031902e409648499020f00040e40b0380d80410103160041da29500c020300c8a00c40340c02040c41d500d400002424031300d0304649070760b21146028081e0300040710b80241e0190554404218800041840303038001a1142d408580080c101a0482a02c030b207d002084014404203101500c000c00380c00d18100559040100341e00d01900340400c56100d080050720700340311a445c0c00c0261005000d4441d0b8a082001076070303105401c000000d8014000c03c2d0005e0400d00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 533939199 1250 533937949 533937973
    0x4030302100f05091c1b051c0201020f030a18140105040624030f020a030209010803030901060f05091501120f0914010504080f0d0902092403060129041d09120309 71
    0xe1701c04006000c9a00d442189503c01c5928406207643c0000b00321961741c040300102c0403c0008c000030924007220b51000b90b242c44003d40e00c90409000141c02600f49070754445698900e92140749030203000e9a441400114100c615255017402048111016111142020b1010643d000785217807008484c1c40410340f1079110303400c641303603240129410310040707800503c411004800341e80c64120b414003c5c0606001036940303103070102e0380a00f540c1095000410282140350184166591481115881465a40602403504100b00101c40c02d140040c11802900d203030a01c42c41c0401c01582004420a02038141e9010a000e251011803c03110111f40140c0700740e00501446034030510900041c0718000c02e6400116165040b07400240c0241c00075199800704908a00c1c244800560900340c903240c1301c0c0105c01400c8250315207003081a031004200142c0d0b82019002c07480c80d941c0381404042c0d60117400a040c1110304420841c0070702c0400041035420200c0e5205450351186014036071011a445005100013403e042c001030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 533940449 1250 533939199 533939233
    0x307080d0c0809040f0c0212090901150c06050a0203100e0c040902090a0e010806061e010906030507030e07140315041a04230105041209031a180304030302100f0509 72
    0x500421100c0b800104160582980e80c1e020300c40c5141102da0340010701e00f000040c0603140030512007141082d14810b04c40f52901d55a90f0701c200e411034555440c10340603884a58000c544400c52000028665481c101c240440c12696502039071040026080858032580c413503070b5039403d05004442c80c40f07522104010911094040760068103c83e00060f020440f040e131580c081c030700300c0102600a81400c1c5d00c103104001561409440c001c0c007581c550281d40c0700b22454030700000d006071414010101859150400305139114401e9000802035540c180030f81d004d40341c0700e042c220120550b0f50b206600c24892032005d1455600ba05081901941e03011186c000c1c0004840221a41030380c00410680d400310840701c00700c8520003045603081e4011140e9000013158600751038241d01c0041d000d07401e80200300500606100180c42301004106070140301250240703507030310040c0c28186141c04031a40032060102107400001c0540002d07510652000149092005108a410360022603070200c40b0810982c2c01140380782160121 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 533941699 1250 533940449 533940467
    0xf0c070e07140315010e1e0112020901020303040308220b01030b073002040e04080702120f1e1c050d050105030c130209010c170c07051f0f02070905070807020c0307080d 74
    0x40c100780c0c90350314441000554074185d0580101e4000f614251f005029a400440f0041480070640210f0800d100c040000f9501e000003000102400000700204030721400000684ea4601030041103800d207004545048040c2e40d03c2840119010400203000c1500316009a1106882062201c0300c078035000030300032040101140e840d15900c0225400c10011403d4000d5145c071038071030b031700031110b05540302051305c180034040340c0e04001e40344076030081c1d901182c2d0070601060141030340a40c64030550f260181880390070308140400b40191101c4034600e0340303a09600c2d0407402800c1c0b500a204030070401c2d44c0c1da440c18507442c3e440d9201100d0780003442d07803a086c51202c0c03580c0c086d1100074818074022100141035030318801c180c0700c202481aa94000402d0b00310480b00200f10050140030143c0300f842d0b0460030301c60140c1c60822080c1d442c5003440101640224003d1003004490028180710b04244050300381a00c3c05010520b0640e4448014043d40e0014480c1d410000f51a03011038008400521802e05000720488100030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 533942949 1250 533941699 533941741
    0x1e070303080633030103020f0d08040504021c1b0801080a0213050a0b0d05100f0218270f160e010f080a020714070918050a030c06020f0c070e071403 65
    0x14103030242c0c10f03030307110503141980114102d903195a49505600402260300001116248074008240450001905203820340341142c0c002e8a0160322520b81018020800700c400001c1030141e8540407030840b41c0c07134a140e541c2803d0042501c5242e4241d0303da030a20303525800e880502079000322001c0c00b240000c1003107038025540501c9040000a0401036a80050312244406000b5101540b211010b1000b0002e0b41c410483c0c2c0400f10602107141c1018840241002a00c240c58036101e51021a03943c03107155004422184041052001e0760094502468814180744c010750310403c00e0200402080305050042a0064208070143c4601d50202d1010208403004a0700030f010802d82ca07001d12240001a12801e01e11044c0d94220340a44205810860450112107030001422005582c424590380400c1300414804149a054984402d5290b00e1b410101c3c042d02c10740100304104030b40040e02d00c803003500105600041c0d40c0d40c02801080c0d078032110003c441c0d50380030045420940c1c20420218040f80d845e032a400718805 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 533944199 1250 533942949 533942989
    0x2010c020a0905070f030f1401030246060504052119230a0201140708130801050907090b0f0f030a0c0f180204060f1b0606081e0703030806 61
    0x5074580310310341d043d5481900c4002c0414944250204426018020f0303484541886004000c030021245445801c00410700c0068001d001c00d1340b846030305564601040003115010022aa5090f0502c0e1f49121459640040031891a11480700458013901c5841154101ca40007440032072103547c100ea14072140703009024444554801c070700c1000048040000385450a6005031441141c81100302c005401c114482c103181441900720301032500050703030804e5500c040030900020003a103845661138001e00522400c41202d00d408949000003601c0541500080d20030080803050b04e02c406d07900c0c1e40d0502682c4088112541c088100e00c480b00c01c50512151000c8030350001030172281c5810301916102c5800d0881d0b00280b4090901600a224102c00904100100f004072242107203407074a030400c014810082d00c411b9108125500c0c1c00ca9401c1800540114180381d0012404c001665444510b40e035503600c1a0a40c0501540b04a1103800f41c42020075400304490701342d00c46101903a2200e0030040280d281443c052401d07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 533945449 1250 533944199 533944219
    0x15060d0b04050a0903080a0509030412080421060e0a020f04020c0c1305010510020d210e390312280f17040c090b0120010c0e03030c030702010c02 64
    0x140d80301e000b2240545880040041c0703120a5040003402120018500380425060400707004501c07100100310340032580360300c401e2001c40069240c121007601c00e42d40714070b03002d6454100d5000241d0030b2100040d240f03481140200031b0202013000d0b1603200c050005000c1e5001c503e05090001505054001305101045681521081c141f91000110464801c1d0324008440340d0b0340340180646e040071207414002d003080c1d000400091b00c0d0310310000c10715407010303d46409025a085407543c0c1c04140e0380003614800714007410368088140d00b401d0b00402d00f000800003440000e5201e44490012810b040d28100700c3c5001c1c001d41102483c03030b40b402910b1751050014048400c1e0043d64a99204241c01440f04503420664a03010003c6003080018046881c0c4140b040030507145500b803000180d206481c2c03504480c2511004036694400600503101d6001381c0150510400071100c03019021807040d0301c000c070542c444e5103070a42c6408000051641d02d00540f0780003043e503031040103c8001b56005407903800b5800d20040c045111707 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 533946699 1250 533945449 533945471
    0x302060901020f101409120f070215070b041101050a0e0904080f041d070503061f09050a0906090c090605040308090a0b0415081815060a0e090d030f0515060d 69
    0xa020300022140d44019524103020140c04500d200041d0406d41c154000c0a01580c003040721541c81c82120307030303c1251103000076540c0c085480d107074100e80c004801100a41d07100d82c2c8505115602075012101240c504100a40c096881d6000720140d80301c40c42e003035030340302640d00b010800c4c0314542c0c00c041c0c410785118500348000c0d40c04d1840980180040d21040051012160040041001909014002e5400d0201c1442007025903207844030012070720001510001d03808000060240c400e202da607000b50350809403000020a00341519040708003200c40d8008100a22070108100b26500540da01549000800410007000454400c00c00380c41451070081020365442d079500a40e14003a441580700700c02e180203003504442a26004129250300500c0144420500352200715803580ba02144040780c080014484082006600c60166080142c80301980c03404143c1010310040c0c0e942c003042a031140c0000d0400c44821140b40c11400750300c0c0241d22020180c00900c1c4240b0400019400520070421078660302e4801c120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 533947949 1250 533946699 533946703
    0x108160912140a08040e0705040605031611060a021809070c0b1b04030317060a0302060306120115090603050d030624020309030d08011e0503030927010b0d051f0302060901020f 77
    0x82a4410080304da9204e1920791452026000141150300744038007400200411504036007140ea2103c044203032462161103011055460303400031140c01032988101c1041113140000c684c02441071408202d03000f40e0b80303800780d0200304101c1011a2100009a40c40d264000051043c0030b80c03c0d00000d040141d82820303900c0403040d28417900940c0c01607002884000e0941d40b40206026500e401440944554034840e0460b00071070300a10000e003056000301c5410403404000013017940001c0405603201800040c055550490201802c041e000c20383d03090040c91810300c1d4160007840b598089800405519940600d56048140307003000c12111030055010810041d03901c4d943c180a8020082e1070703070701c54100c41d505028644242c50115405403c47c4101c0c02c00c240820341d00001580e040d40c2c000c842c044503400c003860320100041ca074800e2244561118400200f15002c15502038024400c42c000c007000103681e01c04014442c0791070900c190300c8003a0000700c2440035091640040c07014450600450300e0449a07605868 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 533949199 1250 533947949 533947963
    0x120209041a160905030a0c0509060103090204021305030105070503090a11310612020108010306090212060106030603020906060405010e210d0903050f150121080d0209010816091214 79
    0xc500200b01450280490b400c240118094a003c1d0000c18107030038907a840d400d04400c2802142e102d200c070f680020b14540e201ea004440c100c1d0740a0030564450702c1035080c8148480141c05083d00c0381d42450000b0301c2c0c072481042500e200b40000002018202c1c4031740c8a0810300a0307403c0000303400035604204c1aa14541c044110500003120200c1c0c0170685000004040031180203070042c840c102a841403044c050303a4000704070343c1500d4000b0400a81d200c050b1002454504444240000c03038000d1500010388650903a0020003141d00940c0c8c00d02841e954042007240c0307807003240205401326001d100c85140c030382003903c00624040000c50783c44004000d40c0303070600e1900401620500000314410000e000f08201400f00440d50b0039400300078088000a400401100141406185502180800300710782c221527200300d800035550010502c81e0384046010195010754400540300303012810240c040348003034011114114000181daa601c002d0a410600f07400a0324464450944178400084880108508148096 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 533950449 1250 533949199 533949211
    0x31b28290c0909181b030106030f05030c0c010c021e040905010f2307170709030b01030b220215090a0504061415130302010309050f16180204120209041a 67
    0x107989500303800040140307502c0d008013150300c40703e000c0842426060b40050b540d024001121445000654070001290051400f68005803d00001074907107014058040020f00d501c0d000107058401104201c4015240103403001c41c0207401840603841c140e601901108015070b984001000440d564000da201c0e0303420b5501c004100084640d80b2280000f26940d15825820701c420010102308840c40c00210141c100ea5210340e55981c2d002c5450300054146208410420145501c0042440d4075610382c207004214182c12103240007400f08281c84100a13034400740d1101c8585074014608070300c000710b5501500040c0c104800c2c0e6500403556010102e125542c50007042d02410400048590b101e4a80d0304000c1d01034868542d06070f098200304a003916012411340070074241da8083c00d020420100c0f03454035a1a0941c08200c2040d2801807810400c410307084501d80d401142c0003400c0b28039950719041001e00c224450f034410202c0b8070040049280050821241e00c5510601401052298050005503403101e00800c80d68 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 533951699 1250 533950449 533950471
    0x628020702180c130503060408030a18060906050114060c07091e09110312070c061b140a0219080c090c0f0711030706080c1b010b03031b2829 62
    0x74004d6400802c0420800402045000f412141029151031241c2e05c40540340c0041c00f0746502003650005521150b00b96000d40c44141004105a54200100140340070300804580202242c4441418508402170b030300740f098410050041146400c8450005100300701040021f204500e1442410301d482c1e12650344c500b40585682141d00c4000e808041c141b00350031140240300c441c10b10211001c1035941b00f401e41605d8450a005a00300d25031120024480701c095802028a0150001942c000760040b038020001d62003503610003220000d005d4100340300e96642c064030b1040d0b4031070040c41c495440c05151090300010900021454030601000310151540030300303000d85001c1c0c01c180b4280301500301048000e0091001d0300c0c00708254100744004500d2481800c41480c002c8000c6258008031803429800704002d20001000c0b41d41c0c80c81c1c0c04041c8444002e55804200340c81c014444200182504039221102290032110500e9529021369112680000e0f50700b1818010f45108441c00070724024141140d02a0004440c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 533952949 1250 533951699 533951707
    0x1b0a02041a091515040608100b12010e0402010c08031609090e12070c1518050301020306010804080a021c0207081b0102030301050112020d0f020405100c03020309011218080301080628020702180c 85
    0x54141000c1c00b6840071820140402c4ac4062010a544481e41950814401d044598949000403182d805400a01812002c3c0001c1403141c176905981001c01032201c581c1303803002c40543d19010710049032602c0912005541045100c107004d442c1150051031003a200300580005145c4901c820034039007106840240104480c070b0030f0024025180040c2d8801080c00320001c0d4514074145e000241369500240c4024800000426600c19050090000030030f009160b000130314030b00010140095464400b0311403001e480c0112411040190720b003102941203c0c0c0d040c1c006500d03691a00c0c004480c110107541c0aa206035600344000c00240d0264060040c00212800002d80c4940c03c2c031041008480c1c19250a406110030b10070365200007500881611014442401d0524008000545450113025401e074003071300705649080034104000003440598161610001107406a503698881c40c1c1620044200090007481e440d410102c090881d03030020120144041c050303e0001440d13a9070001a0700c02600c4040354400045 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 533954199 1250 533952949 533952961
    0xf1103090d0219140306100602070311060d0c0f0f0306050d080c070801110d0606180b030c041d09010606021203010b0307030f15051e0f060309031b0a02041a091515040608 75
    0x64070b508241f803c4240e04c3e01c14640080a59150014032009290074000703070b0490350319550034050340c0b851041e080052003000300100d001801041d8100401010841e61a6101c1009119108135419550040c22130f91101c412a107540d14a608013465800540c03045431004107440d00c00707000354003c100c3c40782c100c29122422403503180d007070f2160781d0802000c0040e6418a900801013030154001112a09807009580e900d80c0d002094441c13140381c21142c6600815107022102c03003004c00e1482d1040144000801400d9102c040403030315500190380142c242c07030003800180001d0401400442c2c101c20203082c00210b1100000d00403007942d482601c108621540c1402c100002c0c103185001d940c2c480c1a1071400401e03001180c0000d04031400c0341d01014040d40011000036400c440402c00c0b42c0c1c01804105041e074920f40072149169a414060104a00517400c01034142c0301030712071000340a0058002800c000c420b82d6040c0c06401e44254400c00d1641c0648120301e030020460f022002030000d40000d40da5411903240003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 533955449 1250 533954199 533954203
    0x30b03060c0304050c0f030c060403050a11060307090303120207140c13110a05070c030c0b030a0b03030403110103050405010b060a020d0e030c01021236010f1103090d02191403 77
    0x1081c0c079500e900c04008220024401003510320801c2000c68a0340003024115011910f402c0c10218141d40025000901000780000003c4a02c4028801c0c1050344807540360805201e040d0005803200300200c3c0594138240f0010340101c1c4002c504c280411801401c1c40030344c2d1100d004010511071038444942200808440b01c0c24042c0c041003105942c000203200b680311490303202c1d00c0c910a02d400743c0200031000c51448104008804100c00844d040b241c9280c030562a0300190415034429541e200c00300e8681003405409007804029101103039000410700c12000c11043c0158003800c0c0040044689550340c0e80c015400341e0354003001c1c050710001d540c01450183c50b032882c0a07011040304400680b1941c04440c602050360781c0012028122000c192109454820f20200b00d0702c40c01c0c01d00c5001001030a816007203555040e070b1744403a8200620999802114020180c0700b40d60000140520300c555400400c4004043e0400780000f81610b880034000350112200003060945500b42e50f080724602c0380040049046920341 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 533956699 1250 533955449 533955451
    0x310030b06040902150c030c0609030a17010501082d0403020f0d020c1014042102010f03050601081521010603060c050c030a140c1b040507051e0d0e0d030b0306 70
    0x1c103490801c14107803d60000303840d0380d80400d500380d000540050355480112091050b035803a50115022a00f460501300a229143d41028000c54002220410030400300c0d034046000c4c604841c410384451980d5100d480805181031030b180400d28400306c0c003041403c000c02c10380d5000f43c4154003d030701900d0b928030204013280c141040e4000d068215030100200980030380c0c5012650000311b20034100741043c00c0c2240310440c110700655200f030f244a402800440c2d2403164550000d61030b980b00b41d90784a162085880198200c0d4016143c150000d246540087c858008102004066020051000c103020000c50300c00c220341e5401241110180e51115810810050039000f8a04c40040a0800310700b04590403001990701c0c00b9440d5200c0412500c104840b102e402924121240d60782c8400540d00080000b4000452500d180320040d8090b5260600203030070188a0700035035072481200606408480c66405820007190000845220342c01d075520840f002000c000c0000e5140345a158a0110b807004031003081608043c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 533957949 1250 533956699 533956711
    0x6080c120a14060a08070506070302010b030604031e0f120902040b030d0509180705181c05010c080a020307020709091502041832090f031c0506040212040f11060310030b 74
    0x111318500340040703070000c41c964040d940d09a810b1903c6910504080b4094000f00c0040c6400d070043c0f900380424103500c50554500c0303420403000403010050400c41118000c1002d9080300c0003540d14846080c110b2030641088030054002400800c0c4180401c0009041c007502401c2800824400103954580e82448410120f0382c1d22200490101031070b07c10809011072095901121414007401101350450390760385c0f040c0708401c0420000070b80114031854298001c1003c1e03031646001c40c0d04a400201f4404490080341d11612407139000d032420b180750669500107002484030407070b8a940118201110381e01184040e100800000407465014604003403501c0840704d591305840c036950b9446e409550103c01401100522443c1c8140307081c201d40c1c480c3c113a80d08112200042c0342c86408001074076950441c2c401189a6200c255440400058440e48204401c0744140700340c2c0b8681d031018800040114900315500909103004900000c50854520001041948104c80c010001d00c03019105200344041d82c808a68000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 533959199 1250 533957949 533957959
    0x212030304020d23010504060b011b12050c0c030a03020106050108010e100e0c071205041409130b100f090c030b04050f010b091503040609110a030c06080c120a1406 72
    0x108040d0040f07071a0040b00e6401070452424030340c022511040300c542003d0303400c82c942c008100c18101803030f0003806840703121102800600310002c04101c92100a5129604a81c031100388194100c5a1600b0384180d00404900b5145029101d003441c01c1c2e40b41417151810840c03082e4000078119084c440050a450810b80100c1e944002500400444048202100007900d282c0524a42c25039905103031319445110b041c038000c10309036040c02c1c101c80a80d004000350003510661351a58200e00898014000980300484154019617100001c040c081001c20032500d03004a5801038030220143c941c00007254030342c2c5030303442240c10036980c020060141e81d0611891400d44d000b29414083c0d0304060003103200640043c003604070001e00000e045c292941e00c85450552007002c0c120302c02d031030b0316040c2440401031180e440d003904c1e8464040403007501c1d868590545800c0d40d0744018a211420304111003150410f00040000b1201e000401070455030a03440c4814610038010000089190350019010444244019042d030307000f2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 533960449 1250 533959199 533959201
    0x17100302030601290d0f0207151a032a0a060221030c07061121040501060b0702060a030b06040e090f010c030b060f0304021f0c050c0d020a05060c100204090902120303 73
    0x22081e144024003190404080280c81e210f8048610300140664401a000780c0d10000da440b08010301c41c1091001d00300b02000400c802b180c01d9203541002a02540341c0b680c9604a038080d02d02056824000d504801c082100303e00d00c1d0f0035000041090b8400c283c02c64805a070107800203821030103c110b07014014400588040c0c1c03c606082032030400c1405066001030080307407610398032400b056199080d61640300004042c1803078500c4401092041c44000d84084e1402e500b040404201d4903200c0049070901907000e44224945510854100c1c02821848181c6500c000101310003e1503500084c0c801b8000c0c0340c9200035001c203a4800407900e00310381c500c609505c01c2c18103080c21303030003030360744280a547c6c01d4442c40c140c036a602d40e214800148441616410b41c1249641120b4100004d079000e201b000800e4415411078016401d81010003c8146507004025070004103804240480c1c2410740290001020900c201c0301e082441303040c4a01a030700290015000666100101415460b1891079641e6460241c0d020710b00e1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 533961699 1250 533960449 533960489
    0xd0809100c060e070e0a020309120d1e060609050d05070308070c091404080f0a1209110a0905010321030e010608010c1202030103050c06160803100306110a080a0c17100302030601 78
    0x403017001442001c0c450780c084000f804103d81804080c0c00003064034a010f54a1405044410003092034940c2502103103800240d40b14441d0f09403040d40240e238140d17101d50020602d0182040382e082003c1c9000c0700e40b8010b400d400400240c156001d040c44238415001120098102104070040340c41010300e0071000a0340c081070002003a4100102c030020700000300071035a41c402080b015a04200440310051840f0303d002d400c1802e001201c880d5512003d01101c4400c07866681f80005000d6540a00010b013842e40554002840011088981860081c26040115510240c0030441d4210740a6911140322079448800d40c0306a00d51000c2d01d24043d030b012141c21811235046450b0750355036201100c2d0203801007070b000881c802480385070321106501d00ea0103002e041d13580c9070010115010740c481b48400c6031703d00e050282e680c90301201e4405032101c00c2581c0d81d815005954140032400a00710419081c414041150705a406001100c5212031003061019814034846141d403061501e481416400b500016078041e4191007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 533962949 1250 533961699 533961719
    0x90601170313410111070f0306050a0e06090c100e1207060912032c060c0d12021602010c0204020c030a0801030212061b090105040906141002010204050d020d0809100c060e07 76
    0x2426460070f180c13a5030b0300407140524a24140161b00304d07407c07101e0501d6001080040c140c12440c86000d10303000c14404800c4600a4580e1340c00f05035420201070300105103507002801c0880302141c0c2c130a02450b0541621b4003480c0480c0030300b900031500280d160400c09050240d150065807982c003c240711214a0000104c076107008040c1501c00b8580c00225400c0007400702105002c1c50314501c010f400034101ca94440b40310220b19a03480074861743e0004140040a8110020300c248299844800254041d220300740f19640111040640300038100d03845542440140410030041000d00b55401194540708510350460041100e81c0c088020301c101158418000c0242450705176560005c0140d41144141c0c98040441c016525070040d0381050303400c54681100064458800c05141e039080c03500392094992441a45822802d0384102d01070550410251908000103007010310001041c60f000c3d1040c02c0c201a251000521840407030f106500000300050a20818003440d4442d021003100305030001c0218500d0708080306 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 533964199 1250 533962949 533963069
    0x301110f09060d0207080c07030b0114180702210403110411040b181305070f0c080a0c060209040c020d0801090209030a06091109040c080106080105090601170313 71
    0x6002c0c0314003040c8143e0150030707501500c01300c0d40e0190380a80c0300d10590940f5941d0f0412448140c4030990b80400008030144081c88807820003401400c00310841c203c00b00c00380b0403204050441000c5203da1700150080f403c0149110000d880304003e0190303100e1440c01d000108441a8817141d2061340303403403550003103155000d08440882d13008540b842d413103000c2c80010289032410140200e4005001c080740c07541710305082e84064417074105512210348055504500b1038400d02c400c80d008000780c0d010010312071000d0240c6440d80800c1c1c403a0001516114128010405407100e41c4503200c090707400001440d00c0c06400410b0103001d0304000c281181856024030010343d441d030314200040c2026590f188180f050204001040031a51006800200c0da400c29140a2002045c54031401c0155440e10700d002c100b144060145c0360180703640800078502030742000c0c115004e200200c0481c42e11848104a00740a22603400500001007802c1c180300380304041d070084440c94000110f143c2e0a052440c440ca181d0503131070010002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 533965449 1250 533964199 533964217
    0x1a07140301210c18050a06140a0303080606040f3305030408030a0e0102071a072303061906081909050a0b06131a031501050a1e090501030305090301110f 67
    0x41151a2901e04210107101c1c0300703401c00c1d0040190000c040401c1315181c0c0056000f4001d84100700016561749103002e13a4140010310995010390300701c0d42003020920601c0416000000105101e152503542c21014051418560206500208941e4466688402d92400f400c00d100d203620170010a96140d00010030912000300b0040c00c00c6c02c00b002140558150340d10652a20003d400210b543d4820b9047c000e0012039001c002c80c3c0300f9206480080d005a101e01c882184003105002d03041c0c5041002c4804440f1340d00000c200780d4000c191b002d00c03070b5107140c840010a8001d1125071940700013818003d9110440210400324103400d141007000d42c0001a00028089940039004840207400c0c0e104e80c400190071100c0788003c001498207001c7c200e00004006090522486070840480b80704000303150300c820395400240309895120f106900100041c550400d54a0715010310300b82000d0502d6101c00501003228001c0e0000d0b0300080d8041104481814244100201041c445803154200040b070b9004441c184101801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 533966699 1250 533965449 533965499
    0x10908030a050f04030212100c0e06070618020a0608040b0603030a0f1206091109121b06030a02070f11030f06060a0618090609090c0f0b030c161a07140301 68
    0x4202803003400c1c03009a4026550040450711031900c2c7c1110307650340d812030606c10400c1500d001c00c1703175600d54040c504000203050041e140300c0c01c00085444400040c07036030b808160712a881c1d44264030016900c00300b94601500c100e0300c903561182403a003001e0140c500010845402903204001c011a0340703400100c0841e90880526003841007011100c030000140c085075212114441c101441c030540d420110010300050380c0306994440d07000515a1500340d689180b4400441c2d0780a2818103c00f42c1e050140003164003042800c030144c9814225a94420000f01d1000c0030b41da91411117803032002602e002d01c0a034402100c0704000b0200f50400320001501c000b1130303100781e0051120070950f4540904000901d0802040151010008250ba0340c070302002414035007a040ba00d61547c400003040076281901e0480c25103220a03030050841c0d640c03071148081070340f140e000f8100b4030002410340800100a40c1003039950710302030b450190103820321100140814400980355a120841800103005420400303d9400c200c080c4091 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 533967949 1250 533966699 533966707
    0x203070b0601180906141806041515020606090603031e131a040501090807030807020d020d1e1209030308040f03050919030b01051806040e1903030b0906010908030a05 73
    0x1c0140c85520360005001441c442c0004001070030704241c1e01c18801c82e030ba4014a54000c2801504000020365210345484035601e011002c5038030360420781e004000b840b01c00b9031030441c01501d8000040c07420801440c00d60042e400b080c100101410001c41c1150090702c140c000b941410315010b10001e190403014100a403100011035480e00710301085c600e51006141100050112401001900c501d6911500800c0d0116101c100001440400005c8200480b900145020b040481c0ca90810000c00031000d0186c0c2c4c000c200ca124030000c030b50b10350403e02048400d046000800c4045151214049420b24440d01c10f210700a0f4080011a805c207040540c040d0f4050540d00800c0344c00e180a032820f00801401a421181840080e010100e80030440f400341c0c0d00a00c4001e64903a6110100030700c483e10001914011203081020400504054002402c2080782d082610b070328900000c088181d00e10504019000291074640c031a000341400c0e0100354000c542807030032060f031501342040180d4074820440e0300010040e00007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 533969199 1250 533967949 533967961
    0x171c14060d1b0305060603060c0c2e0615030510050a03061805010c090e01210615030b0a020405090a02070201050306240a03060e07020d0f0e0103060b161202030304030203070b 77
    0xa26404001e445180c102c04074a4403400c01070780e20f180445455000348203810100e0030384040c030425613015428810007050104900da5034a100c3c50030356171280401590700c400e2100740313401601509002e400308480c1141942585603005055900103410400036003c2c42c401401140c8858000340140c0350001c03c0400c03d083d8850101104c0100c1d240b01401d25407829440001c026440540034040310911040d80f6083d9032166400c0c000c0340624039001040500b998450000601d16400c510040c60035824501755099403520348510703554003200d148000c164000b406000a140c03a60046400000040f0b045003022420750000c0c10a10010304101d00c6585200700340510500810040812026030150301a110384400d00050b001c0c0c1101d0140c044d44004240c00690100e2000a469503404210342ea58884030119542c01e860f200759044090f0f040545a42e03000c030b80200c00750000c0400d6000c400e82d061070781d44035080040603000390071460000c44d00100b081c80042135001042d200d03e0b940000081e03455032500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 533970449 1250 533969199 533969213
    0x130b010905060c0c0102100507090303140c16080d03090c060e061c1e0b010c080d0b0301060f090b030303070e130209040c0f090b0a050d020c0a171c14060d 68
    0x259000c81e034052000144000d49000200c0e030313091149000c1c0c003143c04a013034800c40301e0b050303e0007291700800003100c42200b04003107441244000310040c0e800703e40c18540b0120361800c0303042800412033740440d45074a00341000b108901308410100807000345000c10140c10603941d84d40f08540280b05945c100424540c10038000d07922101115503490a4a00003512040040c24410251500c0d040e070f0303140750141803620a00307802180503450740f00c90141e50358a00986a0382d24113480b030b00300405000b8400e0391518070250b280c50074403508000d4020b41804414003403070318030b4060545154150b114040d030000d0051008071500007205145008080b543c1b1040c0c03001c0402144000c3c0141141640e200341000c280110042c2c02c14480069500c1c2603446102aa484d10320354286031140d01d04460000d4002c100010030030740300f035000d032102c444845c09072041c269554131182640981000c2070210006c0009001c420404405e2104100000d202d00600c06410001c0054020030300c0140420f00404000c00d4140c10807481c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 533971699 1250 533970449 533970467
    0x30c1002060402150715091416030203120f03130539120d0c020d0f0c1e0302060703030905150a02040602061308162f01080a0b130b01 59
    0x5401a191410811002075503100709803016809602c11007031a074800c24180c001c94207001c2e00301e6580c0389096020214180202400e00741a01c0040d44090b6101c07041a0601000303c2c0210350000001565013580101800d204481c000484080c85c200842c101c21002c0406030f9a0211941084044058403401c1481c101682d60107100d81c2d100c03d00000c070004080d07801031400281ca418100c100c150001d90140320162003d24146040b85c0d126802e140b11091140c410314600c4d920180c05045068110b0341e44002220300d0002c00c842c04608424144a003181c164030a50302d0b03803000c07012800b000d441c54000c40c2d4035108a150141c1007589440c0380c1001d1140c1080149003c20501c03144000d1440c040c12020001d40050090200601464001c218400f000c059481a100e82081c045403808160115420303408566481c01c5603800000441c0d841e02d2240100407140f050f0003800508081e40304000010501c0d8801403419030458600050104151240c0d03070005069840c407400021400c6040300140e0f50405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 533972949 1250 533971699 533971723
    0x19051c050d05190c0c12080903060103030806030d090605040306022208010c09120b01090c140f04050108010509040f2607050307020a06081501050a0509060706050f0709210203 77
    0x104266601150981c04001085100e08a42c440c9008a41c49001210b580010890141080030706070010b0240284c4402e451b1101032295480e5491300d078104d404641407400c264030507800f08600300c040140609090000300302c07100440c50140c444030f0038181c015119001e41e0001032705035a40411004168a560b2a54009042d221240305024070342d0307003000310301805c1400030f00390015048580010b0200a1101134101c9940d0000303003445a82c0c02c10220314020300c045090803007048041c9203400485410a002011900c003d41c41f0265203506000c0007408030481a031006004a0040f8104000300305c0c0200e1550b07a8686c802445141c41c000007002c194141c941c50700285242c3e900080210030032400000400c5490710907036000e04056070307072a0155040e21080703a10107450b20080c200140558800e0005205199240c10901e08001c0c84102003800c42d041441c080340d209544005100f070a0039011a880d500840c00c3c588a5075007803c0072158403039a02c000c03480040550030452040215a0b050081300780c420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 533974199 1250 533972949 533972953
    0x708070c02180a061e050411090604140f060c0a03030506031216120507051b01140318014d030403171f0510032d050619051c05 56
    0x1080c41aa0b94200000a40d0078054030340c40d01d01c0000c1c6945002c107003955010105e00703451440c9403500041c800940b40003402c04444e04010480d0b94407030f9030f910000d40050100c4104100040101c1c01c02c6c00018185082c1d9184a4203091240c070403815000a10805c466a2626020905403109000709240480c03c8000240d10300c004107120024601c102809200940540e00124030300d01e40c81000d64440c4503c1c0c0014003140c2201d607942c00c0400d000b03d01a40030990615004209160034901c2c0e015a1b0429100c042030b002d400300f030a200145090081c0703c6a401d21102904201215001100308007070048103010f4600c100011101070b00b404400855407101094548a590345010300c0d00404086114222180711104880071400c2c1015410481c5808000f601940b00506d080c01d003009401d016505181041603118800d090100204030781c01688070089465640b8000c0a011711101903a000500d82409851651804810b4003000d01a440880d4010342c1e00c036290094031402d07445d0320400d0800140040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 533975449 1250 533974199 533974219
    0x20a030212010b04061d240607050f061e070311090f0409140a03110f03030109020c03160b01052103120628030209060108090618070f081b0a030b0708070c02 69
    0x3030508050940d60b50403a00d00c0441d0341c5800203103034a01182d0b003811101f42d40c1c02d549440c0a040000007001240d0013041100d480c400314404081c540b0904407040d20244021140c0b006900410710100c5c0e82104050401b032060500032003444105024441e50144203494402044116403601d501c02c22050741c1028220328020101244956a420103407000c4000600101000e5070041000c02c0543c20100e884020b1840c50340b800702e401300a5000b0040382004d9010800170b2006201c0300341c0c1c01a200d03a124840c407884030742c942420021800c2c0600b16184074a081d4011a801c08200031080300c0c00804000c10a10058803160081100c00d0105013075420304405440a14600622a100707100c1102d00c02c56450602d650307518011184800c05541040d032aa005002059090350036241404e11020000125911244e884c880b4010a0f900c40d07026035582d030050042c02007000814a90007900e450240c076080e401c145565590044201e0050841041026400100c0e030b84910507200f00c51425002008510a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 533976699 1250 533975449 533975459
    0xc01060e150a0e0f1b160302012405100905090103053a0c02152a160612060902070602030f07020c28030b0106050304050d0804020a030212010b0406 65
    0x4145000e9400600001c06100070010501d425070302074064610300841c1c2050340d02ca880000a84040c0680404400021050245144001c01001e0810a040c0b5099071320b200c030290030060f0850b0b59000002003810ba00c1003404000c03581507103a040c02c4540c00d403520f030f03602d00a00004072a502415000b10341c0c800c85c0c0034000418824000740ca45564032100c9804140c00010100764202030490701c945500200f19581c0c120401c030b0103040342c3e80c070407400504421a80da462200d5030805601030f00390140c0c64441103480040c04461a500e24a841120200600d80120602c801c0c100d0107002d4811101002103c601c02c1501030a2900010000c0610040564485845141160203500200c41040020704903400181c203140c80000c1910800c08003800d900041c034644041081c84510803002c100010010b00c50000004140c01c4c400e41c001d121554500d034132818a803400e07908100d10022407030f0030054008140409039842211060031203604544000903e07076554092409001c54865196006160030390020f0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 533977949 1250 533976699 533976719
    0x80304080f01050603010204050a0e0601140a03150e0108070b030a1506030603120e060a0507110d050a020a0603020c03030c0c01142a040311060a110703111005030f04060b060c0106 79
    0x21049400700901c040ea6449040c58200d00440c0f042541c405868203081202d8003144841c5074210106240591850104100500c04d5038030203080d80d40040d40d544100c000601070f0350700e417002030441d040d10490706502d40300005542d103a19008401d2001000400f20f204c60300f080d44180f42645400115258091f42d07220060000c02c0180f1054a001d4291a15030340300600c905032403100c1c0080105014100703408101d04640c503400c007000450b0b0010041300360068541d40c5040ca042402d110f40000d100c2d03410315105101c0d1820b0168806403d250040c4824680d50380040705581c0c1c01180e03440269214424001ca40c2e014101c80643c2e245000800400e0141824140c5449080b46600031480d601000c0686c00f020b00b13034415484050b00b1140b16666011440c0f60020061502c202c140c5401c0c500b55282d050002d00700a43d60740b048841d00039500e2514481e00342401425000041030810798110703c0c040a50400c09003004000a10036907584070721030300c159a10707010744405481c0c4100800846440e05041d103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 533979199 1250 533977949 533977963
    0x13081f05010501031b030c0201020702040603080a140a05030708040c15030c0f0203070c03060f0e12030103021306150f02120f030613060b1602060f0c0615040606020a1b08030408 78
    0x21220508103000414107502030f01860740c0410303c1152119500c60405c40031030042c421080000d0071035401b0851400540e4a070302480b0003641c080c04100750b80342854200a0201c00c488440180d9050040c0505418150001c6c25258030000504160219a40b90300d00391581c804940c0003200520170607800700083e0b82e4554000d0014480c0c0b51984442d01c05415401c2ea640e014040004045901294003840022000d8201c25032200103280e022504118440d0311070b003070000c001c40b18040c021021004200b5450b2404400000005c060b0041043c24106030f20b2411440d84ad40a10080c003500a0700d440700d0520030885082d103081c0c3c080134702d42c4030300d0001c5d1411515071080c0d0750280f1038410314021842100c0941b165004403840d0440325450895511115084203003c514142d9001070180070386814a0007083c000c2284401000c05007141d85856240000e000003000000b9005034a4420140111034000902942450700726041d13a48505040c05202e00307940d13440d0000d0b501400081800210742800180003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 533980449 1250 533979199 533979253
    0x9050f04030e1c03031a0a030b1e0f0105060a1103160524010515041215050a060501020c0f0f100f3209030f16050307050109080607051308 61
    0x4003810200d8107040122204214103802c010f8030240c054480028042d611610b001e024210740282c0a0800e100011458491603000b40c4009500c0410480c65801c0c50000031100510540840c420f401c01035034041d2803d10500420340034402c002140340049001c1c86038100e03402d0f40502200c0d5152600300e219441400b490347d01321650f119180110780c0304c1e1280d020803228200b2220741013855a180c241001010318214002808444081201080c60303103c402003010f44e103005101000b40300201591031800c640e4000c1504d0091490100e060000c1c0ea07004c00d01004112044612950080c003140c0000c10030314203e11070f907070701400c8060884910340d00800000850351031910f0304400100c1c141c0440c484103400b5560181e00c0070141080c17290001000014201e910700c0902120b021a40500c280d5242c92480d607803043e145043c0c400c003003009280410100d0080c1c58280b0308018403600e000011903594202070921010300c03102207030411300302c071980109400414541d030448980da00d045034441c020008807924 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 533981699 1250 533980449 533980457
    0x130204061713021011060106050a090602010b0d0209100506030405061506040f0303050f0408030a020708071a120a1803030e101b11030904020a0e09060f130507050409050f0403 77
    0x300c0400c0c0101c0081c542d12502101641d02c000300d807254200b1494036155004c040610a50b0020018107800030007100d070281800c0d803605941c52070300b0340015140800da40e200c50116818031045880d036859081200305a960f040e9a50907080d11001021004189140c016680084003c001c003c10722a0028069019600118900350340d94800c000b802180d01c07687c069070174482c44508082000074456002001c03146042c02c000350400da00d400085085500c10f46601c0016030040809001c945800e108100040c1001e222301c144089820007002c0ea98007a41000c0100d522181d000140c003403500d0741010b1041001d140c140344c418200c2e441c01030018032007209070700d490f03100d40c1031007141030711301449a100e039171002034030949a8420b0300d072080380d00102d4100c0070700260205214280385030300d481c00689509002621502c1030148024280120000024140e070b11034060300c1101d41550b141c0d883c450000c6080c0d05804112640d80c080150743e98441c540c404202c940c50041080022540006218040d80c4a80e417 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 533982949 1250 533981699 533981717
    0x304020f0a0f0e070c140f100203160c020607020301050915090a020f0607020d1e06140708010302060d020403021008041406331801060f0f0210050402060913020406 72
    0x9124085015010301007082e41d82007814040c10062003041e41d44a441c51500b9502078101d0794070342d0003101c0c000080610315400305c00d40422141060088a80807902c04404500390310f040e880101c40c0c0705046074600d06100249001c0401d40d100c05003100c0c0b0b0345402400034046810002d14140e0f940c2411a030b50042d000030180070448100000c104a52181c0d0014103400454086c5800c00801d90722840089031300c96680510100010711a4a415541c1e240c0040606000319aa00b452000e9035880403030343d42440c0b012001c000566400ca04103a0543ea0151001c40d2542281f40074807000384910740019600800c4404008a2164440d0116204d0381c1718801c4000380c100304071881d41d5581416603003e05410256904030420f034040e00c004460845400d040100e403858140007049070503410459110302ca203c3c0b107006020203034104e18158200102d070314003e503400c800100003d484140c4000320f21019074a580c00f1030700350b60f1200c056940c50100207284120b004020f0141d48003c1d4450b21500c0c0c007040d4503034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 533984199 1250 533982949 533982979
    0xf03030307140d2412050309040c051b0d0f020307020901060e010c060501080307030306090207020f120712050309040e070608010605070804090509151b041404090b1302150702100e01021011030402 86
    0x100410017156001009500f0030751428208005042c2c004600020800144450041c10f00305c008012105030402d0086c0a00a020141c01410070119440440c1958001c1101d0300c0140c840071142411a0a40d00d8001005680800102c480c404a258040d0030750381003c0012070110300200c0200011071180d20b01700402c50365078000000364016200003075800f440384a000000c50425080740c00c4040b5000040d0384646440702e40008880200100c141c6850b4400314046009007001d10803500040f03064001010440e28100d0024940c144c14003c417002c002004c501101000b08501c00e58000d85203c00e410301851034140c2000e50b6500d0307000c0410507000c49200110303016030402c40c14402664156450b1500d8030307090602002030039061003401c0340c000b5954082c50001c40e41400031107008000c244450a550310581c01084180700043d03c0e02c002440c8104011001aa02c02c42d441c0641c10517402c1200e0781c1600100141c0c00d101028407000341c07442c2400d00c45910740144034001c5100e94800c84182c0b170600851 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 533985449 1250 533984199 533984219
    0xc0a06090b0901030f0b1203030105040f050c0304080a0201141e0708011202120705040c08090c010801051c0311060711070e0c0f130302061b06060f03030307140d24 72
    0x911540002100c00c110b039001d154802d40040c51104642480480c800400001194030a5407010840708150408001441245464082c1c030484c0e0124000501160400358070070402c5100203000200200b1000800500e035900030740141d843c00c20100002c1e1190b1402d80410004850001200c51240007040c00107140030b402080c0d4541078444041c510406150b8641c02c9c030407951851a00d4101ca84504200051180e949008510081410b6036440300a410704803005440c0c4022200300506010041c0c0041c000c584400f0038400c0f403072100754208007201009050588108040d0798000c41c041c00303000200003095421a061120b101304480c00c40300c840c1c0c2c0e510109041e50f4410340700c0d000142000c1081144807800340c4007918070810f000350000300362a84ea50010b0600c0d03010310242d2011420800b5a80e000c0300041c01103c0d032046040e1442c06408298800094070b034070005002e0230501c040302007848254104202614020a4181ea042020b6141e5003204080c4980d100a5803642c12040d140c081505821 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 533986699 1250 533985449 533985467
    0x11030d0309120f12020307050901021006120f021309050115060815060a210f05070c02210109050a2d0b010311010e18010602011109060301050405071701080c0a06 71
    0x4081d5001406200a007210340240041412082000613040c40620301d00f0b83c0300640c0140c0581d140d041d0340e083c8500c0003900300b01615464044913841c1800030010f820b4a1004002600d40c085941540c4040d0303440000d0164100d803140c40300701e0340703400c0b041410404150b1200f0036400c045085074820303564845044400401c2221f0104500304510740b03a82d49070030b004024040500d0b80b03041415134900c80340c10f0212041c0700044414241c9450300e0034418a40c29510036a508000c09291002200d90250049891141c0d4a184401c5500c69201c3c1072201c500b0030340c00b000d10a6071003002d444046815050040c40c2c0124038003911001030b6110003070505903105881030b50400394000f2015080360310703680f10041402482c1208505014850070749001d40d5484400900ca0344800100a51081d410f02400a003103c107543c6443c41181d200f0030100c1c85a56807001a00d0450f201101c0c0440c0560311400100c0e030000140228015840c1604c00202d100000426070722141203041d41e4088440355a55811100001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 533987949 1250 533986699 533986703
    0x1030b0109091509030219080d0f0209030c10020c031504020a0806130618020a0b03041b0b09090a0617030d050901050709090e0f160e06040204060e0d06090f11030d0309 74
    0x1c0444078030041440f241c001e0341c0120700074016620303800303c60f02d00513031184100d820840701e80302e0004404030703d80001d21851284080701d20046007071118041c042680c2d0142202c49a108021219140b01c3c601d01c02c020755462442e020f0107440f41001c1d401d01c402c40d034900030355089100e926065408600360000180c4640b0400207504d2000c00121203480d040300500300303140e108807641c510000e03070005038a48410311801002e40002003552071600d406c10808500f40301c10640101030420344104084201041034500030340040b00c4002c060f464101440b00208002d5001142e0448140b060700410304002c0b01808a6070328583c41846165511203e41d800c8401c2201c105c408600c20801c107100c400500c1c0c1c04100780e40c01d5001142c81503001807203018a85003602202c100c2c000750010050000061400e01180c0220041d42e0a40c02d003410701102808094624004038011401003420a040c041550444130409030802e5084901d0701d07280c101040003101c0c843d03080d4001d00ca0b90302c100b10201d101e40301d146404d071703 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 533989199 1250 533987949 533987963
    0x1060504090b01050118030b070f030b0a05030c04020a231e040f15032a020f0303130b0c0412030203030a050121021003020f040f0501270902092701030b010909 70
    0x603007018011b4892031a00c4490034030130591030002000055400ca1081e01500c03458407916505100e0301e0740102a21000090a0b0013401441410030203900c1c0019240ba00c19030858015803544e01002c0200c690035210081091654150347c5100401d210103402415114000419034440c401e442d0380c950300c00e21661203140c801510300c203001c01c124a0841e0741700d0403056092402003100406002944d031400341c011140024080c0384880000415010018400250349080c065820340c40c0c00c0b902518001000c2c000504841c83c0040051400c14050046a010b400c194101d0801c1d00ca99041c02566600f04131480c15095191134008101545070140e00031902c000700070a0118002c859090240b1101703072440b800305040d0203202c06140324045070040d001500d00b01c446410002c0c501800146a074168502c3c540300c3c03164803060060071000c0070319460f0075100382000260303581000c00301003004480b070b21400750040711011404080080320f074a1040e04036400b8074200340c000c0c1d0300c61904004862842c40014155 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 533990449 1250 533989199 533989201
    0xb031e010e190603020907080105041b05031f0305031b06060406050609190914061008040c030611040302040207060c02120a0c0b0a0b03010c080a0c0302160807021f0c0501060504090b 80
    0x21202504070720400909240085001d0b0ba580d40421b50000d815680c4a000c1903480300140041e04051140c03408400310035156520910322104003412500c0041c0180361262241c4600e505201d0341c4584050045900600b201c0d910024940048040740400780d01752640d00406c0080b07035562034180100303010380d64010080344c5090304110801a14003c400c01c0079202d50001d003400204082148150305040240500b5400e03985411000c10080c40010344604080c00303424828440440c8110300e81d4401c2d20340c0b0010000b1229240d920513065801141d00080d07109000042d401c0811040350021460a132160b0210341c4101e441601500701d43c0103c5020400040200421602103405c1d03070945500400c01d080c0c000f641002d40c0c0086030942d00c04541041c0840c506070240100c620051007a98450070f45440c0c00c5041c0112190309441c0f034184814041d088900125181c4195919500e9540168084146a402c0e508030150302411010030000c0980d1207519050000407141064010141c130b26038009402621 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 533991699 1250 533990449 533990461
    0x4080a2105030f07110709090b06030a0305040e040302030705030d0209100c03050a030f0b0402070f020114040e060904031e0e18010e06010305071e02070302090c2706090a0b031e010e 80
    0x78030b080100754071300300140d81140c010050800d00040e03014150780c030004116030913641850708592001507d40750080c2e1064016501103540706050b00c040d00e800c0700c6413a5064459007812480c6001d80540031b403036804002106040640140d00402e03102906840501020402585c1682c601200d8240a0041171080050580d114800e5000382500c01020500141244090020070100d07006203100b00c84050203072075042c1c250343e04101090301c02d000d4054560f280500304404180c0302500070301300c030303000d40940e802160402d801481c003031054089600c1240802c0c80517180050641c07070302d03e440034024802d80040e038480e49000301d426410303242e503036501003810386a00004400412008151104100c2c451400fc100c108040e00712298165550f802804000d00318010440c000c0d1004e0540343c00c81c03c041018014003144000071150b0800c203605c00381521605072001c11207a2190b243c0c2c1590000c2505001f05105026101460041e080c072242500520780b2846d084500c40e02c20300440e402c4400c46000204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 533992805 1106 533991699 533991721
    0xf011d0304060e13020d1b0e0f1e010903050303040b010e102904150915020105071d010507080d020c100203010b0405010309110604080a210503 63
    0x2207414981a80a04a48682500c850003029250303600c0604106541c161020a41451010b21031a58424208601c201c403001442002c90341c0941c907030303002d420150343c12103415401034206c0b2104400d9482c4a0313440340028042d0785c1003108030000800024010300207507009a10440e510b051650400028203c00362000b40554026041c083d402c00c050803140140d000142c1001031084410130072404680d0b002e101d290414030440c91038803c0500c4490b8480c1e02c00044444a5a50480e9002e40d00e03000ca00740c0344245c2c1c405002a240ba07104101e00700074015020400c5005040451400d442039480092a8001d0300c330085019038003140a156020091142441004c100c0408500d5581000001441b9015900a103810996074403034880c10464051114101e0440080465480d541e460000c6580c400305648211403c0f41400d00d01004824000070031010807640ba107410f4115500c00c03e90f55 = true := by decide +kernel

theorem cover : BRFrame.Cov 533812949 533992805 := by
  have h0 := BRFrame.cov_init 533812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 533812949 ≤ n) (h2 : n < 533992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
