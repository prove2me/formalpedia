-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0168
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:14:03.686964+00:00
-- url     : https://prove2.me/submissions/41474edc-d7b1-4f08-bca2-91640612904a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 30035976 ≤ n < 30215832 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 30037226 1250 30035976 30035981
    0xc022401051e040204170615030d1404030602030f07080702010204030b0403050903030d1401140607050d230a0c030f0216030b0a240306060605040f0306051803120402040b19031401 79
    0x107030782c000780250740d66900d48010324001031080181c0c0e103052082501083e0180d81594000001c1031028008000218210300200c801c050380348100e201d002c1c8104404004510540001d500c528070580c003004ca1030400250003030403d20014420b00c11a403040c0803d100080001c3c2c00c46070000e03010315001d43c0b5521040000b07403c41c81285080441685000e002c028803840140303496040f03c211076012842030103140c05100e0540b04070b11004106d50045500c1d00d500c240075000300b138540c00c114003180380103000d58110217140d40e03c0580103401040303114103814105684006000800c503094030241c440c41103442405082d43c1080d000c020036009450002441004c525406080504070039420060b03007050f81000100325155a005c01e9441078281400410158040c100700c9013100c96003000c04c2043d40c61a11260700400029101d1140701c51001420001000100003800d4200c0400074242c1080c00c1030700c10001202d61011240307004030034020701c80f80300d0b4903440c800341c04898210b50300e50050420018010700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 30038476 1250 30037226 30037279
    0x10305040822050a0501020304060203030a1d0a0501150510020c0d0503160305030a050109020a140708040b0f120108010509121b0303011203020613111903150c02240105 74
    0x9085000b900a140e1668080420004482080c1c40401c036140d01d980c0120703141e102d81d0086a001d070b8810000300d00c0c0301849900260a04842c88000840c075401c100e41d09007030030075614095580303a4584450945217000c081200c0010300c0129001d0512540042001c0c1d1940f0355034483c0b82c0b1800104203010188401881140c0518408002911002c403141c03130041c0c400c2d0010b890000b9031038036200012a58181c1407007200d05401554031500f814a0b149110240640c0c0110130031100400305000c001104001940501121040400f445882e589888084802510140d024004176070510003440340c1800b002c608a0001010418071a030b82d04000410315601d004400e0303440039070340710000000450083c46400d89203028820750a503409a1604080440350443c1003001400348001c807402ea07001c41ca00207940c91340701c0e9108008040220b0366030b210005600002c6c27000262003074413101015081c590501030f00219481e0f031035140c0980c09801c0c220040100b0140113090140d84000261029686005000c08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 30039726 1250 30038476 30038497
    0xc02010908100603030e09040201140307090f090b010210050c0901030b060c03071101110a02220e1b010212030114060f0d1506080702031c0203060a0504090b0403020c0d110103050408 80
    0x51020502c2140c07400107283d244070a4000401801c0900c43d81d25101150070301498059580000d2802148005e0206a10107410b210a120713031007100140c0011a00c0c18100101010000000c80c1342184001a040c40020469a0300040c503290400c1900c00c540d000361072582d0340a2900042e56078240c804508944103a850070842440b0114807901001002501054201000c0c0e882c1c030100310015101e26a90880d182c0f0003540411480c4100455440004401a002d02d90010205080e411819400d061011f400702e59070100503176102200407960100844200c3c0d80c0300e03810080c0303991314105c031000b040b5000082251080d000042d0203500100240306441c1c002821410800c40a1a00c0182c2030340c2d000c02e481064042456000010012030010080d11000c540e80030181e9040c0e520309049200035803009241aa10001840c00030629444038411080c1141c8074068600b03843c1464203001c0e10345007080007814400c1c0044410203000174208401a503484c44203007004107460701c9034940a0094060344100c0f4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 30040976 1250 30039726 30039733
    0x1401030506060f03070f06050a0302041203120c05040b0306040e010b091003060f0203010e06010c0201113003040804060309060204090504080304020f01020316020d050f0f0f070918030c02010908 85
    0x4814050003044081c020710b41222814049000c1c034080c5925015540300c1c110f2a040c01240400181d07000703000401d0031015500e4018078040d124100540c080503544415400680994035030210700d092485900c0003140c0310b081c00c5007454504001541c44d440001c00c035034010b503280d0240c2031041c84e003508180300004004181e54041d02c4c0111000404407107901c0181c5140e0700340041074000fa03841c0c0c421a4140c80840d42509026600c00c0d006449a00c5480700c120b04000a40091000254041c4011407802503840748145000245c1c1c0320100402103c2400070081500810034400004c001d14120380c2110414200812304c1240381c02c05500030302807640101400ca003000208020400c42c14025072260744203c4407119400100e00c0126a86d0155800c81c01c00c0c0118032441c80090700e8200002e03018603220300225080a0305106410741013500a6035421034a501000502200340320a11080008c0d1050000c00c0100c07c1000000d00074a030100100581400025081001035901c640362540144c1030b440100d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 30042226 1250 30040976 30040979
    0xa1e0c080a06110708030105041a060309010b0f120303061207121101080a05010f0b07020f040c0503160e09040b0a0906060803041a030108030304030f110a03020109110405071707031401 81
    0x41a0321069030907800c580d010314100c000340c400b08902080d1602c036078100d8a034509503802d00060200915000201031174810440380707134807405d0356020b00440c42480c41c1c10011509c4103900f02888418015440150711600b0000380d19611400c3c0002503984c0080c0495019002240d26684681481200d80110300c1c0c000503046044140010044200c45058003039940e03000071398907016004101c48007801610309155000d601000203414140142c4101400200240c0c803140c00180000c0c00c80e030f009900500803c802004210420f0240f20000e14800c03000d040030700440403c400010910080141b005100301500d20116407091155484202c0d01c81d4003860800c140c0f615503c290f580da4116100c1d800d40c05401d00d1781071245c0c0c080074041d2412202c0c0b20340210305644030350340c09654610000000070200b007070021010452500c10807410421600076000054802a1418003140f018410f550190085051506120380983e204d1010a8140403000c840d0710b01d921610300490146c400a10500e00e40c40380d4000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 30043476 1250 30042226 30042239
    0x4060b010c0f03020d080114090403050912070f05040506060703020a200303030414061302030a020f150d02030402010f0c12210e010b040e1207030e0a03020406060507050f07080a1e0c 80
    0x102213030340c2d0380a0f4032081c109072380c0c44100c080194680c401080d0425031100220380042c1c010300182c007036008002c00340d046102c0341c1da90462070045164005100030700362403010895030801c0d100b05600084155403140c6003d400b03072806035454040440003054249000040c1481441d50105151403203c01000c1e20b683e400c082c01c0102038081d4a1000034114007900c4c02158452405848031040c9030b6000e0040c28074104075800301701c1c14000300c0000c26003250940c411030b0115840040101145081c0d0f0000503264145070000403c88440c0a1110702403020510448002c90140a00842d8003215403500640c0000251400c44d108002068513401c500e040c8a580722800c030041d0810355403034200362002c01481880e10005992425402103c6510395020042c1c68040f83c030130044000440c0c0050100c101c015682d40c0414100d130410b600c900c00255011400004202e005e0041c4241100c0b26001454003d041414650700c1d1101940020207051405e030149404481c4000c2c0e0100164001e440304284a60341d12 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 30044726 1250 30043476 30043483
    0x2180a09030207050108071b1e08041403010501060e10030b1c02010206100308071509081602040b0409110f0409151b030219080c07020d06062105030304060b010c0f0302 74
    0x21084015002e83c402c0410710f54803c0021500ca280983e41d03541d100172900c026807044107928901902c0e004030706442c08002950903400e4905191003102d0044e511031510248140c50b89600710a0761290741440010004240c0c080015480844129144100c1c0d40c04558251f004140c002c0004e9008801060203032840c041d052002e0000c00e000380c0070350756a40c6d0707403131310440b00c005050000403d025414030483c40840e2034010b0384a80f80411681c00180c00c1c410340c0756025036400940020140c2d140c1041048214100341c060401c2d055030594003484400c0d899921400701100d0610100e000c0ca2a40045800303955403a0031080409030000308a042d0380c10001d65101c00381c00c08400350b101c1e0103103222001c11524440d1084034590751b1240d034044910765803420f04544c03200000d81100903c034800d112900269803440007603d10303131307210b00e00005d08503140c83c17844504402142c50784045101001d0540021038004021203510aa220100040390341070100140c03900034041001a01d0740c003004621604054000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 30045976 1250 30044726 30044741
    0x20702040c21051e1e040605011d04050c0105090a030209100602010b0d0b04032607020c030c01020d05030103021005040e070503090c060a0c0b06060f0c071502160303050702180a 78
    0xe00381d4820b40c507030444a41c0705851041c1d60f242c0e40c0382c01e49070038a01a40c0003c0012500704402011041a040340e00000111004003030b0740c00d46a0320743d510010401c00c00d046692101c0340d56400350a11003480d00d520f400d038403410f40d030901e10705006000031082c0c01507407500d0103400a10350040c8500c0b00c2c2c0c10301d024110354161076030051401661a20300514110702d402e05004401641c030080015541c0e40300e54040f200291000c1515410b0000b900b41850323000710301031070f1611500c0f2560040045031160710825140c50310920030503065401c901d0310030082c1e40d44141181c0c15642c040d162107201c6644420b00701d0303e40c419580000b80c5c00d819a020b00100030750110040d4001d1703801000301c64450310f0803070801c00144255104030001c1810344200c40c000680096030150711540c02001e141c1080004039409085500480d41c8801a0300103090620501011010482a01d0458802004102c4a10804150b407208500001d01481400f017400802c40d5036a00c4400b2040794918807031601030038a11100d5000c0c080c0b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 30047226 1250 30045976 30046007
    0x11107140607020c061603030603060f020a180b0403030503100b041d01051e040e01090203010501170f01020406050909090709020a0305150f01080105120a060608070e010b030f0a0b010201020702040c 87
    0x280070201d080c491000983d01002c4000814091400c900e05441402c0d00a10181c00c605040c0c035844004003040c03080c0b04031030780180c0c0c0140140e81e4004e50100206200e401d02d20034194001c5140041c070038520401c0645083c0c951600302984c0e26190700d01640703011241907024007058880081e001c5030820082d14203001c005c070303c0c59a24090741d03203540c104580c3e452444040c00d80d00f40860580c0801d8a02a000070340303c1c1e142c1c1400015119040e40120b030a580d026004076000130b50380c59109404210401c016101c50075003000850809041c104010300f0342c03284079090791244100002142da014028070002000300180c3d0070455a07008020b1028015100440341107044202d0f1305800c0c0310782d0074494103410080c10165510003483e8200300400c20a042c40f0b460010551180c5c25078100021464030800340034104440040c1101031402c442c1c14105141600a403551801c28002e01106a100c0455150070002542002c500503142d000100d00a000c1c500010f5842410705055040e480c2d08480c2c00c1179280103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 30048476 1250 30047226 30047233
    0x10905101e0509030a080307030b04110306130e0606101404080c0103060503030702090f0a020408030c100c020a0b130f08030f06100306060804060b031e012901050306010c0501110714 80
    0x341d80549640c010003d81d907416401c68040040061410380007150301081c41d0400048129152000c581120070b080854200760f00008140200b41c540a204c164905400c10010b0252940c4c803582640c40340c2c8050429400b400c0002c42d039100a40c001c400098a801c5420780b40e0b91120b0781c500445603614440910b04d0b010910b820300119682c2800300450b000c3c1c54028003481400d0b105d6208a50a0180003014804026400d000104480741c0a000034030030740c41094000e00d000b80400300900700b121110390340c540555015020030300004040140f41580030118640114200b255810100c0607007000c00350003040c04600104004134015098440c2c1c1c0500410f07031f11060780e0707004090150b044401c18019200401c00200c0000d00181c00e50f0002d6070b400c1030280130750314070188507080d2081600c41100001c07041d0351240b0440f0080b9480e09040c074403514036402001d11005000002038030a1001403c003d04100308100300e0300174041c013504201050b0655025440c1e54000d14200454880060703207504c40c0901 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 30049726 1250 30048476 30048527
    0xf060a03112205090606030403080c0d0c020a06050a0e10050601050d0c111006081b0609040203090304140307060f0806010c0b090703050f060106080c0d0b040f0603230d0c0201090510 80
    0x60440b135161107014090b012038a592a907807010b540c2031400800701c1d00313946400c00900901401c01c1c040c100d4680440d40080481407e2440d1007400c0c0e4100400010160340ba208007400081300006440c00040580e100028064941a004036018400c0071521180c09040480701700080da44001004000c911400035200317929009000141901c045110b51802540306402c0c106181200c1d0481c400d503150010403482c07174800711001040903a0000c880e03100f0580c201080401c03528203250300030003210004070007900b00107003009009001c519888642c003042040e9040052016401440c0e080d80c3e50b508050745500c40d141181800f942c494441c041114603004000607022044d000107002410b031140390326401c1e050758800d40310460503040301c840d1064554482072602c000340c03518400c1840c84450719401042103410740c203122a8001d01480d982c030742c00d100b0001140f0300c400086034003000c01e00289000c014614080c00122840034168101075408200e5450354600280c0081d0729a1010a400b01764a0910 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 30050976 1250 30049726 30049729
    0x80702150301060f030c0e120705030115050109170d030902040e12090f01081003110a0e090c011409030d050306190b0c070503120a080a0222030618020f060a03112205 73
    0x40346c0001500d030100d02410541102c916207108840d0308440d41504807034106945000080c2503a0140240381495203030ba0b80c05000b19640010103001801c0c0081803c498440d03000d04003540c60316582002410150755000350303c21035603150000303107802e038001048401060403070381290b48075809800e1940c445d5400314520081c42d40035545180c8620381142c940d5502901d1a00c03130012070940d07507842543c4480014400304102d103944100a01030104000180b00c4100341e88005410b450360306190001c8032000b40304180c02a51300140008009045140036601d07a1103000100f00b0b12051141c0d050b20703c007001240805c0380740500c00a003801c40454412a452541e407241850303240e00c0401c21400c4902e108011542846004894158011652010040c034114050303440c1e00d014509405880000c41400104009028035406035244186031202480000c502550004290240000c0c03080e002d0765000c030b8480d0004d8000e81c0244207000d240180e440d0341c0c3c8030741c5030303038455099020b010000f00d60200440032565 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 30052226 1250 30050976 30050981
    0xa05010f0806040f030c0503030f10060302030c1b10020a05031f0f090209011b030c0212071503090503070b0c0408070803090f010c0507210308060904031407080702150301060f03 78
    0x40380c1c0c00e5000b03440e180d00c440e01c80c401d5540390500c0c1603007403100d1241900f0000702c041008611400e080c0c400740c0d44504003500e0301d02c403550b8940e1100d01094010700038816107859030320444401d80c01030340d2050384418400d50300c1801c0020700cbd06d5802e0354510100e2000c101035000801984200100159a034561284071054818510070b4003d0742401d0448600038000e002e900e500800019405040107a65401091a081d011802e006011000640618803207002c60038040d00d01c02e80343d0b01c03000c00380200d0341c20f0001d0340403800310040005c0205521211283c040c05018021601d400f500034504103032a1800081c450a6540301e48a054642e21030790600241321440402070364002c00000f41401d6020307045500440701c0c88291203007600c03035000310000041da203420290082464068221581652682e0307040c041d11000c401031115001c5c01e604020171001982c80250f240c0e0411002d6450341e140c18250626580318040d16400075042645c103080c108a000400d400745040b2086030b6154481c4801c040c00c201d06 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 30053476 1250 30052226 30052229
    0x2040603150806071d190e0906071d010309060608030301081009030507020609030c030d02100f0b06070303021c0f06030606270513050a0605041406070914010c0501020a080a05010f 79
    0x4a5400c9440030542e07451145040ea64071800c80f880d9812401190310016400f41e03130b40808a542002c00701410001c2c03401c807400c280d1740444000049c00c044d1401c0c41000e050701135a41007090041000c1000c010b1968001d6002420454004c1e008202c02c40c0c803180f48a940b54000e01034414a03200b807400368401074a46d4010481050307030581d280d5080507800d600780000c80d00b080d0720842d0300d4007800405401d80e07102001a50b410000b180c0c000d1280a802404003001c07100e44021009500c0c0c24500b1200302130f01c0d00c1040720010b962610380141c1d5113580c0c030098004c2402e80c049050015080818110b074119880c0c101d402603a004078010002c451b1751b0000008030841410321401030105840e10788028411070f0b4031155002c0c02c400081d054800c07440d564035042c0200c1c0380049452980d10410f00090000e409000741a81030107100074162410207171006801c00140d480780c4107101c1d40b020b0b043c1c100c41c1d2180302c440b070103550700c00025511420f4900020305a120300311900320b6210700d8900002403550640a0120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 30054726 1250 30053476 30053489
    0x602030a0c0f0b0702100501120f170909100e01090203090604030309020303040f091506030b0d140a0c09091103030f0906071a010f0305010c020102030423100501090204060315 77
    0x1440c06140510681d440c1949540c1074030007404080880c0041840503001d148609695406045c0384065078a40800312001038021601c1c031080c01c422100000c551b01e03220980d0580007030240700c040c08000c007101e20b40d10903025125080130301101800400d03489407407164240e40110f541c0300c6403603884d000510b080740000c42e1036024a600440104000c00e001e940b003282c2d4140041c082da490552103403c1c2044040d0326a1208031519503440312070f0101c215485a8034080d1400e4507041c050b00010b030b0f000a83d032054100c00034018510796829444424010031913045410f501440e07130201c2643c0c41303035504020700701c0079025034504111502045503441d001c0100d42444040c22030b003600744040f0034140603d6402c402d60440c0c0180c4040c500745007a01035503d640e802003111303e581c6407805056240c81400d40d100c0810140275680148140400680c5400b0078180840c5070140d92096400c036140003524218a002c280f40c1c00619010000c14103001640050003130f168152003c1c000040460070081c81700707840e80f2850 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 30055976 1250 30054726 30054733
    0x3042105010c2d1b060906020c030c010b04020405030d1b060908030f0a05010509010b0a0905030304080c12010207080403110f0d0c0623040e07140a080a0c030e150c0705030d06030209100602 83
    0x10306503a441540c41caa48140685c800040018980c0e40e224203e038055a0b04001d558070105030b02a1482090240d45548281920158146403502c0f0100c2d543d00300d100403410a20000400322112200c0c882c00d64060305400c80c2e02844a1b140300e0030185003551040c1c541e41c0184400d10005005046140100ca0480381d02a0021156a280050603516038018180340810800300c0b800c0001d00b6a0100041c0001d0500540940320746c0ba401001c0160754454013010002d00d074010703c038a40108041d00c00395000c482c0c00200f000f901a40d4070001904001c1c2c040d150b41e5010702071103101c40a02201c0d0341c7c0042a03402503203c4c000c40d02012040b050142c049645d8482240b00200000e1101141030f940f06ea40115840c180131090101d05641c950082e0031040030400000c2661040100740c240f00c0c0100c00c000903041c01c0802008119180c072a0320307511003c0d1740e400740c448050041410400d44508036984940c02009480c0c4601c4402101c03c040c02c040d120a074841c0343d403080459030340445400060126481500203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 30057226 1250 30055976 30055997
    0x30105010e09071d060c070b0301050901150903080d0e150118060e061207030c060f02010b010c111207050a0305060412020d02100522030305090610060203042105010c2d 74
    0x40026031641352030076401c14401c0c40b11007048401080104090860081c00ca52258140018008451416440000250344500001080c00c0d005460038050303981050449503980400a5207001601500b5840c41e040d104420803154111082021a41600c00c01311081e11151502078050095540c5030080701000303401d1002240881c0340c9803140d00c01201041c03050b02c1003590f40e0b407039210700c5c00c41c160700c81c00c0030540302001c0b9110194207218400140800f400c1518815419854400d010011000920b000f08281c0c149500650801c22000740144001080701580d00c3e22071070511703100c80095408580c0003c00d1240c81c9003050010922000810007070740200002100c4002c510050300e07018006504003224030015044100c0440d4400410500075103001c00c2e01d05109200500c3d129000704601186112203400340011640031040b5400c40b0039a400401c107090080e01110441c0707440e1203000300f0365883c00817480c07407040d00a510103103030715640042d4000c1c40603441005100c8c0c2e102c49208a0014000e00b40d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 30058476 1250 30057226 30057257
    0xb0609011202090a0f030f0c060318060207060605030d02070f050604030206071203020d0906090b070206010302090703020a0e030a030207030201080106050c0d0f0201090209090c031e0606010e0612010902030105010e0907 96
    0x83e00708500010000384802c2d6580000807030049558005484c80491140e0709020701806060040081c1000e140c03c1002d07440c14180b5803040d003003582c8024600d82e0009901d209102c003580022002e13050050503160103024200c400381d9181e06034862040e030000c9070040054245850030035501101d4000c0d0200303140442c2c5039030320154499205810024107500740721000444d4024482c0403211803082000140c034046c03a05000c580410f0017403142d011503018030700500050700c4095000703811030528100540c641d80806070641e41001d403900c2542d010b228200d005800d042e40020303668203c7e4001c0c0c83e0f240080e41c031140c0440d114850040800815845600400101031003424210980f403070a00c00000c1d032022a0780012280354055813066081c0d0711607112000b12b03260501c0301014564000e48030301420305801980a48070174000301000d05010316250341c1d00141c0c0342c0d40c00711109411403252808156031284080402500280a003034001141407481d0315071400c041a503140124030075101c1c003010607040c84 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 30059726 1250 30058476 30058481
    0x1303060c090e040f02090105031f0507090b0705060f0f0106050403020f0105120a06090e0d08040f03090803030f1b09090a090c08010603080304050d020a02180405010204030c0b0d0b06090112 83
    0x100c5100400041074000682d4102c150030b40c60146200344420009121140100070821a040e00054401e80284039a12160241d00d9091401e4208480c000b040c640e540407401e40da070480300d0b80f000c11000c03400612401003140200d021840b424090140340001e0300e80c80011100ca400174020000801c0c401c000610151a05010303480c00c80d54149003441c81d10003042008003403c50180c417550803403915901d00384100240703401240ca5049490000f404200302c000307402403a181d0080c00203401d111000b02c810742854031070b0b140361000c0c0c200304089a0ba00c0c1020740c40032a9000c01140c01613a6441c002d00071000c4500364408417440321100a00d0b0203800d844840101001700501d0f41c0403108c00941000025412000b80140e20056001d1040c0a4036031403d1308020f410801d259a0400454204016a4006945402d019100d00c1a0307801100e003507580d103141ca23a00a04c9079410180481807080000200c0880782001044260f605150911802047c5002c0c41003034095503950741d0104481d01d0803172810241c030781d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 30060976 1250 30059726 30059741
    0xf0305030a020d020714010e01020906040512031204080c07060206160305130507140102100b0a03030804061e0509100c05030109020f071202030a1805030a0204050408070204060f0f0803130306 84
    0x25100149402c182d084010300300c1c2d20001d0b0846d80313440c0100f0220344068081c403a11481c940c0c840c000b5490443d408000031218440e5000b00b9106034102002d42d00d9000080055880010035040c03800e07801d09141c20429a1500040e00003d400d10499501107462440410041c0c080d50f100d452079040070091410039005040000e14084003500c030031480c800030035001c01207040100000c10003803014101c0a000281002244008000c015003801481c01e49034075190198401c0340d80602d424026902c451030503c0140c40032a40b0070302161803210083c000c4407400e500150162000d1400c80c0c102d01c550f00709550a86590325400e101092040c001001440215001412600300d80180c00c1c0c54417241c2d80d40d00c01c5049070080c5081c0140d0010910042d03083e00255410074200741040303101c0710180703800000384d40c2d0041024000d00558980000c942006141070503038800c0c0d80d00820034401c290b21008003014034002407048054010010000041380c01c000700854420103580070324410300c41d01715104c0f5400380048 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 30062226 1250 30060976 30060991
    0xa030207050a0c0f06030605030105090c0919020c030901030507020c01120c05040f1508010503070b0702010f05040503030d09110a03050a08090109180605010315080a14030f0d05100603090f030503 86
    0xc4080e403400041c0e180c0100c40152200c5544c0c00a41403c00c1001001c44d155500300034002da141005000501c0c00c0010b20f40100d42c0100c0d00d202e41031365007407182000000120744490007140082245144014040702030030b51803d007a40c0400040d59002001c80e0307103c02c80c8040c9804550007140001b00e66241d0303084042c2725241ca0030964505a030f40c0c50b40c0c0c2455415644074000842c2541194545030b6405081a80101422002400d0b04e40c100f4880ca5254890104001e0521010b0b11419074114091020390b4001c0800070180c98035950040445406441341c620112441c025211045040b4500300b080d0500341c9400100401807001182c2d0341440740d44c000f80403503050215114000a56011003003003101c070800c0040f4046001850200050103654030404480d81c1440805401e00800c4c0c2c0c0001e003051115005102c29660103e046911070551084259141e0140800200d41003048540c0d00700d40e002d103a4000248200540d694012021642041d00007447d1015031640320300072a211358007454000c0c03130 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 30063476 1250 30062226 30062233
    0x8191a100b070c030c050d21120603121205100501050d0b100207080d050a050306060a031d0705090c1806030a0605030d0f032301050d0606050904060501080d050c030a03020705 77
    0x446080512490b0480030003110183c0602d0014410000441003500c01800103551001403203080d80e48001c0100c0400714919440d5120b40120038003a44110a4800806406a4104242501c0b810145550300348007a56001107a540340c800980901c5c6031161303500c1142132041d03041241d400e00c3d004603629403095560285e02501c81c0d11000141e519503042000c100020f40041444074903050300c440c1032480c0b0b0310100d8148002800940400360300041280c0e030024040340c4550b542c03001c00c0320030360040100300d0015912052081d10140040350005480e81915411a0189929554510b06460034480c80c1e01c03070050ba54607030800c107066051020140d0b8010407102004502d80c4c3c0c907030011a140c96040d855200000f4131236160f01d03c2047c1c040c4034001110a20241034018a4940a0f4005101d20184101c0d40240e2007862032100b44441c9a04c03030000303032078003c16002c81800c02d8180031000d00002c0c044c41c101c500525800124860040003201e40500c50000654100352107648107800075001294251140d00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 30064726 1250 30063476 30063479
    0xf0405090a0905060112030e010e01020a06050106031a0319110114070c09050609090a02010e010314090303040c0b03100306150b0c0d080703061809050f070f08191a10 73
    0x15180d400340c501c64000048009801c6440c1e052080c03074a801a80211005100aa803510210b9130014411103040001e080029400302c414004030315050a00f4000b908040c0740a001190041d4140c0241800080315850f0015a04401d402c1548070400300d004e00c190214420340c0000014a10408040c000b08141898009101c01e00d010584130383c0409030445032000000014400da48003807050b00d4101c80e0030f803030380ca0061816242d5150703117801104029060007104c05232007c942c1e100e43c0000904494001520f40d280c100003148903904c2c2c00c25202180c0c00c0d0110600400c19070002c0043c1c81c810106c400345d0200d064915102e113001029008101c543e840c1e452203012545461000061820410490081c05070014426005103061b001500700010141040403c001c4001982d007048a600c4240744005249251460040c0c90700800d2141c0301594000c030540000d80781c4030355035940202c641e8a000d0388c43c00c41001c0d00040070311068580007800a5090850f0350503a4540d60452035112002041d0404050f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 30065976 1250 30064726 30064729
    0x906040306090204141e1b0a021605010215070804060b090c0306012309061c0c080108010509012706060302060f090a0504020412020603090703080d06030303240b0f0405 74
    0x9600540040d03900ca500d40e107851046080c144500008011004e451201c1802c0c11020301500201483c8108103041c4000b01203001801801c98030201c1c120352180c065642ca000302c0c0c4c06503e070a500668100c4000040e04005055400402e1503400356410394095942030b9101c09083d030b400f11029005550030340c1e03074151038051621451003260007512105411a22860244d00052405401e0f078a4a0500011040300004840e402c2d002e4444140741100e00d03c0c0c0381c103201ca08518107280048038a5001c07a00304001c1009058000c10218140e0341c0340d50081c401c13035981d440035070300343c40c1c7d182c107418103801d00810301c8042102c02591007550244240000b048995032a000100d07141c01c050054041440c00142c004010316250f03040400078002903c040d03081c10321302403103590b0b055400a0042c1c0265400170008124a505220b580082c5902250245c1c440310110081801000c20b070004502207460900b9000b524104540354854141c01041c0c4110018241081c05c20203130444900d1401e40c0c0c10611010425 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 30067226 1250 30065976 30065989
    0x40510030e0c0f010e010309020402071e14011406060307230a0207080c0303030f090f010504060f050703140105060c07080102030412090b070305030105091024020f0d050301030b06010509 82
    0x4800658001c52220382500000d41000a00407001c0c0c45200145400d18099030010441e00907941c007400d0006a0800310b0000c03030041d01c10101d00038440303058800002555040c047c0351109003070181d6040c80100b0002c140d00c1e801c94144992100d507034180e080c0012100d181280003190b003c9100c0c40c100b8030f0540f541c0084149525448441c16007a00080f40d050700465040111074020f1a010008004a024030408283c50348005804020070750211000246091010090237031600f1214008200a1800e420705400405009406580880c100350118031858031a000e0940e484481d02c0415005074a0401001069072144800d6030300750092110010710b40d4402e1000d984035500a10008403010074511005241400c50b803c44400e8060500402c00407035481419241580d100707850b40400d5807148240c1d102030713171807503401000121500c02040404160b040840026000305800700d80075005010400f60312511103150100c0014800d10041011580a245041e0424418140304e490a003002020850 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 30068476 1250 30067226 30067249
    0x61014030703060513060b160204140f0703050a05090309010804050f01150503070902040f0b090a1503020903010b060315010c0204140c0406020c0603010303050409051f270504050706140405 83
    0x46507481d082041135050102d240840d0303640c0d10208100160500f003030000180903a0031142100800f5030340b111308545595002100545034802c1c1080c540c6804010f8940c8010100c4890300082c2c00c00004c42c40d4481d140c004c15001e101000302850800c80c035a03004442d00798004000351094400e00d803035003000803428030407442c090300c3c006c10070301c04141031400349441c1c06002c1d8851043c1500c104401c00140c60704150384015100140d444691300e540580010313001e0150f941214116600c984200c05000d0340550050440c0c030400d034020312183c50b44e4000c0002ca17000c100e501c21404213204031240600c0d072103203c0444c8168070003800000d02ca8843c0d05442d112030300450350090240e000003424841950104000003210300704840c018a15815036400903c0d50180344210200c068030f42c0c000c100060010320240003088504e444201940d035941c050800d140480d1118101c1440689041903102c0b202801024805c03900000100352445c50018201c41a0010420941c0c5004091001080603903400881c0301 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 30069726 1250 30068476 30068491
    0x603080406120b09040506040b070306030804091b0207030210050706020714060414070303020a0210172802040302060403140f100504140d0903060f0b0d0b0f06120606101403 76
    0x81c81920310300c402e101201d0803610924458070300801040001000028240d50241d440707100859141c0341c010b01076028040da50030040101c400480c0100b21281c0325032042c44402410841c5012070075500d00140c0c0c880300d03a4080690001445403030040b03202e01810041017540c0c865440145000006c1d2140900d007207131000b0055203034000f01c0500c0f05200f100094a80c044041d480230301950ba1039a034019540e490700c400c1c003d02031441c1119407000203010340d107200b5a0f41c0040c03507580706070710380285859480445000c4045041c014400c401800c2402c51082d10140ca03409424a482e20741580c85250b4003000c0031524035814030a0b91035500121a081c0300a01300416128000b090f00c5c1058074002c0f12940c000e0b0f0104600c1d50080008240c4164440451011a80c222800081042508450340050046100e0b5a80c221403081300440c1009081808980f081c0011000200b4035161181003005895003240f940c0301c540c0c058000b2801500d846008041c40c03195600300f0401c070040341458842940c20845601 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 30070976 1250 30069726 30069737
    0x40305070501090b030903030a051302031516020c030c04090503070f0803061e100e04060b0c060118090c0306020c010f0609020c01050f07020304030b090a050303010e01090c090e060d03030603080406 87
    0xc0101d540c004001c9006001d070303080c040d070451800300c0100707650b07000046c00c1001003610b400100e42d20b680e551002c0015a074019055501001203020f80c801c070301c4d8040d6203c40c809103129404240a0b071010420703a00044008003c0c10300c0c00052000c00c0040e18a250050f66140400c1041d040045c03111126015124403456683c3d49030b02d420740c2084200d541004d900b1a5007031210310807140310703611001c5080c0c0d680b042d400e140001c200c5800118000780107507080070310340c044001045882c115000a4290480d00f02c3c0d6500c2c814108143c0280087c0d070a0814020034114054505000180e00c03a0007038154011940000940c0300d4900e0f4060080ea01c10790701c04a4250f50000b458100e00d031003130281c1c40d809115484171500609102d00008c0d40e0f803050b03101c054a005510408912418014021013449a4000003166180d507194100c03299142c07000e00c6482892498441d000600c180581440d00c121003e910004280d90b07102818000706140c0c081086040590381c000200020f601d0201a0000d0b083c1d5030b984 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 30072226 1250 30070976 30070979
    0xd02130c0f0f05031003030c0c0b1605060604060501140a021627050709140a180518071802090102031b03090307051210022a01050f0f040b01141504030507 68
    0xd4069060182c4050410808104100b500c0c2c40c2e02e40010102c0344c0c11b1400c5017092205007409000075110381c122401c60400018524520b41c100c21030385003010f001c0c0084c3d4420381c481c02d04020450308144102400306450b02c005d02070881c046030241801c80b02c0c85c01a1420031a800301c0b559204000340c0c020440050005408012241c100203c0889a0a540b01d00700118184a41b014001d1100c07480f03194203040034107141c0155038032201e000b4801050281089180c400f00d41448201030201122040e08032003298085400e50100081d2290485c1c1c0c22002c46503401302201000070181d0301c824845c60651100b00924120124201c2c460440c042400000e15115051a0f04150920109500040c810301c2000c84081201402148145003034110302c01c0143c4c0c0345030855034103140b0306415060300c010560085604441e8141034201910500e08614280f50079a2580c210001440d002c1d80c024042000050041c00070750b440c203040d0b2844034402842d0507050714403c001104241c0c0039030001c40701d0381c000032030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 30073476 1250 30072226 30072257
    0x3040e010e07080a140414070315051506030103031403060109030f03020a170c07051002070308040e04050d08090c0904110d081207020c010c060902060702060408012004140d02130c 79
    0x114113802010011061203d5103420b00e40781c0d40c0741740182000d09002501c8241413000281000600d009541c0400e010b4580e1071840180c1d0000c102c12150a043c4030402d000c0324032540342034411241a01d9041d12040705c041d4001108003001d030001001103040c00039614000c0046014100740b0b4100902c80d6000f40040a06850300c451140119810402816000c1c000c4400d00400812400c054440590b00e0102d1b00030380d108100d10340300507984003520100c800a804100b0401c288101c600c2940203104840d01d00328407410071940984100d330700300c4840e00249290a01e034501280919001802908004201c1c990000020490700c004481201c0001000651001d40d50101d010310f41d1003299800513000c04c04e00040040d02005041d00002c10b665690b0001c01c0c110350303807403040d507012580213040c40b500c2d5519881c04900820310b14041d54511518081c20011032078204040701c051380e02c0d4846808a8041110601c094004071f41000c0780d0181400c40d4500c24541e8a02c10900942460713640d8070360f0610b0259 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 30074726 1250 30073476 30073487
    0x109021225140111070906061101050603031201090911190806090c030d050c011e0c02011a030304090c030207050115030308090a03080c0f0702130204090b09040b07050702010203040e010e07 83
    0x1807079180002100d101002030301156401410210801c2c204094880f01c00c051050800b10580c2004014a18005000c50480c1d4005032480428101000810044c0c40d08410036649010320026151030702d45020052068801c41d0b0002c00c03c82d4850269281c2401540d000190b050800103626000f0004150040000c3c2070200a1a46c1207140358000e4035441507940082a25200360902d40401e0090000f0450103041c001d41c800072007040c030602c00426a03d0050b445402814400011800560805402204989501e1b2022014a10050041d49400d1078408105c0c050400d065003d01415400c1c84143c01052007030160a851440c003000100f690380c10361401501480001d89074001e07603070041e0111070000342c205000300c2d0441185110f5680b00c0c0f4072100d94040714441c10340c000390401d05611801140300d00c00c1d005041070b98850002400003203040d806200300f01c80c0898000e0b04401c0b005e0003149007240103800170f00c072590061042ea45803580392180360301f424400780d000302c03002c1c1c0d20b8008000703a00c1e600a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 30075976 1250 30074726 30074773
    0xc0c0c010305010b070b0402010219050105010f08010b100f0e06160201020d0f0807030b0a03021210060b0702010210240b07020102060601030209011d01030f06060201090606060203041802030901090212 88
    0x900707007007000b94102450301c08140120403004150500140208040da03000b0400c3c5150341585d00d02c410446c58030391406901800e4288a0403000b080d242c4800704000d041070007404121400603011020b207041411040302c0014003200c0300400e1100e051100071858480c0382c01082c5440e45250004101240c500c00240b0f0501802c07450410012a480710401580d8081000c5812000b240b03804514000f001002403841d2040b6400203520015020a52825081c0420f0780c003002010908100070b0240e035030b4413140041c45040002401070b0821080250402801d80c003c1c0c2d81c3c10034a56440d4002040c42807032040140ca5500804c901d100f01003100e008543e070403c04960700410a29080d4100340ca0b402c00a403c8107804040d5018100c5c1441c0c642c5483d0f4400e5010801c00c404100b010b21810307650f00c3c0040d000702200c0d4415514581841000300d000c030b0000044508643c40039000031440d840c0240200c000f0b400160243c0c8095484501030800359440101041d01003009101070501c8447c1c65403121001e2401c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 30077226 1250 30075976 30075979
    0x5220305091804230c040e060a1103010b1c0f020a02060406051b0f07020d080a090609050d110105030c0d0603030801140a05060324190614030c0406030e03120c0c0c 72
    0x2204200f00004514050340707560f01801d0840796101e0101c104034a410002205c48154004d07140400d800304c5600002421030190000700c908000129008202d006140b00c24081c4480c401010451492503c0b08011012080307a034000c0b0000c4e80f0304074100f0703010580e0301c1140402c0040e0701001c01d11090004508c01c49400c0b05c45403038907008040d61007044164034000d07070a03a00c1c00b21001090500c01d545030703903540c0c8a05a82c490030183d5150b54181002d0401c0c66076001e0305000404c582c80c0414507040c00b540344541a900001d05280807070b0020300440c0d01d80e000800050500d0030610605035010b02034001e9034051413082d1a0800d9560610040d040740d9211204124880e4142820800030340c2c8528040302d4004103500e9540c2e0120381e0006000d0070f03005a0000441d0400700d42d02c80c03a508403100d417000805071141070f03884907901c100e90b403507030180ea02007500c908000c20b80411081107014000d0b031182c032460a41c0340c262801d21038210810024494111103008800c01c00184080014000f4007006150080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 30078476 1250 30077226 30077269
    0xb09040b090d09030f0303020304030203130801050106020f01050f0117030d060605041406070308150d0f060b12150606070606031202061801150512010908030106030e0c04050103080306040522030509 87
    0x4d51380314820740d007020b420060103140c0d002001c1824107100b4021074502521b2000b600c1490b81e80c900751507008200920a10005010b4040b240b003000034103010310b40c00350410540c5002d407a401c016846803e04889a1007224607c0b0820940f8450005809600014841a201c49440e0391130480c0030160342e02500000351203000c04220640c0025040f028143d00242c29003000701005445002123104107001000c080c4c1041e0320211170344100002d40d00003049840080e03400c480d01141c40d103845030740c940040a80201310b040c442c0c000b45160030100003610311540111000311301680d0340c0d2030311881001014544001a040355007004410340320390500c03192802c03881c4000c02841054041880c04c62806024461091403145d00c4604190300075000055400e4010754140da80356500c0401800a10070a601a003690140d0742080c4464a440d10a15040f25000302c8002c0c074598a1404120007081c00400e00341701c1c24104030f010014003490300d005502440c402e8541035030300e480c5202003080c4240d82c4252580c0000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 30079726 1250 30078476 30078479
    0x1e040f0509061e03030c0304180605040608030706090203100c0305100803041503021305031603030e040c08040f0c23010201060b03090a020d05070302030102130e10061e030b09040b090d09 82
    0x4a4854910607015980f044410075800d150300000d09511030725502404601c80170070040baa0200701c60340a140c02c5240c1c101000107540c0c1d0400d0200703486c5a4800c1400980040c00540301055107604102680d503c018180e54048010461034412540300300c061a00090b900c01c1007103440c41d06403c4580180008034015400d080c07030104208101440d00c10784400301500400c031012601d001d11024030240c4001000e850440f4440041c049140070300c0d10056002400c60350a03c0720500f0940304070b540c0c00201da03444010300e641d0398031401d11000c0009021905101250740009602441540c1801440142d07400306a0b07002c0c28100090940d41950841c50f4903910400c01e0003541080000d82800003a815074441c4070030196800c007181850344607403000e50554000210314034800d2403d08800159464810445403a0316008900d502e603030118010f036804103111900e00b1480c4440078103a04121141d031b2901103020742c1440c021440a5a0940d01124444012828040250001c1c4688c1005c1c0d000c0f07140c005481c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 30080976 1250 30079726 30079729
    0x40506030c0f010e060406020f060717010e0705090307030311120301080a02010c0309030503030109050601140909010306020306041d030d181203020d06080a0302070509010503030711040b04021e040f050906 90
    0x10031403414080c0c428a0a0034031801c0070f90144500341c0755140002c214680b5180c0d07541010303495030240ca0a81c03480d8010080007901e03e80c003035100d200a45105141c802c105a08040da2010a0f140103400601400402d009020341f42d80e080081c0e9029520940d01c5951038200c401c0f00328030702046000301801c94081400144007540c40010307103c1c117898091030102008095418240c500b1801c035003003d04030740000000814105415000f20b4043d400a0b038840301c00b4144821060b2a43c000ea00125600c0181c0307200410204000d82c01554004500602c0003400c03a8201000c101c03014001c00100134640c002040e440e00c030150f18441e02c03203c24483c2e6040724050000d0f9640720b860400e000070310300c10f143d40800e000741703544040da0050b0050a4800102ea095400e10304000e95144910b01c100d520030004a0004a003905020054903111584144041d00794849182008003401c0c0c0390744030701c2c6c0081d8203010744451032880c000c0e4000500c0610240c50382d107904168200e42d040e03030550003190280d46c0325818041c46 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 30082226 1250 30080976 30080983
    0x5030307020603060402090d051501060c03170603010e03121005060405010c0303050c070c060503090d0315051507050105011d0f0105060d0509010b060301080102120105040c091802040b040906030b0604050603 91
    0x21035604482c0c80380c3da542c030038000400901032888125000419000c0e00d404205000a402e0800c074103655034200c0e281c0e41e50f00102c0300d20802c2c0ca001030000386100c070720005007021501d0280c2c100c1001000498182e070405081071442e004880c00010000c4001c061103031488600042c000502802c0c0d0b801482e041c10600040d10107207001000170704150359003001480c610041c100780c0d40d0499000d0322122419966180042c0160019125034403180211b01e015014640030b0700c1013000280e56440c0a0040520b07150030048460911031000c3c205070030801c40e0f0300003e802032040314042c114000c3d00710703202c1030004000741e56020020088071030403842c7c034010320040e80c43d10159420281d0301e1030049440e9540720b4045001d01201218035810940c0440082001001034015200200c16942030b205180e076a00100000e94004e081180003180c282403052000280101449602e4542414058541a0340e800841603e9000c1e5000321049a603400050040120b50021160407403c00c403400e004608040700007986 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 30083476 1250 30082226 30082237
    0x6030c09160908030301030807140604110f040e0f0303190b0102060609040f02030607050a030c0c0c0501050a11030712080903090108010b18030a050a1e0b01090203060607080a17060109050303 84
    0x804210001c001440500c14402d070406089000e0549860b96035070300c0c0210054200c88011618043c0c620002c8600340b4001402034804c2c0c0e08428202e48410400c000d2050040b02d4581450700140c6803260b419050100300314090010070f004006568900e000c0c050b19100c50100038036109600e08220030f010b02030303900003407454004508aa03000105d450310f107458100405031810094043c007a000c200700700a0b8209000c0c0c0751420031510148a1400c80b49030495400f480c1c001c0050220304074403404e00095100742d01800380341a80741040040034082c081214510342149200300d0307550812010043c0c1c01540b20311065041004080214200802e000c0007810038803050040c00c110610204404000c000d008400d00703520318000d01074414050386420038689985144106407284c014144599101507d0b41c21500515a0840c07003d080903400d04501d60007a51025210303551004080c064100460443c0e401003102c1d04c070540301c0000c04e4480c2510710303030700c0003000b0481418003504c42c1341000b8a8601104580703 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 30084726 1250 30083476 30083491
    0x2070e0a050c04030506090a1407060507060504020402070b0108030403060606170402010e0109120602090a0b030f0411010216060503100b03010b09220207121101090312090c09050c0a030506030c09 86
    0x40341c0d0340d007500b1208a03014507800601180720314400e1202c207074004503100426902401c51304440701c0c0610010b903035441041c0b06540c00524104100300100344c03968095a0010310042c00075103040400d4480c080b481c80280c0040145400016040040000d14480c55004017114107180321212089840e45544080040019051044098082c00d5982c0b04908101c041d00d0b0b403000c3e458007544203081100c0250481c08005005060203076010400d46a01d03001d50744100d541080c0e507035075903449039203000342c402162500e1415803142e006080a048460910031025200c66500c01e9200d103015600d464010a0507441006490b8080005024900c444421601e12810941d684c0810f1b2401c1480441d9802c04207400c400a43d10110f01c3c80d0400c8814241e078002241d03a03940f100c1919040c441102d0894026450007004030b102e50000004404850b0803416240340111411028107030740c0c00c2180309841e42110154038480002450080c4242c0520840e5080070056008158440442e00880c000e0b410140506 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 30085976 1250 30084726 30084731
    0x606090103120309120504050f03060402030d05070c0503060403030e06071107090207170309011e060b0306040504060902042c06090304030803062701141c02040e0a020d0c05010e0102070e0a 83
    0x2c00700d0303009030444c03055107510031044050110309400080641d0000c2c02903d100e1003c03204072540e0340c640081c0a5003e04d40080140003840713190704007900c031588040307005c0350200740c900000182941c00b4020300784900d000c1d4401182484c9114821428a40000d025009000e51600d194015050002e4a03c0907564020b50059550040303051003034920b85c00351030300920042c002003003080014041d0031940410403040503c2c815005101d154405440c940d00502003000c1c1d0600c0005c500d440c1c5508400d4003d4082e17200001c60b0440d40d00898162100c5c007013034801021484246c40449095800002019054207018104074188081c503261244154480604012800300c045130700f9942e2580c0720440c291035014100140b0100340e001d454201400d1240c442800c0110322800c1d41d901b02032291280e0710808032002c880d84a030b25400c000091400f00259045481540a14401030b1070765104803040c0750140040440c2c4903e0000010544000508a00d0442d0440ca008200740940c0d2a80c140e0071441000c4003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 30087226 1250 30085976 30086003
    0x403090501181a09040507020d08040201050a0908160519060206060607060b03030409060312050703440a0b060f1b120307051b010b130f0212070908010b01020606090103 74
    0x404207007840c50b0085016110039111914070a4110f0005200d610360076034050001d40e40d410f000381d0f00d500c005203114010400040000d00158420070042241d8109410720b0b1400307d48480c8003a1500d050718141d405003c06142c000d0005203841d1040ba007a03c421107030308845107400c1050003902c401000c0c041c24060701010401504220058001d440c0303806018040342d84450b07940030b010010380700303600c030a40c0d00c20507411411030322a1040b41214803075030705902d81d140f19014507248180041d1505980108076034105902c0e90344181e00c5100003c402844180c190440c1c01d1510640d0111000c000d46075100700f03c02c10214204000c1d40c41946c21002030300310080da40070801d29409061554400d2520240c42000003004100740d085400740030181c211046080001c20703450204e41c00c0b1864031107801d80c0007110b03144607900d038065074000c0281006800d0016003840d80703102034801d800c00141c4000010510440d802d0150070f00911688446010900c001c010b203080090104003448018000a0f1000444420 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 30088476 1250 30087226 30087257
    0xb060402121906090b060703050c10020a050a0219020d021201060308030c030f07090305030d0c020106090e01050105011205040b01060c030e090f09070603050432070602030403060f02030403090501 86
    0x6440310155100d440c0082494000c4029106034084400b40e580c051500001149550083c401e44070040005803000b4580121910151400e0b00321078a142c1e83da200341e90048406804a0014251001c120b80f00c0c40d443c1c20055130083d040201001c8050a903503050819000075903285500d80c000550155544068544a40021409044a070f0070180c4005800000c3c841c2d007140d20402140b160104103c807500715101d44ca0219404401c0b4400074166030f105201c00051408150b00041106015000000394159190b40c05004c0c1d800600001c0301c203035900c4004102c5940c0100203251b1000d00d82c401002245415a43c220115006019140400210b400500201400340c80c160414500040c070184461400f42400756031050304a400c1c02c803a0062000c005207040c0130780100c5016540c0191010b8100e204802c0040001c40c91111f640c8132800c5403002c60722605014045032001d000c8560103560703980d044d070510f00d060700c14401100c1040c501c10003c20001c81d40c40103500c2d003515001d281244101c1c4c801035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 30089726 1250 30088476 30088481
    0x110102131a0c03070308040b070809060606130302030601090501030c061e05090406050d06060f120c0e06030a021201020d1107020d03030b130c0809060702010501060207060c0219080f1204050604030b0604 89
    0x1442c4070750b11000409005150b04280740e24130030361180062404a540d00102261401d030152101200365000c0310101e605e501d0004060400001c0a00124a540b59a80c0010380b50000a920030203000796104010b00501c030120108502410190034414882540c100d40c4848424030642d4800070460042488901950386030071203402054020a000c014031064100000180803d00c20100000d10880c000110003a082d0302c1080100e4006420854181c40c10a603001006001409580e140c01629014030040e80da9003001114803114800058440c50300326000f500700c2d45801c0050382e08100500403040140e43d8010002842a03051401150798482d00005c00c140700b02c1c003100b40417042d0604a04030303041540b10010030300c9072410000319096a1102201030303003211303070a000340c03170050300718000501507070b0f000e0300c41806018400390000c0da12642c1310500c1c0400c00300c0c0d600500c10716000b05c0741200d05401c0812914000205c403004407840c00d4a05030000304644501d00c001000c0f6a6028001055555030740e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 30090976 1250 30089726 30089737
    0x150b0402040b0a0201061a1c180503030f010b04030803070509010c02151c050f010605160c09140f19090503070b040303091502030f0609061c12110102131a 68
    0x1900a645694880c0c0490141d9080328420400562800d07500003020900048421100144115400d00d4907140d07000d40d2104182101d0401e0708180c0b5007100c189060056424211200c0c0100b018503240d00b0180014140361030306900017064103c09201c1440032810340411660000002d042c4035556042a40059602880c60040694401354896134896010f541d10000c26440c040b04000d0301e001212610b10308202d650664003035426103034140051000c180a10003c1c42501754009102148409581c1c0324803001c1030a80144252036140c400e8842000251207032243c000d64244400121482d010030159000e02d00826104100c9803521612424440240b04440b082034001d8900c0c13840389080d06015000c1c144035002241c0003003003000102103240981c400d46c0d00501055550014507101c18003088400500608802c0c1d10005020000800c680d21445600480348503034402000c240703003090050440000000512196401000040112081540c0d40400c1c0c440da24911040041c1b07102c000d1005001d40d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 30092226 1250 30090976 30090979
    0x6080a09050f0d1d0a03080d02030c040b07050d03050105100c0b070507051006080c03070e0106050f0c010203040309080d0e013c020606040f0b01020613060b0604030f051504050307150b 81
    0x155150b260603d5400444802001d200181002c00c5001c60401d00c8814042444040d24111007170201c0c440740314054000f141c20a070447c0c0740728101034807102220101d40c8280400c80d076660240221080d0580c15018250040c0811110454029100c07030300a010780d80b00c808000d00c0300040d0340014a20034003a03c1a246110740020232100304c2c485804010380200000d010300219845044211501860000b6004090b5010385403c140035034a010780540300c42d041081d00c190190300910102000a40901c00345205900030307500d0288107031500f42224208818030b8500c400b001040c50458410780d802c04c5018010f2681e8400012450304440c845091403440c510005030107508031080740300c44503030009070280142c41c211713010409841d100350080d00700e03540111003a001d80c21880002c0e14503060611480407044c05802c0220f0301e411148009402070740325400c100e810607101044c0e40c091000c10001c6481c5040500b407101520f04183d140c0903902c1c060308500038248200918141d03c00c074a580c0114410010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 30093476 1250 30092226 30092233
    0x130504060204080f010603110f1503060616031805062106030c0a121b030c0504051504020a020a060506060a020606060307031b0c030215060f0609010201110a03060807060906080a09050f 81
    0x20b050207030f020b0b001620081c8c4090140b6800300c1007030314081442244042c1c0061404c0c01c2181c005901c00e01070b03000100215800700c17082c070909803004a00c401f0381103102c1c4282e0340d0310704801e01452454580c04e402e811090140209020b0001500b08140703c0c2d080d0303c101c0991941c1c0329a00da03400a45051107100070704c1d400c1b550400300052401c0800c00c0101c0082c2c815068012004449003681d481800144409041d040032510100f0003401d184d40200d40003002e50002c004101c04410210741aa44048008401a030005028505003c02803003100c0d000381d070031103140740b400d01342010023551400003074011481804004042020355000303500c200c104507070b25825141031100350140a0722086c00050f083c0d025002c5c4801001c13421541d00c4043d0f00c202c10040081c1d201a00e010207001d400d0b04880c1184d41036650f03803d02d048401c62200c2c00340a4041759994041402800d1002450400441c0d501c0001408118001408a550426542036001055200015018145040052034103840780d000a01502 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 30094726 1250 30093476 30093493
    0x50903120c03070c0b090603061005190f020111040b040905180a050d080601020c01021b0a0b180a060203030114040b1f020604110102070609031401020913020901031a13050406020408 80
    0xca0102c00303011098000d911944035590359408000b610321460070780e981c2c01042080015917901e407034140425010483e1400e42c0c14281c1808e191041c0385007107e07000c3c011074040c20360900b4140c2e0900464440c2c100c0700c070155040c20300d403010b122028010780c040c0103803017512400001c0b1002d203505180d0700e40d00380e0701040f1501125642442a04e07200114004800a110302000501039400056101e40d040e03030680c0200500e4141242e80300d81c5d000354811003548802003503400991207000c0009020b030a48200c9601c19030b41034000802c40d14840035400308040d07400a00040010003841c0000383c00804041d10003081000324030000400d4075071f130528881205c080f040c2030b5110b100d1f40025214401e40c4a2011800e12001c0c41c801a680c0e00d4040c490080001c040102c2840010710094400c6081441710002604004a000000b401030203d11440e208690f0301083c0c0d04074540e4180104150200300c000342904140c45000414003c2d01440c20b0002425110000310341000017603070485004047c001c041c1d40303194 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 30095976 1250 30094726 30094747
    0x105040b0d0e030a0903030201110403050a060504051609060e0603010c020601122103090201030609020405030a11060c120304051005010f050d031e050c120a050313032105010905090d02070605090312 87
    0x41071500051f40103600c1c050700b075044100c2ea1000c440035a90400024100c072281540d4000103408001c10440303141c011b4040c04544103049460740c81c050004400702042090400072203141440004142c10f110b68141855002e420303802144090560303881c580c158440005904100c05a09004038182d5010080b081c08031890540c907a11030702e0210b200742e8003400481d648198080a90103503008165064004480c518001410741080401c42d0300c2c0070f0101414403e04408150900140d0f9000b008004000010001000014800c54642c503070a05800c02883d41081200ea0030300703a5034020540101008001b950a050240901c40580302c0281607400142004520040041d000130f4100040c1e4440c0f060f440803c45c060310f0a40b003031070440f42d5480b415650756101c410010442c070030044c4c062102902d100514030580c04401c00c11014803d00202e0700354034000b42e040071900020a00b030f030384c0d070440212404c80070360124803907080302d4840c0781c000e450b41600000a420a12b4200d14401a07150015240260 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 30097226 1250 30095976 30095987
    0x70b070809060a1b05071a0403090e0f1003030f021e011d030c03160f0f031e18090e0304080a060902030705180f220302010501090b0f0105040b0d0e030a 67
    0x1a445001038611a49500c80f4610940d1442280b90588001556240c0c19880c85400a0014140507001c0f2481082142c04284402c00040e40c065000070001c18052250140507a18260088584910107180b0318104100d4150004035000090401141c002140c031903d01c00c000301800ea841014411009041c407030402e038000d00143d003035001c0e02c1b813070f00842c105c000501005039040a4000001303189012121401071700030480c236032001c541d000c5480742e051010500d04002d00d001a4441e031a0214000b98280ca2003c5101c40316010070204500b551a80c5118581000401c1c2203d0356003178080b0320041318003101e80c1036004a401c05015481a111b0003001e105d0075801c002d0005000380d040c2e4003c5500c0f8818883c0f50411541d501c54000c00380e10205203008542581640d110040c4d0b582c1403a0050700c00000d992401c9c08030030a80050b9100d038018001100d403407280a150f0341040b0f0344111a10300400c006081d500980c880ca403007961000c200c81c80442c1140d0020000510382c08192680e8008801e0090003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 30098476 1250 30097226 30097231
    0xc151d0601080a0308010e06010915020604030e041e15211b151b0f0b0604050105040506030d03020309240a0606031e0209010212130303030b10080714070b0708 70
    0x225849400d00004040c10046800b282480d00743e60382d491241c0c01d00002d00304010014106604004401c14001003c6e001844105007285143c0c2c05003c040c24071781001420300c140c030000c0034802c9143c01c0108500c60070101040300c00f594143c1c00414084103400150350380c1c820507403228070b0040502603201c030805d001001d00140ca621688109031030b9220800380b507040070654000d0400281004003101c04090241d103501e1038034605114407088019241d40c401700c01c04031501c02190303000e500c042440f29920300303030240c580542015541084549800b10000b907950003200700480c14568000045640c04a0500a20200951007034492814200d24200d0729180a01101c0050101b45030140100b0046d01c01d024400740d441c2d261398503412800c0c40a6050340254410701d0b402d0306501c960150031540750120001303007203203c08044401c1c6451345542005030507500c40f82c00d603074800c00005a0f00000c07030350410f10103a0070100707515001441c298980e500045510802d94003a240307901d10710800c035403154081015072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 30099726 1250 30098476 30098531
    0x106060305160e0904080d020a05030105040e01110301090209030a02030a05030702180601090501030e010f06030303060602070b070f08030601050706020f0910020a23100f0501050a0609080d0c15 85
    0x15954000b80e903000380100844610004403903228000f0381e07113004003409400c64081d4515a00d04604c4a129030200e9001c0c1c551803001c00d90210040203289820b1241e05540c8103d90002e1080000083c010302007840b05005100131590b010504140c240c13402c2141d110840e6019085448541030340c1403480d03503034110010803407089002c60860716000d8080201c490243d041030710f0b0400a07608000041d0050701c000c070041035441d035845148074800c081c0b500850300118020745001400c142803280003428034030541c02c421010507081000d100090190f20781c200c0f8490304040015100c0d212400120340c00e226903103000e0305460012902c61f16004030345c8010304032784008484a42500e80401f400340d8403401c1400001e0314a0b0281d0a2040c107040d20415071040300300406090b602512003009120048032044034800100e981e4a0f80180503e0a154030584080e00700380c2440640300789042406643c41c5c49100c004c5c0c0800c00d1401c2d8042c200514580201c0503424107580a010040c03000200118082620b81c01c81c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 30100976 1250 30099726 30099731
    0x609050a090b10080c090604090204150e0a0608060109020a050403122d05120702120403140c03010203090307110a030b0a0b010201050f100e100803030408030702060721052701060603 80
    0x145001050f0320001c003103030804005403580c84030709000c000c401c520080450742c206481c0c515800059549110b6140c020145000d402151410810780070070f4000c0c0201141152840c0900030720050ba40003890a044034000400507a48106040e0100c0d241c0c02140c6c80203008041e00c1110329405500301403450494612202c2c503a41d00da00580081460000c4886840089001001401d081c91920058075500c8070441c01241c40ea081c0500180352280d200354001c2c0d03018807401c0201c200c901d20902c9200324400085000b50301394281824041c0d107038804c1800c0200a00f10003145e2049c1501c410b200d1000540d080131500e0503900d0810044006000300036111030040d4a070500003801c040080c110517014031100d9211190290900c41d955002540140005000000c3e84400051001041008512843c03141c20040c0d12130600d600f010385004005029142804003030801c0c0c0b41c0f200b401080e1105141104140400c0da41c4131104900e50754101c01c0007580e0310741100c128142c02c90605402050450b4940d5404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 30102226 1250 30100976 30100981
    0xb0712030506010503060103020306041401090c081003050c101206030807110d1e060b0904050a021002060c030703050a090c060203040f090b030c0103090203030d050f1009020a140a02010609050a090b 87
    0x8608070750003251100d020440130700105055520950140d5403011000d40009246524404141c0c00e20381301744d201507111130b25298003400d4280d0008461b500062200c2d1411142e0f070660303480c103440b01d0070104078600500030441070b000c159201d0440580e46880c602c2003080300548070b06060395280d001d4442075801c01034426031105a41400202610025000004560001070b8510f8070f500040a20105840070758541c0c54401c45a07030ba083d1100d02403446a001844000818070501580180c20314000d020b541041e401c104540d070045048aa1040103072a00080680d07444c8604001803c00d01405840c900066001140e45500000103000380c80d250400000031075500e503140001c1e00ca40c113120541580200e100076407194045d40140c40d00d00e20040641c6d0806c444140f4400441c0d0302240e00000d82c030340f5001400359002c401c0000c1005049810410751611a102401030103603180c40001600d4068001040c1100610070360240018100c0c01d02c00b40009d08001c1401c2e405000c0c45601038032102c000002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 30103476 1250 30102226 30102263
    0x604091b2604030e191e050a0e0705070c1203020601030b01080d05040504020310120501200a05090d0809120c03010506040608121c05040609030e01030c0c02090c040f0b07 75
    0x3074405403400054200325103561140e03811203010a1061026800c0704003000034042d101245c010240c098079500c248039014020b40021171003034109030303800540114004030050100740c00074108103511094500f040307961030000345418281d040d220350104040c2d22000d48610b08150740890200d04803402003440c951583d1700d8608c01d541320030706880c50714003003070702008100581c0c05c00e5005158041d0f4501603403188150b403940030b442c02500304034040b1480d0355503007d0583c051032000c2222040014030000c03981040020000546140f041c90f0042d440b90100c01c4403803040058410489080903409014420007560791442c02c2c0d900c0b4500203065102e1b5003040c002a1107401c05105940c1140c580030001c00707030340100e042c04a030309034803d2405004400c201d0781000130740e0b0f00502030240610b2240400040b080c1290800030821039240e001c1c1c0e41010304010300d4080700b42d40000800c1800c0d804860ba00100d0f00c440811710168407030341c1e100c1c0c0800340d8034007000500000320002504031a406481100c42031141881d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 30104726 1250 30103476 30103517
    0x7082107030e07260616020105010807050d020409020d05010c0504060e03060f19110f070203011505061b010e07030b0601020d0807170c0c0a060c031104030507030f020604091b 77
    0x480b40c07001a405260f0801103404501400500d0035402e01c66800d4090007001c416040c840b044078507040d240c1d48500044155076091103150300400541c0c01402241c1d003010001600340d001c59401a10841d29110b43d0819540c443c41e40910456003c0020082140c000c02d01a103140c0107485044041107a4501020960501188030344c03055460305040c1e0007594505005030881e103401102082095500d0740b80c68600c80c2d100d0000e2503807084c002816030322401248105400e44007840180168007090120400a84c0c851000742d5041d40d0307802c03159404d1040602a0640180740d11401c50002d441010000000d0001a806150041d070007a4242c44903025000c0003651460001e031404000640300019034401d0002001140303070000b003e0908940380402c925426803820315401c2003030710070a80d5400141030050f014400c1075426003d42c00d40c2400c107032450f11801d80b1a946440090030300a1000194400c5507070301c5045a010301032040d0100300b041406410707055404003144c3d01c900480c04014051802c3d00880 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 30105976 1250 30104726 30104741
    0x4110c07090b240a110f070306060306050a09020f101b08030f070203030f060f120d0e030106120b0c31060f081510030204231c12050f0708210703 64
    0x80d0f9607460014496003c4440860890105116004050a0014460040c030604006500807a40480d5041c1103083c81001c1322070103082c01c40704500e40b0001b03000603280c1d64000c1d00300383c2084440510901104030240c9011410740c3d02498564030042c1c113442081010005540201e0701c210403050980d03102c4030260b03640d12080c1c5e010034036000b07988001001072604101070b224110000d0104d400c0a11400c00c0d80d0715107080e0101321004a140c1400f0710700c483c107091003800e00a080d410005a1510001d403100c2c288803501504a110342080003620346000115810012f8400d800c41c0400520301c0145e14110007444040c2c0110400030b0f1f11240d0b1405c1d0184526007150103481402c070000c080da044c407000c003c814280502c50409064003400002210440310305103441460745405655000d0400304c0400014003d41001160f40425240846000c02c941d81e000905d2858181090b9a448030811581c5415014010004044100c0010070005030325280c64204208900502000e0217034480366015410365604 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 30107226 1250 30105976 30106039
    0x3060501051504090209010509040504060e0d050306130b0d12090303020610030206030c090f040e010c11010c021e0304030507120201030b0409030509040f020403020d030c050d020304060206010504110c07090b 91
    0x9110074403109405600620081b50141000391078608540701040a42e00300b120b003601c06540d513007041c0b025281c09001da902d040c4010701d00f191a6283c44800202e0001e030100b0441c100d030b41d660000000944491580c544220f420200820340603d24510042450340140001c500600440000ca40e4000360480a5002d0701c0e4010301107801d507a194103103803820382c01490919a0000040004a81c030b03461707a1040e550076509023000421980755003580a0158080401c400d1556898501751503140340d40400d108c285068511103102c000207000c1c40052850155402c003030300d6070103111400200070004442c040d149620030b032002e02c801070341c0030204007ca404c00c00e005404640c04020b1030701c00e4030746a0b000a882d041c0034400141043e0312500400c4240f14444011030105001302c00d0300d000d2020401000b625009640300843c038150038140025110b00b018400c541c010b40d1107030204c8000c51040016210454824811110041d6403030200300d01500803843c0c282e000d84810180740c44612142410340a4082c030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 30108476 1250 30107226 30107269
    0xc0310150e04020904090f0c0f06080c0a0e13050c030a0c050c0a02090606070f0b01030501051807030b180d020c0a0504181509020303041508070305070818030409020703090306050105 80
    0x1001d0501001c3e501070700003513600c9941d91a034a400140121a039070401c500840f06034000a003042e040c4852124240c0081090001402c100102025402c089940152651600b24140c0d035040002c03414450034dc40400e8a41c60504042007001000940a144126070442c818080581040c10a0b1480d00c6078486074400e81e04400c001070058145601c440e5000500908103514100c0c0c2500c03900c3c2e0038880e00c07904484401c0c042004101b80306003400381c16082080c03403039940c01c87c02c40e101c0740d10b0741c0d01d045203c0144030b8040000065045204466084001d5010343d081c2c94a031211504000d440f9428039880c18880d41044001081c58103080c41041018910070307640c984c3d00380303003278450460408ea2030071202c0d0019110364078180142c80c04e0014000824105030011030031905104003420b0510018058001c15103001c0030010140c1d4000b4890350080b031000164074030801c0040c0083d040d4866900500700d2280002601820113a01c0f0b5614401c6074015481009a0b90301c520400910341a240040c1100c0c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 30109726 1250 30108476 30108497
    0xd0b010f020303070311190903050c01030b100c030201020d0e010e0d11030901080903040306090b1b0703050a1d040606022109010c17040302100c060f0b060d1a0303030c031015 77
    0x14001d1b0302203103c10b010030f140d03541821050801c1d02c40362030303996105400041e8400d01c01c004001c410402c0b03890f104002d0030240942c25075440400c440010800c600d01c1000142ca0442040c07600039412104030b0b0040400a110085150380c105010b41b01c81102a0313054801c5560440031284281a01c0000024180145240003070740401120300e0f0f0b4020b0012090b501080000000180d0713244a443e6040740301e058000403518014005200800c04481841182c2104021f001c0000b80d03c04101c410000560406115640c20110316120302d204800c0e140e07402900c1c104e07003c10070350b030001007480904c0541a07840741200300c007144000c22401a04003250125005002d200c0005000c50102d0101ea14040c0300d040c1440e035641c00040e459004051042c001c1407089142900b170110700e0003030b44001101c0107000e105000750b180109109110b488217034001a9511028241c0d0304503c40100706030b071800141203c0d01d07400c05e1900441540d0040d0f407141d0f49500c25060014020500502e01d0010318019100d924480 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 30110976 1250 30109726 30109741
    0x90f0612010903230d0c180801090201020a0201050d02090a08010e010c0905030607081315020715140c0904020408010f020306030c030708060703020f090d030905031002091e03150c0d0b010f020303 86
    0x826135403a0810b859814001c007085d80b41103105420303090405039038112041c0700c015901d1712003442c4e80c1c200440c42e90401c52800c0250341c002078090a15542803a00540c0c4a0304017404900900491a80359401424003400140c04803054000108420484008121001d91502d041d00d8030072191043c96010b0f00200001a00c0030700548000354400b651000d0040124029aa03e04e9004c001359411045668040707401c00a00c240003070340b1320800c003d42d0020424091102d500045c8404018840161941c0002d605030359034890b034041d1001400444000e02050842204002c00b0f5041141c1842c0240701d00e040c820414a40090320804881c5c03284c0103014661100d00d400c801039480f004481a1600f0100082140307500d44400c00807065001e0340c0d070280b09c075007400101410803058050301c0e45c0c0b01d030040c00315428a40c0d074100c1040850301c08210090419524a02090411409440001c0025030040420000440c0080208144d00d480340b800c00500c00742c40019955803071030980d403c006034070500004010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 30112226 1250 30110976 30111017
    0x6060506130510020f030a090305060703020403080328181a010302060315010504051005030a0515030d030f060308070305031503120f0304020d290f010b0a0f0905090f0612010903 78
    0x100203e92050b0341140301211005407460b17020151210000b40a00e60400c00c3c05424070540750058451700e0250704d0301d403541d2540150783c080a0a12440030b034013503460b0042805481000348001c0341100d42480111103580c1000d87c0f00803d030105540ca0b142a043c0040c19030140d00a0358140d980c014001030464036044155240e030100100c02c5418400c2c00c01004c2400c3ea03941034004900700e40d5179521075603032600e00d018900b590800b500003840c0056062608416035408940c500c103c0001c0c0ca80010f20000c0401e080f00507151982c005820300c04000744040500d640302005522400c40d108140b0000b28440051541e00c0601440754802507030103002c1307808050a1400150307000350000b01121032035203494a5080e4898013003912602c40d100586002100505040c0d0b1260303004603407191507040d645c0340c031a81c41424400e02c424401008140c803141c80305507000c0c40204000d4900548441134601d4410303a44400c03180c041d01e42d18070841c90054a024560014062202400e03819500c1459121140c11141c90 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 30113476 1250 30112226 30112249
    0xa050706080a0f060e01170a02010f0f0210050709051804050a1e050708030c1501030210141201030c0e090d140307030603170d050106090e0c03060409080a0c060605061305 75
    0x1802c2c3c9a2850440b642d0316405003a01401c0c040342c90040d954900b0404071040c551050244c0c256802400140e80940e0f0070500e580c4c0000c3c01030600e4a440d031070200742242440c1070a0401c200c0c00f40f0b494148001503500c01620811f42c0c41c20f4900c0c080d001c207865000030b04070a0032074008045a114015140000c0c2000850160345496101c05252606a0303690303c030b040504540040301e0950000c80c54100d07500003000691005a482600041c2950441d0007040b6410b08820b940010310243c00d002c1c0031743d60b404000300d40c415071030002c5014039540c480c500550712141902c282015010800d01241404001082c0000e010f5040d45481d0030b440038207610405507810040c54101071507901c0d400000800c0ea6410742c5218142c5142c100c80d80e450a60141ca4100c03035042c1c210b6810009620000e010001c10301c1196600280d102400e030792a85e58001c00140a0103464000404d01c80c00400c100c0c141030340001a441d40716100b088288429a1600c090095600a002c0043d200c080400000c1005080c580760a45 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 30114726 1250 30113476 30113491
    0x3091002070807051b090a0905061b040806070e03010c0806100f031104061e08040314030a0b060f070b160504090f090c03080304032307020415031209050906030a05070608 75
    0x20b08183e200d0300c4035418440a409007690002488000800901c1c1100e00301fa0b00078440d820070080907120341c86c0c0558400e00103041a00a410b10450030703540c000d00d0820b0702c000304961380842e203162604890040c00e0010003102c09000390300b0102074940050082e42c40b1407003210007603d5201410903480c0d04840c5031071110303810400c5c550344040102c142c0040200400152415403a0095187d00e0255030428200c0d00500040800856801303000000f40d2003401c0010416581c180c03035441e40ca80c042c10074001e11000c0380700b5030f20003000115011151542d8000d041400e0048024000d030707a9840380318404130030703030300001070002042040203005a68556001900040f40a813000901103101c1d81d4881c006800d50700240d48444020040208155010080700ea580f0305c80500c0d11003d0000d4407000e80e4601502c50700a10643d113600300c040900c9481542d81c00115000241540070040e42c0ba0040c2003e203c3e030140700c0c001c2c000d20700002c0c91400e0021f440120320390301a00410b500d510300a400c4502c40320282016 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 30115976 1250 30114726 30114743
    0x8041211011506110114010b070c050a060807020114010305060c0a0509040203010b1308070e040816020310201306030b1203120a0b0409020f060f0c0f010b03120309100207 75
    0x280c0088500348500803141501e80e10207222a0b08080d070140c110001040d00c2d54940c5e06081410800c00b1b2158115030450b11254802a200c81c0c051a1401404810b40c1025800004050002036185c3d44a460140a0074050300204050284600350740d0340850309002c0601941c0c420302c04120110841c13001802c00c0d440740d00e0b00c503090010311000541603a000b070b40301902040011030b580c0320a01c0603e0041b0003c16101009000262400c407603032400540003080500710100c0407800c0c3d0540042c026485000316070040589041a07881c2004a00030100030300030411a1a91300403480012503081c045806c1705007120b050300b400900d0300074120054128100341c82c0e045291300d0b001e5080f292080000c0c1025421782d040b480030510302004a00c0c01c81e402049802d01c190304101d807235409a150b4011500360701c5015600caaa403414148021000d51180c007880f1a00c40c81144516a22040194064009041c080301078544401080003092503030b010541d2026803c0c1c203c9480021800103960007801d40502c43d8460 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 30117226 1250 30115976 30115997
    0xc0f030a0b09030306151806090402040302041e05010902040602100e0f0303040c060e0a0303050d0c0e18040b18100504030e040c0201050604060801290406030b041a0604060501080412 80
    0x80d1141040d050340c50085030f9101105102c00c900d480c2c0d030341d0503001059101541c241020074081a180402e11038070756000780e01c0002c85160b50f4941d0303012640615009401444407512031102c99000340f20303a000310089140342c01c00108090045008641c201d0780035034000c0030380000505081d4000d00b001e03002c0c00c00c244102840304980303010920255210758040c4804809480c80c00001401c075011503503000e0720405a12905200180d00b10050700d400000c05d0b1000180c3c0c459081c0242c500d101c1001040d44e00030781d03e40c031140c0f130340300c46aa01e140300300d209561044140c1c4420a104070324100405268000790070124800c055800c2c554081d5034043d01a1910b003510040040204044582e0000d107040140d4480c4100500d81c180380c019580100384a200801185015000c060300d5403842003142400b9801c0c001840c80a80d03926040300019581001d0103200504051608094001c1401039103a11f18034040001200c0303140a10882d4210b1300180c6682005659550b9080e055402c0003248100307201f21440c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 30118476 1250 30117226 30117233
    0x10806040612030f030c020c0607060e0f1e07080606061b010f02030a09021002070303050a110c061204030906050408060109020307110d02060105191404090f06020d0603030e030604050c0f030a 84
    0x2551858000e403a8180c1542c204c25006081c4c829041d9490155403001001d4451611100112210250085000125518003120450171302c030700c42000c001148914000c00302a030600b0001942100d08070800ca0341032698920b50b01c0e0700c4100072540030b98410814440749160303080354210080740d000d050000203011120038110b44101d0b001540c000d100b9682e034415100c00c504240206c011130340098001002a103141d035400400d944210120b542c02c100f44500100c0d0156030411001e54103440007408513868000b01c100e50700d050041120140e0004061000024100740a03100701e074140c4c0c84083c06010180c0c00d004030980a540041d1900081110301c0d610541c5001007070009100f107041c1c1c0d90140c4603d5140c4010440420a50421041c46c1d24070f5440800c018007400c004000d6044060f10701151180c45400c01d0001d401e80c0207000f40510303000082000314000b90754401002c3d01c0c0310741c84903041d0001240501d81c0d0b8040840340206682e01a08190324246080210000080001021126521000c1d078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 30119726 1250 30118476 30118499
    0xc090a080a0312060e0405060613150e0403031103101a0702120601030201080105030102090306042006030108070510030207050a060f0b0604080303010305060705030402031b01030f020c0a03020c120c0108060406 92
    0x7002500042c5000b4981e0385102201d002e00801031603103906011060500361161921514044e000c1c0c1e12440f14003840d100100001d420150500740039086030081300390344002003c403510b8101c5041b40024508501400c1000d15007080c1d90007040d910038095185410510f900c41034002c120087d000303051051040c140180e4500391607007542004a4064030306945540f00140502c07030180c100500c43c1c3d0040c850740903d6200050000e90051304401d00b00086890a0908911054641207540e0001000000070603c045c000500c24121001520b1540d260f044810b8218100c0c000d0707840c0203007250000584000410300a8012102c00c00f6502c0c00010040c7c2c0700c41c0010b1543e840b80d404440680c20110040040c0070b41449160750020700d90a1041c07071031600c0da00082d103840e407027200c00785510085060320790264400e5001c0b40c2c1d241c0001104561b5a140895443c0e036400381d0300740031401840388009400c428181490071003004245070f0020419070f4110001502c004400074440da0304640d464170000303080105003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 30120976 1250 30119726 30119743
    0xb04150e0a11010f050702060906070209070c1205040501051b010f0606030917130506160b040609111909020703030902040c03091a070c03030b0d1202060601030e060606030c090a08 79
    0x308219120707403410390b00184000402030f0601c03000324881500c8940120803102c00c1a0304540301c07a5950b0004001880d43c1c0130726400a034000c24030000304100150000b40d02c00701580103e00101184481c000e003111a40310303500036240040e03014000354500030300600d40408500c4203000082074a40161421504441041e0300542c0000d0b125018401404540750742c02c2034007244107405c40d142240925444601000610880d0300801000412200009070b0040206070640c2c8400310a2142c103180c00c00c1400742800c404151071510b80010090001c0c03400341c1000005480e5440d504604c0e9117000c0400d4000c0d0082c00c3c00303406150311810701c039006075594402c55041850a0b18005850802e40c2041c5403041c1c602004810824019428131a40d030f9040360300c8114030350303061a001c180c807500000031502c0501800c034010320399142c80caa03032001d05801141241c4507a074217903400c218084a08201e641d40d00070944181d60080401c0011980c40003000008101c2400e0140421141507038890603286042c504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 30122226 1250 30120976 30121001
    0x12060504050c0d0b1e04080703080405100e010209010306050916030b030a08041e05030f060606030a090206030708061009030c0314151504060e01060210050a1116061b050301030b0415 80
    0x1440d0070480004a00031504180e140c10f805e03074040c1850b103a80c43c840c8030303c140b220103000e0104460000e0f0810004000140c8000e00721101484104000c55556010b5003121001c14082400e169002c6014180080740034440c00c02c80811844104900d00e080e4010082050195010b0080c0080500843c014900030300c0104110301100010000d4500c050003045055007201d031207900003c070750036004900001d0864100307004507175155a0391242d04202000f0030140c24020f421400101c100306a0542244c07145100e542e00b034600342440300c0c41c407008076900801400010240c3e007a003c2c050001c501c141c00503a251103a0360045400c01c4c0c000760b10450101d40c7c00c54030394019113207001d9030f41f000d41403a000c5da40040400c3c110144607541001c901a4945540d00664050140e0344d0300015512509074200e20f400b0044109010307981d03450340c200a021580d01510640d8201e042218885003580242104600d800d096030306d07d801d40c1d08554496003a0200a403054401400c226581c9051904501c82d4110308200c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 30123476 1250 30122226 30122243
    0xe060d260a120c0e090c1318050a0b090c040308090f06040e04030e0603190c0e060406180e0103030507080a05090301180b0a06051f1701060c0b010801050112060504050c0d 75
    0x5100703000c80c050f210400e07401400c00c04080c0c64400ca0340c80d40c0c0e1105400860811175151264045403034071402d07040c6a84010082e81ca024006002211130342e00560140818040c18001c40c0080414030003d04000e81e42884024420007041010a20132005020844002000300300072100300e100184076a00150002e04c080c000e150240020144c0010030400b0790501500e00718210b1500b40750703c25034105000c03d0000825180c181a4545d50305c03600040401c2c180040c00345441d80d4850f100142140c0301081341c0205607400560201e00d02c500c542170141201d82c140c0d99540f81481ea55203c0c00c8907004440d071201486028001c05102c0c0d5000c5c01903d80d4901000780c2e07070380d0419080c100306001c85e2002c2d09500e00f40c0d00d401814000d545841e900e41898080003c41058414030b6035a080740d0f507048003050f1510002111002003040c42c0c2c001c0d02c200e00c1b5806860a02c0250341c8032290345e400c03200c1c2031260346030114403000700311300003041604017650140c0944c09403248101c442001c100a6582032804581c0440c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 30124726 1250 30123476 30123497
    0x92c0c01110c1804080c070905100602031602010c08040806090a200a0b09030a170409060617040204051e07020a0309120201140c070503070602010b04060e060d260a 72
    0x1648040c92020324218000104215803002d4045842601074a003100c0201c1e040e04006024803001c0f02c01c43d0354440d030740c80c11100b92035a030b408154002c0400761804041c405080724006082403001051390806c00300c13000c1c07030f01c0000e18582c01980c1c40030b03042d141111600f0382440b00140140052017182c2c40340482d44c0280401d50103c3c50001011840d241c10050b440214010628080d200c2070f0340d080586200210050391001000e000a180c40107034140202403401c1401e14043c20000d0001800482e03038403510034000b86450307000954425281e02408a40707a40140e0000e000351400b50032494008400d00543d01c00311050400b0380315140000c1352020050781c0f00080a03000c141c1e000607030000401440200c0c00b1003080f1980001c1a04110044d43c20031100c0c0400d0704040740e4402d001d064001e10004040ba4629a642c0001901030a4504804d6205900c0c1042c00200071145480e03007485860001c2c40040d900318180e54102409154801c400c03964020159041c3d41c81050100800d60440182c4444030a507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 30125976 1250 30124726 30124729
    0x31309050a05040506060d020f13060e01300303060512031305030c030a0602070c170706030609140c070303090803280e0a0201050a02150a02040e060307030309092c0c 73
    0x2a003024003a511220310340801c200c080b030340100709030b508102d0131241100086070f1400040c01ca0a1007040f2103620488403010058041003603440002228008880c01540f6079031001040881c0301000004c140b0b80c072081000302c000030f490480d4424924820b060008080e900e500125000e00300e007200c02c0101303510002c3c0da1001300c65000c5402c002420103e0041c40300301c1c42c000100c0e4640c000804000c0549801044100801420440c100003a080340001d00c031a40302002d45050350343c2c0701c620400c0e0101c0c0c0752101c045514161030081c942d40d410742c41e07031041440d100c040304064180c1c0f048500781d041540c1c2d200c0b0000084c01900c0110300902c510754015a8038000b901c04600680c10410f174441c08149490244030f09d943c00400d905e01142d409080c80e644440d0f40b42800c0e4181100145202c1700c0301e000e142008000041e80c0e014005031508640803074410f40d13581c01815a5034030303a0f01018001c50142c0b1000c1000940303580000c60280e04080c00c68090082008a280410743c2e1031140407210340001c900310805 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 30127226 1250 30125976 30125981
    0x60f110303040b091006080d030f02040503060901020301060807030207020102070e060d0c06050a0311030405070306090f05060108010912030c0905090a0f061409060108040807020904020402040b030a050708060d0321060305031309 100
    0x5000019003000301c141f504000959902820145400703040d101c1c1c80e0801031b02c00d1541610002c1c0005001d03140b541ca043c0440340d001394803d000385001700d503510010400042c805e20950780e0072a41a0010300500e03041451403182d01b50700410003640009501002030008902e06080ba00600c1d15031034054039801044405800d9a0b80654150240c1506000b040701060000510b00c040301c0c1c04c070800088103505030400102d0b42c40b007608054554414030340000351b0200150310010300d80d030050b80c2c41030f403401204004409580203038411200040310b5601c00c1c8040d20f00807820340d0b00407040b1600000c0c05c2030003840c002c05681301d681c00982c82d00c05418000038941400d2640c6507101409103000d00c240e240c10307500d1843c14040e06e1806405400e912000804645490f8100c070041d06407050025282d10b048408400507003402c4800e0800500244003282c802d0410f43c184683c003035410348440306c081c0c8248010340b0909540445010000380c03075190000108400f44002e00c4d03d0050040503007220b50800914406 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 30128476 1250 30127226 30127243
    0x30206010807080a0302070902070302010213141e0f040b010306090e0703021305010e0a0e0a060603150b0405070c020904021f0203190c021f020115090b010806090402030304060f110303040b09 84
    0x526000740b10110002030380461f19909482145500607181d04032410308038020700070000031121600c2d103001c0218000b200c0310281d96148204840c4055031034040b20092003180310409020350888801980c60019140607009081a80b0062500080c01a5902208816104460300e002c0c4160410308050040d4104000d840c501610f081005100c41c0d45009010a83c1c0b42c0c0c01000d0310405951083c2e00703c20032500b40656804a41c01c8402403101c1c07902d80c1060405d01101081d0786501d40d282264005a50a16000390703071090449844003000c01016400340803108000a004a81c4080081001d5040781c0140d07050b0807260013194001c6868640e6064008103104481551905200c051034101e40140c0e1074844481c0901c1c20140e0b00c601001c17070340200380c3c09880c1e00c54100c00c01703180400c408a9102c0c1d05500c49103200c0b0007640c0d41480c42d00c2e900144400f40d00d05442c041d4040e00b0401040c01140d01400d1034030310a03515031801010f640002200d00703096420039141260001018400e0141c0c84004008205 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 30129726 1250 30128476 30128489
    0x120d05060306010509010b071a0f0106110c090105010c0f06050c0306030d030632150c0c010801120b04021f0c14030a020d1101060f0306090204110301030512090f040207030206010807 80
    0x10b40d5504000000d90b460320148101c9181c480c0009480d010813542c0403041028040e61112514642450b4490080d0100c0c240200310009081844030071f18100006080540070398041c2c003000482e400d00004642820700d02106480032842ca00441e4002446c80c0f00305441231002e03121498590414808150510006000300400c140c1824024001d59030869030a031029100a040030161008240645000c1c00359001800e0344003c1710318911440c21526001003030b155080200303980e11106003100548060740280601c10012182a0f100c40025040c040c200750440d00040c07451400401e60561000740400b031120620006205a12847c20002d00710841c0c0c1610400001035401c0c0629031400a58035500c1c00d20800801481004250034040c2c00c0d80100301812340d0001802c1ca803500c0e030030040040d00c865001240504e03e01a81c6103240c3d4040010f49042e0f0740e210000d8601056510310449050700002e1055500c489020600e640b00d13a640e20080043d540309402508e5658580229141040150f51204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 30130976 1250 30129726 30129733
    0x1109040503040504052707180c080a0207080702030307080c01050a1b080612070b070b0109050103021c0309050909010504030210110a080907080105070203040f05041107060c030b03120d050603 84
    0x8400600d0110a44082e9002518001400c1ea5020841c2d0003824124016504184030000301c0c2000d26030109035481039503012541c0151031822040d245046038020701d10080016a5003000c201a006941c00502d0f526011f0303c0e01b240dd007149600001d007540c3c0900011142081c0001301e1898000f002c0c040c450380400350110401c14112105054041d90b10245401000c000b140c40c00680141e55000300001c0c0a00f1b040121400a078803404c0b0074074294000c0c4004d95404020300b00014102d40d05000c0c26068903400f0345025a13006020183c00d0f02e412288008609200038400c0114240e2901c030b91017486410f4440011807107041c5803c001e400d1641c041140300b4090b007440b003440004c89078402210025186854880c4640da15002440d0414845412905255003018248444154000050815903542c0701082851075640c0f4200021195007145403c81d01500380402070114136158401d0390142c00030f04010a464401200003820b04c01d40d00211340c8a00c1020803003900b070501c10b01c00c40354018002e9009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 30132226 1250 30130976 30130981
    0xc2d091503020f0406170c09150307030b09010f11040303030b030606010e220207030201062105060703020903030903070306020301080c0f030a0f02030307060501060c1515050103020c031201080303041109 89
    0x810128203200d00000c0e0180b450f40c0b594400907280e5610000c0105042140e0300c0940e000b103800140c441d64040d0f143c900c01d0819401161804441000000d0b00701c0700100140301e620718590b44c1421407034006014a4075550b9500b2107200c03421050040c0051207442004d91560381b82180380143c101c1e45240c00342c038080e41c010010020640d070010005003110000f11203d4100b140301d8840007180c0405505001003550001c01c1c81c0c02010380542003002510880382c1c0c81144002040e0390700104c4109179078090540d512007004500b001c0c0c0a1350044c02d04140203000c3c3c030324200100020030316080d06c40e40220b50300c550000c01000082c106100051950800f1030701030700e085001da40081d917a008044400740a41800d07180c50021540d04004030352802d0ba001030188110b40e0350346005003904001d01d1003030b16804000d0900400c883c0041c425044002c003100614410a030814004500070340150824040c80c0c84100a41050b0003101a0898002c00c1c0300340095560b4681484d11a0480e8042c80c1c1c1940204401801d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 30133476 1250 30132226 30132251
    0x21003050f0415090804090219111c090302090f070207050303040b1209210301080c0105030408070605060102030f04031103010c05090901030303020a05280206060915010503040c2d09 80
    0x10500d80060b00035601801c40300390f9101c420010410400000d08071100010000740c5c50186070043e0400e51650300600e43c0d250403810041e2001c0c00202810001c6401580200001d25004003010030145000e2405c03a4819450754046845240e080d00d14000e0780300035200700900e4642c1001040081c21040c1d01441c1000e140c450ba8070028012041100c14560705000041c200c601c0c2003100302d061002c1d00720303140c01c031000c680404020390303000f03005020b0980a207a80400031540140c045034010360b4001c080910b002e0176a25080c00034030b4050007860450008100c40e052481148024201840c003c00d00110010704403000c040c2190b4078a40c2c290244002480031a4060360741c000a03604503505803e015a907605805011070b035034804c0d00021903070002007858102011143c00000c010040f803a070200e403d96100c9104210503940c1c03c0b81c007210010f402070140e5806511450141d82c2103449503156400c3c00742c0714000d1a8004540411005c08104960001c80c00c403400c202c061801018004003c1200c2100001d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 30134726 1250 30133476 30133501
    0x11d0d09030201050d0e010203010f03050c030a0314090d0b0702010221041703070e04110a180b0a0e0f0603090c01020607080108150601170703050601090b0903030417071e0302100305 80
    0x4070190601801013403001c07001074503402c4604903920600c000c554940e104c1c1c942102506081c04151064440c0302c0e2500141c1c14006034100e00f80d40c05856141c80c0e2441402c4100040c0c0c041c03008590071002a070300c1c0400040000320718900034215030300090784030111000702006489140b0587c02e507040a40d070a110105000704800100d511000c4251940c036a14080140c031950200c69a040d0410700c1c0103494402c2c2d00d144009443c51f00000ea80b000c644214020711452814102d000c3c0480306581007120000550140f200604950800f4101001c0250714000245898000f110013450b10b82044100c00c4003581d0500c50154030050a0510b035120b5410b01412540d50701c4110b0550f00340c0c1174140c02052150b8010348840c002e58030183d002c0051850485801001f9100c01d840741400315485207008500b000901c070a032181a840070340114246031410b00180004003001c03109106600551901158020401203e003403140c40c0d0300c01d8181541c3c03030342c03040c0b00c12850700300f85407000c052a04007844400c01180c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 30135976 1250 30134726 30134729
    0xd03030b030c011b0204021b070609090c080910020904180606080705031605150c010207030e090a0915050c0403150b01080604050f04020d150c090305100c050403080d060512011d0d09 80
    0x5960068681e00c400301c0000031507054204c445231511814000080080d4020040380940d40960310078031541d041c9540907145110280c40300c01481d0409440c14290125560140074aa6002440490564500d0703841c4002c000c0004400d6560340d40300c40c4d00348299881048030b0070044c6802ea0007040e030908481d90801540b01280903c1c0e104540042541d42141a0001034640d01500307103008641e50b090790b1402501c00d42000c00c01178003030b2000b0f600041d114182c500c40c00c014a60001c1c01074011200b00e00420000b1f18000340655581c0b041400003202050f690446403603002201d04002038011010310002d030131000f0043c10144503609040070842c1e03404141e00071a401c5030b4107844907a030100c03407450300494441403100640d42d064600008100280c0d400741100c0308490144080da115191207204103015680c14021350008503000300000c00000e615030004001010f04030307000050591311030000401c400d5020050100c240c4d100d094604031901030300750304540c2012200003010002c02d0101c000e00320450a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 30137226 1250 30135976 30135979
    0xc0f0303081609051005031e07050f1308030c10050f010b0d0f0e0105090a03120501030809010f020309030604060c08060a0e01090b06070f050a050f030307020703110f0d03030b030c011b02 82
    0x42022501c2183d0007050b01c03801408004190550304811150b008059400403607201036484203042c50141c000d0040f0381d91500401040c1d0f41c161500c03455217000289688011400001000b8008001131011018806043e00d0381240018080604c03c40d1980001d17900042c009044d200c11040041102451400464181480c99000852082050007052004140e0b5590040130f0b5401c16040186c41074001c00c90750304c424801d448000900c0092110303c02110806d00004055a508201c41005503024990414400c0c90a1040368075040020020a00340300c01541c1c22103000f91a44600c9401a402c8041c46034051020b0b11813256042c900395410480a1040c407a0b80343e2240e4a401d00c111949410701124625034201c003010581400f10b2400942d58510944180c1e985d004803c855500c010000c0120380c01403055900078070780d84d030540d01c40d030903009030300146903034030140550b4255a55220560701d0724065000b510006230f41c51265051500708101800c03194100000764101c0020580c08c2107500c03050940 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 30138476 1250 30137226 30137251
    0x20304050d021c060f062304051b0a020d0906031808030a020702030105011212111b01170a0630140109050303010902030403020c0a03020f090703060510020304030c0f030308 76
    0x1a1400420b01112107509a0f6240c1e010000000090050035040110b0703501c01c1a400700001a078500301d00c04120740d09403010070a07006010481d2110303e810340105402c100e4140002d074a0a0b0610060015603022440384030141c6c11906e40d500005030000700020040040d03060500c0902c201e003126466186141c04020882c41010012a80c00e4105906464200703501400820103940c40d109030000c1c000c4106c10441b54580640700142c0c025105e184800d042d01d0701c0e03900800d04402058079811480f810304d60000d042000c0801d0044201500c19501340c000d02c40d400c000110301d41086280400c0c40309007040c8001d46203201540200c030795040d0036030300b01d4179411545070003090749404179060140145e9003000d001032002100202d9581400e500441c0154420307000c0f2070807032402d2000d03c4848c04540c0300c040d40c0b00b0300c40d600c0c58916040602e0007550080c00d03490300007401e540f1980052640d450015901e801603001003802d00800104543c0a03014040080310302042c81d00e541c0e40286803c0c4020a041113004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 30139726 1250 30138476 30138499
    0xf070201020f0408010605040f0213030b0408090612040311010c050a0c05030904050c040f0e0103030e0409030e040510030311060609010b0a180b090429040b0a0f09051902090102030405 81
    0x14401c0d030684042c01c41c0d01e212a66101d984000d003601030035886c000c07144914544507484801003007520031103401c0b480840208017503914545400724494002001503400c03030301c10440c0b400e40d45d6490340200000c0b041511041000c2c1010304004104800c06040445580e1520004026031a08641601c5151905281581d01c407109803038500d0a40c043c280390190030505113000c0c0110070320900003400c01d03070701580a90020b6541c1c0e8080401805420700c0054086416541140d071030f4285a0045250745020382804060340d031091001c0380c2121000c4441c01258508104180209070340004c06011101589004003102d040110000b95507100c180b04030300b050400000e0803510940103000042902c42c45200c4040c010355501085501a031060403418455460804040360360511305164400300d51401444031a4042d0710386c1800000d105403980194420307075003040010068202d8003083d018050707160000c02e05003041100420000e80182c1e00b440007600500c02850341c0e0741c5c004150740440e01d04035040c8200c030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 30140976 1250 30139726 30139741
    0x140702011a0f0109030f0b0115030207020609040c0c05062e051e010c14010203070e090907060311070203012909010e0601030f060e1005010815090c0c1c0c021008010b030f 75
    0x4000a5100801b612140c100082c06c0c003080c80070441c100c034004421b24103c4142548120224410f85e800298840001d001440441c2040d906c18014105181882c190310005030312058076000d1704548005d400551420039014034660070011120b00b10542951900950600d070020f408410b00d110303ca412402d2400b07048001c1d80c4030710404c541c1e003038207c0400602c9079003c24a80b13010f03520403904180868441d440c80e40507800c10301007241c86250345038044c220841c02c1c05002c0b000b1b8094442280c080342c0003803080d800581e8083c846c1c03090b030607002c2c8850f411045280303030380f40c41001410482512511054004120044a0007407480d0b2105003440c0015034945000010402003650b600140c042e41d180e641009411b1000030003000a445090700c60f14543d40d0b4500c03500351400d003034408881e040030803c0042214504100c001c0c207901c10402003070340c07a504601070403a082c1c0010070410a000507071001c035070020360800d062102e0b2448920b2800d028030358103010a011140c8000780041c0001524200000c584 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 30142226 1250 30140976 30140987
    0x80d020a02031207090501020c0a03150504020f10020114090d02060a050604090c060807080f01080c0114040e07090f0506040b1902010902150a09080a050c010813020402040306140702011a0f01 84
    0x120701a1962a032150501c0c020081a00c0640c0c0101b030f0142c0f1402151201c02c1c585801c08800700e82d8800d2a003003103d0507240340701002c4c0034050701c102e8008142e2a542000d80d5582004603140400c641d000240400c450340c014100002d000d0109020740c0c101c4641c1031380300ca6000c03d0456005a40000105031a15840e001c035005040c0c070070025280702000407000c02d4480c0e001c0d1045018501c26540c100700d64a0b0001d01c018034003420300c0780701c03000e522400030141c403940515a01d10308005c261009a0810303645280c9102404000c44040c80040d50030070091003452a100507610260030107460031400d00e0304043c010b20851180a00e2540c0c2d4144462241480368401d40000d42107590142402014501d4081d680d00326420524a075000b091840c1c201045d090320000e1021580350b0800000c1034641c00d01070040d508894090200050b0b0308175a050000507071118001440110f20600c80000c0034800c100e1604002c0c10054800421a410300c9004650010b92814a0000380401c640303843c030820801005a46 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 30143476 1250 30142226 30142237
    0x70c0b03070c060203010303050705010b0901060207060c020102030f0a0f09080a02060901030f0f0f020309150c09010c08040807030302030405150a09030b060402070204050f070207050312030a021303050a0506070318080d020a0203 100
    0xb40f5400040003004156100002e022443c1c030a80081c410410f40808018498109014800050b840540100041441601407031011401030041c1c3e45404401240800141d0001100c00f01081c1c401c0d0001c0b0703a0070f0f40410094020070f8064054000c0401507400a40c1910456940c641015207554070400640305071f40c454880c940440c3d100304a0400320b500c40401039041214105c3c6c00b805030ba49013040030b494801d26140720300c1c42c40a207649401e078404015542c20361140d40070303160200d0501000c290580204103100c003541c0030f50025030700c86240200700045030810b500050402c07a800e028060107140c200d220442640e50000040103281e44290200d8005e009401c0701a50150030318043c00856140d0b0519a07000344146d500390b400050b1076200f45a90380420150010510504000280d4510310319406403c151790408024a25541e882e2100f034034103e81a0002d440c0341d08010140030501da01445941c0c41c50603420f11044040c25513495403a050300510000400084d00000c0e0b80756401d1081c401c940 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 30144726 1250 30143476 30143483
    0x20319090b03090615030106050307050402070303150308131502060a0f0b0d0c05040605030304060804110409080c030a09051005090609060d05010e0106020d0305040b01090923030a03050606070c0b03070c 89
    0x16141d1911024884d61290180d4400c0030284c00104504074604040c0a03420582e04003034000c4c500319240c0801d1000070340c4005020b5040660703440c50740880d00d0004d090240290701628007103442c0d41800440c1140010168400740d0541d00039990811116004101e8030742c80072641000041500480c500d11010f01001290300742d004004070351540410840f40d6041080d12001d079030801c001a02d078414141d5a11850084902050207240000c1c0002c0010003e140000005000824408103070780d078800381c40d08800784034103058102082d10410300758014002002800d0454a00d410a00303503140280c05440b860304880c1c082c40c0001010040750b15540d04840040080310810096903a41e51641c2488940038010300005020301030003201d915201c1e006082c001d42c3c00c000f668200364a05a148401040002000c80d480e1b41c0da0200495020f0036140c3c5016104050005990b862400b100020121103000b842d00344100d406010280108040810000c140c6110712003440d030f25101e01d1001e035040e03540302c0d4004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 30145976 1250 30144726 30144749
    0x50a030201231303050c0a031a040816060b0f030703020604090207050102090603270102040b0435060907080601030b0c13090204031a070c050c09060409050f010b0307060f02031909 79
    0xd06000d803c0709410400c8a00402c2620740103545c4000300903003400d1500c0041e281b48000160066844003554070903030894807601d451480d0190700d040001d110300100c4806e81d500b0380d582c0b0710f0b4910760914000668240344c003200a000b409045500180d03c50007240180765405074042411010010b00351b0445200403c0240b0003916407034010b034408000b02c0503403400319007004c110f12001040d000500030344e410341c1c94a04000c0e00341418403003d4004a40b203c440080c003017040340300728090000b075140815600060000544403501c1c242010503e061203da0080b24250b103da80100080b03004180d02680054040341a10b56076840c41c6c00c20540c9422a030486080140f000900100300900b0044043c1d101c00c3c0303143c2401055840c0a42541c041c1e0f24080094902d800c6400013284502c0c01c413241a0307112100420009a120840d10745516000d030207614120580c1d0349400101503890200041d80003844186001062910b022400035243d025907440b0380c0811081400c000440d0f13008072000c202420842414 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 30147226 1250 30145976 30145987
    0x402011211160507030201170c03060409030e040525050f0706020d0905060108010606021506060d0e030f040b0c101e0c020309090c0d0b01020d09030201210203040b010608060a050a03020123 83
    0x119440b80b000b817008a0104e100c11007114603820344a10114400e020441c200743c110394a1006000260500d103004404001c0c00c10240f1845954500c603540c01400807490687d1136840b03001e441e51180c07012002c61701c11300005000c2d1140e0212180100c480c52a8040d0002d85c880e9a1180001e01410034824020098040c96001050700c110550240c02100c1441e42100c561500f168280d51401c10b0584001ea08406e040040c0586010203801410581090404a0b0720317140b045200041160825080b0030001240025620380d00c0710304111714011219a20000c1000e81f8072001d15240d0102e04070503100c0d0070794035140d50720380e10385c02441955408a409004090640780c07402454101e91b00491030700d800141383c407441d0700c01544005440845103031540c891100d190f06580040d90050f001c10810841511141075182404c5c01c0ea0020354000c2d4401c1040c00041c1d4100302010b480ca040007024507020700c000c81400c0216542e2054103c2c1200c0e02802d001103900c20141c180d00e100541d00480010500c0b00088 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 30148476 1250 30147226 30147233
    0x603010314060f070f1107051003020702040f060509010e040606080d270b03180f01020703020705011d0609040504060b0406030c0f050307080c060a020a0501050703060905090303040201121116 84
    0x2080c01c54448000107480c000e40d41c810504800382015915840000c2c45402994200c42c050034411070f641d08584210340b11103507a803000810030a07170b00b4000c0002030703000b0480f502141054024850407524040082c00300e14104008212550b005102c1c90380301c0b0018402080c00d02c18a0361200e000303000c0d41402c2d0b501c42c0700015030241c241e424941d400751060709140c68041001c45074250460588410718906071450b120701403610343c01100360301e000b0300358000da00c03100c0b8008030244024034150384260040c00d6268504000504081d00e0394851890035a0f80c2440c2d040d655403001c0c121940604200e4000413651100d00344000184003402200e034000c1d00c2c0507000300502041c0008141264110890262055114010b040e1221441d11074201c441d4401f4841840c1894142d01400f22000380b44120740441300b00f0b0300c0325400c1d10420348070741c0082540c0f0003080c0196500c030702070503903c100f040700114650704059000030135032010400c000c3e0b0015603e03100d007410400c520301220f00c2181e0740302d00c4204407080350030f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 30149726 1250 30148476 30148493
    0x30305040c0509060906060d11071406010614040306092d05060a0c080a111204060b0112020721110a050106051002060105030a030e0102100c080618010506040b130506030103 76
    0x26001c0e10040c100c50400039151a1030340b495445004044e00e00241611084103104440d080b2040300322815842c0c15402c20300003036034005443c40ea0302469100e01522082e50240f030410b5010b800032010800c42d5550302284185400440c4d040f41c1e48120005219003007814554200d000400299002c1180d00e0030291034080200f00001005003e0004e4a01e603071180c00d0300c0c0c82100c1041a020022590b01800a411001d00340d1141c03078610401209549401c510301c001000c240e008980c04c951503661194104204d5070301107000f5609020034141140707007004030345481003809041001e07520062082c0c00c03400003942c4070311801104080c0c480c0854248200616206000c0d06003030103124000e030800310585001c94800500541220800b601501090a850318102c55421000c1c2c40c031415841262407504912042c0e02c0b420070b00804a0380d03441e4090820b0003c100f0a81442021201c20600f606c00622240c0e88410440301152260380210b0390b260b00d404460418011241d10180c3c0c04040403000106004954 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 30150976 1250 30149726 30149731
    0x20715050c06151c020406030b040c080f0304030f080309280204150506040608040614010608061002011b05130906030303021b01051e0408090a062f0a1211010603030305 74
    0x441c16142256585507160f011500c06000b044d0313000b40100f1071420b02c0380054004a1500340017030b00204881e503c0f915440090340c4140d0382151506000002040464402d1000c002d6040ca660061403506155448034560800d01035809405c950f000804110000030070000c001922500884040c1000a001464102c01200801c0cd0740214100f1684600c0c3da542441110305450000b0071540c100b81c2001070451300c41d44000c2040310003a0307823400302554200119101c80d000348920360b03a02d4100d10b002410303c425200c4c511604001d5a041080ca40400020350002200104003841e06a4554114070a110381030030b01036200460940ca081804030031700d581900240300820a070290701801c01070486826080350021580e0f0506c6601d0000c0014102a0002803990803a014182d40381c18901c1480c00500c0003403e560200010640c883d20b0b400c00c05048444021500e1131715500019076410380e4504d1380c0c50307603800b040052400068030020803840d40244d040c42117006802c0c0082140a80f2454081c005040a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 30152226 1250 30150976 30150997
    0xa1e0909060e011508040f0f0b0604180203060f1b03090d02070605130b0904090501140a0b0301020a02150901020408030414010e09041a04020a0503030d02120114031c02071505 77
    0x14440c1c007180500494041a04840344480741c01048215681d017198032100207001100d6a0303100350201404030b1001c00900000350300404030b203011800c1407420170080303030080d03000e81a0a1000214040c096500070410590050300032001c47c05d9551850100c101c41203203401800610200401480442140090710b504c42d02e89a8084400413a1505802d6540d40141c1c410f03030305484510344040c44002d600c900030b050b4405010f0800300d4008020380d5002c0c25120101b070803041d9411000c04000344e10841740594444800e0580c0218a45010140d009440341d0000001c44e98000d015070202c1d140c480e00354105d40041407228240d03030301c1d42d48401006c0342500400c10740b90b0028881042188051920b6142d644c007541c1d1000301551407601d0030b10141c500c10f030020016a07020000b40400591620188002d1111504101c0e0040c0c0d20340020010b6808c40c241a00068014070300c0094001d02038a001511103805494019840c442000480c412881d2081c0c130303000524880038030001505140d0f04100a003892800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 30153476 1250 30152226 30152231
    0x4020f0306060a03080903011e090308010e150913020a0f0f080102180d020a05090108030714010209153702100e030405010f030207060c09080f0d0509060a1e0909 71
    0x81801010354500080c2c45440d4820351000381040082c0200c0c00a11320814050000b040d510880f1600b9861088501c404211260725504207504041c0d0001c03045026000c0041c0008841c01c050704500d00c80f404861003540204024000300310b02c800c10b0884c0b0181258018201c45480780c4034041001e407100c581c410255040c1c04060302140e00001802620901c0b80000790a100d400340e400200804442c400304140c1e00402d509030701048585811245601a0808200565842c0d03981d19010200c1c20f01421450f0940e44140700700500c81e45c0340109400751011454446031a0420600e8040c612038a03002d507110054503802001140d040b050041d100c5010780303078080d03401d260660710100b01075070620b01c020441500200424881c540c040e20b0100c018464501d4014181129962280c0495010084001c085000b5503000c2100e01404c001c2d400b0550300300c5000d458621258000030340103000d180002441039a000c40c501403100e215214100d075a5180281c01d160703540d070800c0040d11071106401081101c50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 30154726 1250 30153476 30153499
    0x20c0a1a0402010c120c020306090106060207120503160201051c0f050a05060916050d06090605030d090f030602072409020f0315040b0c0f03100504050106030903050706050702070b0a02060402 84
    0x825000d40300e4032442c1c040e1620b680c82d50b01503030740c8400c40c00360004000501a2a40703030940541c41c200140ca106000e8007000107446820001c010f86042000d03401390058400010503440041c0010041d1000d884030900d491201a0091006841c5809030031004000318000600500d03041a05401002e009138625900b00700f5610741781e0036002640e0f01100d8840c1c00c0400d040c0448c070308680403d80041c0d451110701c2d1030390400c017000e90380b14165545a844001c050b80c031a034092210340b40a002c1d2021b14446030030070601e55841e09181071490485c0e444042c0906a0116000040c030428440002281c44130242c10130103181c0e8444008000c049968040e07000d002d00600c0b00010341000504000601040030090ad626034a942d2850315082008202c00210382080c0072160500d4601c001039400b46d10707150b0103050b8a505220a0208039a8168024004c15003042400f0022076088000c582130309400440c0070404c1d47c0c4074841646080483c0c1d1225240000010f029103102d540428042c0c00340f403007243d0a20300c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 30155976 1250 30154726 30154763
    0xf0c19060209210303062e020a0b0f040c090c020c0604060f080c090f0d050c040c08072a060b0a0506030a02040305010b040204030201020606010f021204030b0f06010305151909020c0a 80
    0x26181c0708030744a900d90040021038854079000c68264680200301d40c24036500302247d000e40c03040251141c88000507a1081c0d0508040220781c2502c5540700a00c2e50190809160544980341701080c0d80c843c0101d016030342c41c05c9003000e5209212460340074034060806035031165214401030440c603400503c4800158820080340e0209102c03011204c0c800c200038582c07015840c0c81c40402603c4005440200c07560320030600110f410f51103901038114500d556442d0899030745070441c0003400c03694170350ba20300f0203601074001d9140032001c00c2c40281d0348080c0c00c0080043c0310104400810100481c03504030a5000070040b0421500006540082c42a01d11400c028000c03a1744440511050303000341d00000380540c0004002902c9544a42880c09014602e4412a00c0f20384009800c200b00c0e034456003090b140c0c00950fa00308141d01c8012181941c002001f0700e820030a5282c0030004100c1c54240540652207a4622200d03580480c0103241c00502412840030210740d520b074954003543d6601c038030741c401300c2c1c0d01c5d600304110b103041703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 30157226 1250 30155976 30156019
    0x108060709060203191707050304020102060f01060206010605090301020d060e011802040b04091e090506041101020607092c0901060e06010804110415030f05010510050a0b0f0c19060209 81
    0x1220310b1030f002142011141034024150321000d200c02001c00145031040000c588843c213105002e011141c44207966420300340002810104001d000d0580ea0b103440c00100080d90340025034a0445a0a1a00507101e404060000c2c3c060b2107080030b103850542c1007d502144030800c8013420b504840400e40004001e0105206240a9004c0d074402ca000b164030511080011103040e400000c101d40c0c20300c0b13056140c1c900c21062581140c22a0105490541c0840d007084108240c0780b030480b6008000340010482d45c504060001e1402c01c440c012445411566800c82060084040341251400384484403000c080c0707490b1206500900301c51183d0705002d21554003040d90f0394014400c1c24003c44d00160720b0b4a43e4045442804050401d003800c1400c0250b00c0700340000803641c00340c06804910b10030300020a090514602c984e01950082d080f144c03042e07915540c100051a200380032148180004003103281c5929044520500304070b010611280140c2882e041d80341042140c2d8004d1050f041e007190b400342400c0700c0d200b00910 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 30158476 1250 30157226 30157229
    0x70b010f1220060c070e04060f05160c030915080f07030204080604061a040504030302070b070503241f0203070b070302040f03140c06041706090303040206070f030905030d05030108060709 82
    0x2411481016062a40721142d140c078142e04030140c92a450060281c1c14070745000c078564480d605071030100341884100700c00c80c041c20140d40802e0b0014000c50401011403080b40724031090340c1d030078010b00e2040703c1c0400d0300174035440b0002d0207481200d0004d03100051029004500481d5031070440503548000604560182c420b40e019a410344000308503030707541ca59400c001060310803100d03904200300d0031030b12045980b03901581c3d214507c255030250700d070001e500d0002d2615002404800501c0424002c1010704600d0782c8103000c1c00d41c244a04540186003120206528105004010480807204420f1410640c3c0000080200602c1f171781e8032040c01d659140c1d0031800c0340241d00038807210a8101d0002c20200750821490601a0904425600e01c2d020003000102c00c0e40c06607114440c0e0b108400000500841d0600800e0b0b404441200594510b02c0c1035400585903100301d0900402c803898912440040c584520701141c090308002d8126075000c4540000944950024400c02c00240b04590010340f80c14404c000280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 30159726 1250 30158476 30158483
    0x150a090c03021003020c07060905030d0206090606150d0203010308090a0e040b0109050702100603230111071b090e1e0d0903080306010c0c090203070f140306040504140102070b010f12 80
    0x24041801d650812541d04400103d610070581c080c000300130400c0c400d000c400300901c20703600c955501c54681302c107140c00c01c10300788802c0b010341d00158100f00c003090f0702043d12070f44110203c403001d1503e0301580d0390020780d0042d101480b00e1148040300100030403010000911032a8021543c09100550315243e2502a8400319802810242988010000100340d5049141c00c6002c900550b1860001d5601c01801c0320400d80c07040d600500d441c8808222410b040c901000964941c41c000d00442d444a141d41c1c80510500b8030080004440100c102d400c4c5d10000054009000303074000074407150010101880d41c87c214840f910385203402000e442c90b81413000140095101c0c5840d103402c60b0355442c0d074841d0001500b009092030f0502151a190741d002400015406d009411000303401030701da00301360000030201c4041c6002c020034403094940400700c910700c000030303203600042c12603010441c0da03503510740241011003401118075258004110390040160040400e8143c90703040f400c0100703031030341c0300c0000d211101d510f44043d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 30160976 1250 30159726 30159743
    0xa05091509060105250b07140f0a0908070e010806130b04121b0609050c030604020d080304021306030f1101020102250f051218010c0804090f0f060602150a09 69
    0x40c050030140c85940e070000050411a040c411400091182c54604040d108a5100e00300469410018890507030340e00700c0001d00c4e00542c0c3c101c0b4a001c11030300348a64040b040d00b50401181510307805108100400180001c0803c0d15003480d542c080d03034041140b081c09403600c00d00a45c000529903050481045da2200c0e0044014255501c1d20b455055082041800300d804008440c21030640300200140750588003031080d00c000910701c40d2810020b00b01104a02400d03c00d40001003403001507601d00c080313111001e0f046041c5541c0d9494074400588100d640391a038040349810400000180001c0ba6040b600850085444598034074207440120300301c0c440e08040142e2600343e44d00b180784005004242640386486080a0315070981186c032a075103000036046083c3d00440700001d0002d5064888074403400584d20030b0800c800c00390840e6440000302d018074058010819170711000c09e10058240d0b000243d9004451800308807182e01d03510000c2d22104a04030780c1820800030000300340410014032580860640002e0325 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 30162226 1250 30160976 30161011
    0x519030e0111010605040c020a1a090a150b03061e0604050118110f0f03040c061b0311030912012003010305030711030a1b050a090c020d050c01060308040f050a0509 72
    0x5551a0481d0b0751160203030340d030b03500b808a0740703403120701c940d908072800ca130000c00380c2c5e414624003800c0903030140721a0b4800600103c02e000920800003645c0c1c00140e4080d9a04a0400d0000400c2c0028020010819850710480d020300c0750384841001480310100c00740c070584503075548200500050f20020f12558181c0c2842c0907071000300302d14035405948166060381d0f02c0c92400074a801446440c2e00040027400c1d401c0b034000107220030001885034010040c44a8200800c0b420050b04001f03124590000014043c0302285050100000c01403084409218004041305e0780c07407075200c41c024020024000007060541d4000c1580c10141a86401c2e0390403a58001d0040d45014150b984229002d602e00c0c181c290103128005810700010b04460320860162804400804054541030400581d010280d2095500c05e2920804694259000c140031400ea40a8100b00340d135100200002401452940d101400c1c11101003404a241191041031a04541d411121100b05c0c50300c07801000780c820300503a201941d81c00715058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 30163476 1250 30162226 30162229
    0xf0a05090705060c07031b05091803030a020a0903210806040b0d0f050c0909010506040b010c0f06090804080304090b100905010507030807090b040b0703030c031a0f0a170a0519030e 79
    0x40564038818410f55105c6980d030b83d203e01e40d48810440c0030049110781d100500031707420b003081c0843e03220740c2510800354065a420109601ca00c4060041d90103581c0010701007213540c1c0241c0645004546c8040311140c159001140d0080703070140441c000c0d0000d0080004a10503103450b0042005002005007180a504e0b0b190707980c00d1503070720696012541c0d4040d0015038400e039076a0768102c81c4240422400894285895005c1204031428211224140441020503201050b41c9040600d80160301020000c1c0c3c5541604001c281c2d03009030382c4020003a20002401040c0500715400540c20300c413041d6070703014412440030f1040e115a0294001c486c0001e6003840303000701103842070200035001001400c001005030348424503c901e03036100340c00030080d8002c001000010980d0610440072036203000d10301009074004c1d8003660042e43d42b48100c0d0603c224a600700c000140d5407049c50f01c0c0c00500c16003602d8000d9141c0c51220549079881070505640074011400040e08d488410306550009641c180d5034100103d40000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 30164726 1250 30163476 30163489
    0x5030c0f070f06050d0605060304050d020d020307080d02030a0f0203070f0806030c031507271d06030c010f030e03070b0609010f060e0103090302030d0c02030d0b030304080307080325080f0a05090705 87
    0x10052117607112107001600d5280d0100541c000c0c0e008038007034405004a0407001c5c1c90b1080c100d5400c000c551080000340081900c010030384040b06a046000350b60f0761140b080da100a031045d06000208248008140082140c12222240415034151141c165a030780301c1c02051b480f481030791449509504180026591a250408100d50020132070804110142c260440c94501103110340d07840c1c044608109007800100c400b00c44520040e02d000c40a0740c0942740c507002003611620301c0884070703051104460305100e40034002d8000f81810180ca0044035219415030500301c514040c2030b9003039400350315500700100b55801220b40307050603640706817680244031108400440040c61001d1003030701140803d210401c0b04444500410404c031800340d000f1a100e20381040e40d44115091101c03002c2c4030f9481048200300c2044040182c0d145c041d00001d80c580c49940703ea14a20301a103860420204540344000344100460700422075500501080003001103030354a041c0c0c000c084800a66034400542d0010804108502e40030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 30165976 1250 30164726 30164737
    0x203060c090a03080304030504171b1c1a07030b01020a050303042003160501081f03060c09080f0d12180b0c0f1215030604120c1e05030c0f070f0605 65
    0x14001910050707580d04d0302c0705640c1080e50304400145000400304a82d088401440701e07000003000c06040f5035444040c00b1408040b4002d0740e00e028507260301000c01e904144880e01004203070421040a003400b003092078507440c14012170b01d5070042450000040c1c0d1135480018051101d030b51003802980f560320b03a600d03021b142c10140f414064644a900c7c91840301501c0602580d2494230065503580c42443c28080090700c000c81c020000c20100c002050b140780144800c2503150100c036003003040056a9215240100c401c221550410011440740383c0c4401d0b48850300040b06a968095907441c000d017442c1c440003100554043e04c4503591400d0020100b000807414402c13600f500400e0800d6000d140951001b48100140c101f0f114400c1a19141e00801c031091b5010220f401b44000210050800c03858265a04500c0c002075080990401500b184240304010f05103203080200f11103201d50381c0303500d501880c0855480d40015071259060140169013289610000f4440c002e44505038418941242416000ca4298100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 30167226 1250 30165976 30165979
    0xf03020907171b071505040302060c0a050414031006060507051002070c0603021605191a01060203031801020412060506190305070501050c0c040c0e0a080601050603040210030905071419030203060c09 87
    0x4202410001703490380114045655024404030796403034182006070501c2002006024004000c102e2100a158803030210b4080c3c60720b1001074080c0c4845480402e01c0c000810300b40071f00c858030701a40032904940010142c1107141c402c1d000c580d000e602411405d0280d0280c41b200030112001044144101802038024100020008200e4890310380d842d02c0d45441c28491001c0b00c2c0340c1c60109400c500a100d013082c682121841c80c40d031840b919502d094002552840028040e88800d481041d405841910a4040350010311036007103406400f12290804500a01013078402610680c44c03030514240b8540400500d03802c03642c0120192140c1c80c07400b0010345d880d5100c06910380603030046001d250000d031b503188103072214642c05035a0001d061445e00305120f28003925030000d211692248004120540d58401100c0c1c4c0942d0580d020b5401c072259400a030007800c5504001880c602826101240700d001070700040c0d840c40c1084507003401e490301c454201803034015a400040d4240d0401030000b42218112401441e10020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 30168476 1250 30167226 30167281
    0xe12031905012301020309060a03110f072102010c09060302090a0b0d050a0b0123090a09020a0e01030c05040501080411060912010e070509060907030c020c04060f0302090717 76
    0x3980e000c1412100260003080003028803410018a1030103c561100b0028000c1c0015031600341e18800180f01760003820b01600c10191a21a0010181d02c90000c2c0d940b2080340016082c1c84000c2480c5c03804200c5090142c40300050540381c0b200c51098814000e0402c00300464130303000c0c01e4078201281140a54060f42c0813075004505c24200003406240b820044c18110700300c50b0f00041604068280c1030585001d055801d04010202c00340380242008002420248200060307116a15180200802c0c602c0f0075030750080709001d2000c41c0910750f0603044102200380407c266420800d0480482096039540a81d01540780022030034000500020280d245094980c01d00808440c02c102d5080300156901a003200b1295242c1d46802c5d42030400d020400c9a007000c0c0204942c0c002146c60003602040c0741540080c102c0007055160405903468600034888500c62480c081c00174805280c54103843d00051840b480100c1c09a80c2c0708000481e000d101e4103403d94245018070148099440310079045d18010444806110b0142 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 30169726 1250 30168476 30168511
    0xc02090f06150a03050a0b01080c04120f0b01030f020102070501080114040504050a050105010b0406030e010b18040c0905100524040611100609090605060f030d1b140604150e1203 78
    0x1420b07200507090740700302d641d00800d0500e410f8441d4803d4a1101d0070301030601070a40300340051b8403494004d0b036068440c412102031800855082c010b13041444854054500111500003005000c40403280c201030314000c1c0c08588809550707500450300ba610034031548581c1c5401080807104c514007500301c00d03005405082200d000e00c8603501c2e03003800c581c0203030f12400410344005420420b240e05405159003000d5590000c112001401c804505000c0b50f960f19030620441c000006000c10401c03045040103030204403020401031500726a0301c0316445060051900c200a004156810401a1724490b42c055011050385030815103410b209031032500d05e03e0b43c103117800e0040980400e1000c1c043d11401c2c0080c140e074040480c412001d4200002260300203080207010f1100b003e480b9907a901d0024092055800c076203000d503a03541c015108000026040340c0700511091120080c546046800691a0f001c5e6008048002c00f0400c1546d10004554007140a441c0c550013071440e0b2014504000081c1d0780c0f042c0e10041c2d01c2e5100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 30170976 1250 30169726 30169759
    0x90c09050310050709090c091203200601060215060a06050f2206090b0702011403100306050405030307020c0a0e040f060b100c0506070e0105090603090a02030d03020a0305070c02090f06 81
    0x8012181040c456586804120504d81e1002061004240f00801048840c0f804400148141c50030300508451500c140c00c40010144180405104400c0031030140201e0040e10a00b640c642c00288140e900503c03c1562a802600103140361501684008101b070080d18079000080d0358a4102030000074052106000304154041442d2407005010003c1842881d514100710019092504a40107100184018011940180d0b04642a100f0102841064a0316580c030504011001041c5400041015040005200c00c005001001e9030140364681c09862255400b0814441002414803880001001940108022801a412040c000c5000d56004600b40046801081030703440128400c3c0d0000e2402c84400d8140b04c02031150a40100c0d5a1030540d081102c0f40700020030074014110f1151084d9000404140c107008104049402540d025082d070b03810307000001c8050000d400c0700c1c8206000c01d04080c00145030074400c1c02c0c03c0780c415600603c2480182c0303840c8600888880010940342d04070b002d901000e4580c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 30172226 1250 30170976 30170983
    0x902060a020601030203070b040b0d05090c0d060f110309060106080406061508060907050a2c04090804080c09060d0308060a180603060b060301050a0e041106030103080702041b09090c090503 83
    0x354100d580007481103514602c18149000151741c044075101001744002d1280c1038450741101c04241380b4220100d00c0303484540f9100e05010382c4601d40c941c0820790700921030410500f81c01c0106c2021180504120601040c00314041d01e1004a4421140d41c1003040180f1038a4055408560072a00600000409a4540030741141e540d0440030300401041003001080400d2a0a4081d00d0707010b09186406820164000c001504407241401d0780360000c01034200351081220368010381c251803c0700410900038503410f8105040380c1e50144c012440035004038260034500e81041340c0c00c0760141202900101002105450480d1403d01c0a040300394010801680090710700340201e204183c0203543c04c0d0018520345107240030004c482001e408507020380414001080103a0703c140c40001104e051124004c041c0c0e85603d001c59000001c200b19550001c0c0200010080c4044840581101d91081e202000941c1c0001210444240e500340c1403000501380f120284110303212504840b070900f109081002d49240c8400c006403e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 30173476 1250 30172226 30172237
    0x10080d03060806090715051b0303010b0c07060207031527060c09050d231218120105040f02040e030c010912030c0503010303050f090d0501020d150f08070504050901090206 75
    0x20745424060010301c400740140c94003c0003180042901d03510703207016581084000c119000a001011610b42890420f0035110b0b40c0b20b40d60a001d0340e5a0b580c4451090300c55800030211461288070f90403010503003030700008000c0b069941010304107200018520340c000240a80683d58401c8040c5a615040b03250f0300e040940010074070402000c03c268807031240040c01071046a00c607a200c1c100883c41c560102d91001d01485c0d00b04506448040800c601501c45890000ca1000e8010070040014101c0f4000e26000c2c61491b01240032544000008030b00d0008600340c90080d03a000d040340000312004401450b00c1c0c0c0c8116410020030042e00c0c10040c0660300c650071140b1004058805440619883d404540e1510400c0105105400c2082c15075045840040460140680380810180000740345041d0b950340e61200c003a1944c2c0000203650780e1150034401e0000d48046000c40c203081d100d0b944082a001d03560852801030300e403104c0007054110700c3c000402003e0310018228500d25581c802c15403001d40c403030800404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 30174726 1250 30173476 30173503
    0x326060625030906030e030f0301050607050c0a030506010602160b16020a050d080d0f02030c1b070b03090102071104020a0c080904060306051303020d0e010507030309110306070201060e0a0c020c0105031008 90
    0xa41c3d01d413034598003a0541d032280c806000140c004000c2c410b114100c03041900d042d240d0640c0c8981d140c1c80a403401c00c1ca8000254552948110003040000c10000e00182701e9060741c1d095401d6807020460320401a41060181c0120030540303105001c52050a0b200c001c00b0701e00e01d8002884802d2480e03030b80000c2004e55103c140c05035502d41000580284241940c0903081d500c0e03010650851441c5040c2107403010350702658001c00040d216190304100d81220800c07501e409000885442a941e041c1100c259000b03500502c1c0450f140715403049640d4583c40c291003569854005520307041c0034000c9643c3d480020307a10254240c0d40c09035403541e000c40401c00034071605203d107455814a550000c03450034080d1606040d44021010040f843c0ca40f80d07203599218080d2000c0d198141404103101d0017510381350600301d417054243c0383c1502c540360030403e03150f9054000c24101c400d8208000d01a40b40c000c18030007900c00b441d10800140c0d00156168605521070b0000b158414480c448a4003400d45a0500e1401d0900c44030b05113 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 30175976 1250 30174726 30174737
    0x103080a090e07020322030b01030209040804150806040f09020303030c072103021b01020a09140105071208060a05090903180d0c0b07020114090d020f040b03060a09032606062503 78
    0x2503001c080c09800d84182c4581c054103407001607d107941c1c2c5041c0800500000740115084004501081110400d4402a021056903c0d003c032041041c001c00034442201c1441c800d508001d006d040005051245c0d408180c1c000c0d02947c5140d880c9040c540c4c940e03101500407a01d03403000b0752607004000000c0c1e2605004074081e94016075281440120590100c01d5101d10b41c450340d104102101800e81c010022800b210050322140c500c40c400d440069a49002d0100c015081c0c0b451000c44191701544400c071507104d140110b91040b030716601c1d1801d00c14502c0003180e50312075070780c02002449404048500a41a4500f00402c05c1080f00d56517640d02c04400900d9120141800004c40e1400841d0f8104d5806d00b51030301c00c501e1240c04c24501e100001d15882d50801e01901807803844000c2d4245803100d41003c2d01030080641120980d08040024100038a2030240690010f03402c03507003805240c10b460402c00c1102c80c0a0221824580f207400400080390b100002288441589425101c0d2058120201c500d8090003900c58 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 30177226 1250 30175976 30175987
    0x5010e0703062003070e060904050f06040c1416020d0f080c0d030b01020a0b0703020d0e0f010c03050402060406110c0907020303070201050c19120608060f0a0b0102060f0103080a090e070203 83
    0x980a0360350101c402010311100485240c44611a0004d0320f074001d440d8035020748565007410104000f440f410444507041401e1404104042214014041c060f0405036001c00a00103040c40c1110b18a4550200d644400410440c0b40031400c1c0c3c01c04402c440c6400281000d40180e03441c2c0e24006e64002c0c044007180e66120101d17600b50f040100b07202c0400300c2c1e0b103a03060512189505400003900c6540e0410001e04081e0300c0408203807003d11990681e110762000364010070200580b0901c1d1561004103680182c0d0341d40c01e001c81c08600500c84e000f00ea0007154041c0c1040e0400703040c10025104010079200410652107140110f601c40d540f25030000d4010308441c1c001e1950f078109008000c3c217448000b0712641001c0001c029042c20140020a03400f0301d08003914101d070ba04007507842c0b004042c0001fa40688003d1051505004c0d5202500a0044c02038011a0041203080a07034001640ca0390001c45011081c603c13102d00410101300303014003c2180e0341ca940790990405881d001c0752003415105454000c010303440400c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 30178476 1250 30177226 30177233
    0x60d0603050a06050601020a0309060309060f050a0213050a0e0f04052d0c0111030d020c0307051006060f0e0d06090602120411010912050303010501030e07030b0403020303060901120b07031805010e0703 88
    0x40e8a8201a01f0300c05080480803584003d04000307940e2207010101a960001031041c03100c0d5600542045a00b50f40610a90900d140c0000107900701540c40c5101840d14080001c95281100000c4115003042c100031207150303a428102001c80308000d20036906800307951001c002503401010603002240211140f07458426421080a01d804220070703034207040c04550800180c000c100003081d40c1c0e220a1800015a8408800104505501900000809078030a030b500c0340440443da5046842031b80d81c1d59881409455030300e8400c075240c03183c4030b400b1900010444001d801046040e000f42440500400e0003603d400c0c0c2c80200380041c0e40341203909441d8030300000103030025076a11041003402031541d448008801f0041d500c0700ca4607480103125950626030f54984e8100800406e00c1103500079500b00c0340c10f03400d525245c10065101ea2084402500c02c6039032600104134103004800c4003507000c0c0c21402c1c0094554444034140c0042c0890062000b00f42c084074070f0300e000241d007401000b880425007400380400c2c514518 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 30179726 1250 30178476 30178481
    0xb190e0a0c0c050a320102030906060904030c1502070f0f02011b021e0f03070305010c0210062301180305071a090102120702010314070c0c0602010216030509060d0603050a06 76
    0x4078140300300808a0400d201103940003030321100d41ca400071422240c0e9007200080541d00c0d400000c031145000d01810a040e0005010360241d481a60008162800342c1c3e1201d0803c0504101200c006001c078007600f0140380810914034800c040030070072400c01481c06201d92100c1c1400c8400c20300480350003c04804000c11540d00c01200a00e240c500c0c0400700f40c83c1001d900080c0d00d0503100944003654298400786050340e60b540000186c4150b40078081c0c84e142d5840c0e00306075019150000c03028004d07208400f00d04000030b01900c180760899404181402d0792100802d0a039060610744110103041050074164668007402d840c050400135881203000b84042442c000c0c0510b40c90500407e40c00948800780712402040e60049030841c480480801c01589d03c08080c03005074020080030b0180ca400d89100c0c000c0200749600b0203000e031001d42c003890103c00e1166035034400300e09038030801d8031010392500b8140300500000c2c05a8050420030900a0080341080a082c50a02c2168001c3d802521150310844241042c0a0b452 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 30180976 1250 30179726 30179741
    0xc0c03052a031902010c0914060405060a0507061104050607030e03070506040602010b1509090106050d09060f14060d080f090f040e0105010513020408060106080717070e130612060b190e0a 82
    0x180000c0c0003001b00c00d4030103440401d4904c0790030b540094100040c2e200c2c2d55a18216405400001d104035103645250000609942280e4012030303d2504d03203110151400c1c54541030300e045840091185107805003d0750b040b01e84142c20802c0503054804c0d000003044595030b0502030b0000c0e03c2c0d035034000114a03000d401001404500380c1020080c141003045201e085031519903050341590350b2404c1036a611801210b020008202e90300d03010b4170301407400810888405840c2c02558950241c80103034005602e400e0f0401c18144180f01300240340704401c001c078020322000794001c0c2015640c01081032407090049400300b01540c0802610b901165500c00045c4541d252085104c429050311903011810503003820700c2ca5550b560113001d800140108040080c041d6407085004c01c645400c808803810007400c022a020b07212000f41603100707100b0300b21401130500b100f4980c4108000c85130b00740310b100c0201d6130f143c03150f000504000e140702e138208005c4a202c95030901e200894030000c041e20b00c0e01c1242464070b0381c1c06074220b801d031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 30182226 1250 30180976 30181027
    0x3020c07120f0b0402060d02030f04140c0f01080903070602030103050706020610030b07080c0f070c0e060103090308010308160b010605030105150f031801021c09020301050a0c0c03052a03 82
    0x21103515801040c6a1a000340b2010781c40701240e03205807240c2c00044c132540650002200854000010000d20800f08210a03025078440c0b08060140f81103200c0b545d4507044143c01c1d56402c00c01000c52030006600c50040039400030085416031745401440c0d100d2078180d0380240c0050303880b07078442d64041002507030401656612050b488104c610450031a9070301c400b01100a031032101004440b0f030104400c0d075402011981903042c1000443e607035a041d4604030011100512500a11080410000360594041d0090200d07a90b4940d9401f0220380c02c550310882d03150083c003e0501003005410303811000480b507650050180c62240c5400e502c03503240c1010400c01c014400d030100d070600424406090400381000c00d403a00309402900d0000400e5003030b6551402401741c4002c148410300c01e2004020700110b41d44c0000e8119000394002c0c85240c3d503614110095038000080c0000040c1104036041c0828400d0f0081c00305032107160034014050240b000317807201004d10221307292655000083c3c10442514003840b04541c0000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 30183476 1250 30182226 30182249
    0x70203030402010c06020904060f120b060402030c070602071406010816080d0504270f0f060b16080703030b030a0c0e0708070801120206040302060d0b03070927060b090703020c07 78
    0x505500084c004500141c00070603c640100e2840410713904c5811400207030904240b0505400d554107035100c500b83c045941940d00c070b548580856014101130003164801e080303070001541740800300d5850350021341c8400400e9944a50280f15400400b40501090b03000380756200003005009041200500d00c040c155000c6211a171000a0700714200c2e0300481583c00701e481400300c03034450360741044141c005000103130031140002d0300d0172050320145003003688149060f14410104201aa4485528490350320500e4000320070740c0310f03085d285030008203454010304080d032091034085060005000440d1500d0701d4030400310303003d40d003000c0b05000d4460418140c542c041d07414a421140c03801c250300d010b00341002c180500380460341c0542048083d511280e08440044d9400f038003042d1740b249140002d030f001300201c415442c480d000c1d02a000410401a01526584d045a0030361040780036202440e042d8980e850390000ca44842e200c00c00d5036255594264a07500c0f40c0456203001d0780c0d4040b040d540c03c2c203007030311030300040803106 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 30184726 1250 30183476 30183481
    0x30a0506030601060e0a05090c0c010e07080c030106030c0b070f0f0605040b0c0306090403110f060a1d030406051c0b031b030705040e031603050c03040803190801050f040c050c0d1707020303 83
    0x80e03829080208561080d148d0300741d15100d200d003000311031146102e0070b1855802c1c22009440c040e40000c1d00c600b180c0c442030684031030300744c04000c240c240c421602c0060164404450140010003003800180b41003849100380c100440103079070f030786102d60464690942c0c0155071081040180b007101d400b41a8001e1800c5491440c5142190004441d10405400601003040031140c100e9a083c0800130310005600000c00c0b9451071078484660340151115440d80140c0345004103600e01ca84030000103650941e1714a841e10390424030a043d0450000d40c410308940e1070151100460b01d59030300c2c140003142c210701480e51750701c82c8500010103040c1b904403070780d102a000e203103400300c0c450805d0030210544000100b5220383c1801480c060908407a24080d1050401e0300b400300260014050100000400744028030f0141030940800213101580d4800c0d09200b950b8000c0712400b4a600a0301c5d00c1c0d48800220032903800e005081030710002c0386c14a0018010484404a0980c0e0380c1c0502d426450b06c01594000d183e44011407551 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 30185976 1250 30184726 30184729
    0x80f06060d050603030c0712051504050727020301090504031106090a020418050706080109050f010e01091805030d060512070b070206070309050d080a110d09050f0f0402030a0506030601060e 83
    0x1071040120088005549402055099070140222500c0810180884111645881840b50210110003040302c0c43e100b42c01041c0005160307a40018429a04480a4440a8507000c1c2c0c589009149503410001e0300d0760f03054030300301c804901d10240d40600002040080c1da80791a1034080c251000c8090703034100e25400740301002043ea500050691041e03505450104458040303030300707a050104d186003008215006008010400c2544a8603a60407203460181c244416155000702003840d240a01480e900306c540b0301d0040c001c82c22241c2118440f00c904101c00040451161552400c40e082118a044580d450300270410603490f100c82c801d01807400401c080c0c03010500e888043c1c5503504c80c3c000000e0091002281240c203050207640b400d801014007420445401d007242c640000c0345d81c00388072010049501d541980c01241c1001803881350041792070702d498800c2c0741040100404048460388035030380045603070f01220781900c490000d14055440c035500815203042003000c1500344170058011000b00150041d803000c89 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 30187226 1250 30185976 30185989
    0x507021b0a15050d020708091306050904030509031608100b030309030604020103150e09030706050703051005040e0f0f1506011d06090406030210020a030801150801090b040e0a0b040201080f06 84
    0x4581040c00107110440b18244151040e00840000300c031140c0c4045200002e00001c1c10082c841ca010469034815229010368132801194014002c8030b130041003032000038000034010780013000d8506000b400c07581612403d40160040c14910341101d0041e400c000c414100031021801107900a01003200a94140002c6101180c1d854800410290425449643d8900200101505100a815606401e08135440d044007940d03502c0d40b210004662a0340740000080308140710340700e060300654085a00301241341c038040400c07010b0094143c058800c1d01881c50081c06401c0d007007005080e8110400041c0c40e82004404101040c1d0500600340303814403d912420444006041c90b651022501c2107480c2ca46485094020030020021030300001c1d0403404000351400305940018030000a1446641c84a4150b0381354600312005691800c01c14010401c8a001440007505c10781085e1050702006d000000c07081d402004881c903114a510080d10748040520038001996440717444941d10030116074603a20107040c00c0e000f0560 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 30188476 1250 30187226 30187229
    0x20c06180d17030103060203010303090b040503030703030506030712050f0708070b0409020c2107020a0b040b0d1d030a050406080a060303050909040201030f0e0d020106091802150415030507021b0a 86
    0x128006144140041206944039099282c034a60100c0c1c1d107030341e120300e8000002e5000307020680106d90f00000006a60115508540503035101034055810034007a55002d50141201829296043c0550440450070702c9041c080503100901820041c0000420741301140d042c80603a41081c00e0b15044480e00b44501a881c1c000c660858140b0000144c1c2e81503171380c002a080103480b116190710702c80501c03004909142d00f28040d0004600884208041541d40c0740401c45500c0f4510510ba81d40300140701c040900510365005805003940003a1041c0b120501408090031680086480300200d10042814442d003984035030004c0c0d00074103050781049428115240a4241c0c090b0f02400c52180c54000005021a440383c0c001c02c0e940d8440290034840c0c4006010a40e13201c42d1004102e01c015840c0000001c0c2007240b5004149400c3e1102010f03520f204860307024424841540c40d014921010100000178854441444550350281c8070341d00000c1500706800024100a40109141d40007031842110500b180c1e10203441a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 30189726 1250 30188476 30188479
    0x50a0c08160c120c060b01020c0f15090907080f0a09020d08070303140a0b0f011b02040e15040302031308151503120c06040c0b0301030f030f0e04050a090201020c0618 73
    0x2401c402100003110448000b4200503c0c0360741c01c0034040801900070745007030784a5104150074810b90f108013004991390000845030641c040303020020703168141010500221b0307900710700c2029840c00d0503904c04150b252174165080700009402c00c082040041c0402d004541141461a05110030380540e00003503082c10b07a51001420350000010300208041c081c3c1e010340501c0800406190071071a00d120400000c09881207040d004144440d41101d039584901d4110340e0b010701d80c03013601d40110460340900005290301040e0341c05510820840c4c0509008260341e10340f0482c4a40d00840d039810102c5d1010440003131550095a855000d00e0705c18080c419840170255219519045024016001c00006440c2c4900f03520941d1510f40c0000e10110802004a011480b03940510f0307444000a07641c0e40002e0040c4024400503013040000c3c040d2900080c400c1d507504031b0410f400e01d04a0140040b080008044440030758a03440030342c0da61980c0a0071075805000c01e10030900100c407c642010100122440700700980840c45 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 30190976 1250 30189726 30189751
    0x80d05090402091f021e031e0a03060302061b12070201050702120c18040b0903090109090b03030d0513050c0103050c040504051e0709060e0d0c090504060b040f020706050a0c08 77
    0x880c03c50f1100340c62000c04560030801c00040e514881030103520340011880a0140c0c4507880c03542c0300820000021100949012240c55006c070000e84020400364000030720b0320040645402000025a40b46000790120041c0040c2c0040c000142c49100d500d0018060501e883c00c00c0c060141d040542e0300801034035406501500c61440340d00d070000c007260620700740541050340100c04540042c40d030b0180c0c40d01c40d84540c3c172a074007610780d5841d00e6500c83c0d90390007035129041c0045c820000500118009410010b500c8ca40034044a081c00d04964000b4150f40e802c1310540c03034040013416500140030080140515080c03081c01c04000b2810448045601c51180d03002d824007450700c68000c03605541c5040c5c440050103070503003000c4809080a001c000c1065540c2c0c418100040c0021204e0f41032454841c60410703290b5070003245143c81501d041121740107064002c2c42603c1d87d030380d504141c10382d43e20780340212803400300850001a511001440c08074111840a400c1754181482d141e241034a003900003800303136000711009101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 30192226 1250 30190976 30190987
    0x30305060307030b010b1c14040212071a0706050601090b1803030403060e0601060f110319030e0708060a0f0209030c01110307150518010c0f180902071506080d05090402 74
    0x12070720304603490f80010503030b8442c540001001d41c00c0034003078580304d04045a50300c00310b9070348184031054030410b400c45c1c546116140301050040c642040e0f000c035a0704040080d1a0902e558507500381d0fa10111041a000d880302c0003480c10104652845200e07405042424103240d00b6003000d44802e0f281c05034040c0b844034040402c0ea980516a0b0402c20380e0700075640041f0038040030302c0c80c0050980750340c82885070070080707108281c09894480c001c00d40e180c48500740b00000c5090040c84086400007800f000a04000e03d0390710b800115200b241400003101518801c0000c1040342083c01304a4201c98211401c541d9451060003540103940c0c0225443c51843d41c2440d0460020343d454009a044d88102c2d0701c000c090150440001201f034041e500000d01c100a4094030501070341c49405d03414203a600c0103401c3d200044050390b240a41030301030700c142c0b141c070792090540002031a240d08100d0101c1e40b102009450400c50f40341c1d02d103420324681c01203601a222000181082c3c0c10010406456405142d40701071045401152 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 30193476 1250 30192226 30192229
    0x40c020105101a0705030f04090e0f0d03020702040b060a020a030f0309080d0b01050f030a0609050105060f070201200f0601080c030a02100e012607030f02180f030a05011103090c03160303030506 85
    0x1944e01982d085026207507a00014140e45103240e0141c8180c0c1c1c411400d003c51130349449000704041c620301d10942c0181107400c3e42000704400070b602c4030f91b040b42c5c019036500c1510340a40311a40604140c1c100d607002441c0401c0c1c1d2b410041c00301040c4164080416090811810005101c141a180480b13028030303020444241e030b907005070340354010f020350701158a4000c03041101080554000104031103944000b0005a6203800c00d000d8184610760465190f08810060072006510900031f9179400d0380317480144445038801807899410510303401d104070541c0d4803010050040c01414803907110710020440040c184400e40b0390216451034100d45401d81403014400315003129034022085034207006000c840e40120b0064458982a0359681518564002854405652800c0e40184200d4858403407203441d5549546190080200c2c808582d841c541d014010a44420000b072400d0044a40050b80041155101d2900c2d5021034600f903625400a8441d601201614070818150b140c1035050b43e42510b00410f10359190720 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 30194726 1250 30193476 30193529
    0xc0b04060b060a0512010801050402090118060801020c030706060f0f170307060c080406051e06060c120c0705011404030c0603091a070504060306050609090f04151406040c02010510 79
    0x255a040b031400035a2558403075000009140000101c0c11070308559880f403070f1203822520101c07002508000c818005004852180c1c00c914821070b10a140420361507140c2e03a24500b0ba0308071a14005850740f011507002e040000b07a02035040944000d817034500d0320398507010042003017100074810440410680c807142e100d0844180304071040990481000d0103042e40b0b0001c001d1403214102c900341c80442c035040c0807502e10440036400804002061105000d941c03189410003040764002c1500007007038410304440f180c0c0e000030312004d04041104800504802c03840d2600242070030314011104040c01c4000c000134000a41c044004c10140e071030303c1c0790008440340207180440500d184c0e072583c2000000d8000810001c41e5002c40100240c81c0031341e81c1400308a64071070902ca024020070380b4050344950b00100080d0000f0300c000010750b00500230b544078411005a04003000880768046e24642036440481704001c3d840c14140a07540d440748072803000f0041ea2400c95039000e40e40c0014041c1948003d11025072500150303400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 30195976 1250 30194726 30194741
    0xf0a0504030c1205040f050103020304050703030e01090e0c070201020c010216211407061107030c030602030a09170c0d080103050a0b04030203040b0f04030c09020408120903100504060f05160c0b0406 87
    0x180f2010303d800c0083c01c016001e50442c0c0b0038000c4002035140007085030351007402941d0040b54800300400c00030781940d40c281c4031540b6044440d8100480f5020001d480c20a10380998011014071841c90350701d0b501c0d400028205088840841d056502640310300410300c941c045140b00b03c43e000306200a209030711080184144a24030405095100210502401101e000c20100100c07049903c030382c002564125403554559043d40310203001e071a1504c5e006c0002c00c03400d03002140c0c45501940001307100b24540c0e58507201e011a9a03100c0030041c8011035404508030003001041423003646800d10103103640c0341d80c0d074080c2e40711104800100030016201c08182010300800c02e5230041d003280d11800d07840e9400c4075600c06ca0340c1c01c544001d036441d081c204000920304503248203d1b403e581580025050b03d1602600b9030000d648074079809601032003080c00d030780120025442501c0c010351280d81d020440e0504d096140c0142c480282c048201c0e00c0c10f03404111440c40d00822040562544001100d84030342d08c5e810500000d000d607 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 30197226 1250 30195976 30195983
    0x2040605090f0601020706110d1409040204030c080d05040b16060905030c01140f04170c070f03060902010e0907200c09040308010807080712030c140d030b030c090f0a0504030c 77
    0x222000d002c1400011a80e951240c1000e900316441969680411070b408005510160f030301da0440c030400b9843c548680442940301c1000806a880c0520a01c04103089900036481503030815039109084c80001c4c0f003489111140504d0345000c0e03041a0a00c0400b452a220700149000ca0704030018007042048400c2c0c2114683c160400c040d40d0310b41120110a81c060208100003203201c684020009101e81e02030281c4500036500400007240140c0c420f0002c2205911550742c185c110b00c80c038800050800e1080c82080c015501c42d40020910740e0f081c1c80050040c14000328411700c00d20298080010342580030070000315582c1f0302c82c1e4060001e115480e00a00340801801419003006c281020003080c550021580c50403a14050102c560803940d640c070458441ca800d00039019469001a0b004002c6881403854180081c0203000d00c0c900d1541c04a20b00345010090141030001ca51034545840f0700c0c0c030f0284040254250247c6901010b40340001120501200081041980304d960360082418580b0030000195459407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 30198476 1250 30197226 30197239
    0x2010215090303060a06110c010e01110106061706041815020408010204080f240105060d02040b0c0714010c030206040209090a020a0308070606050a0b031602010213060512090102030f040f02040605 86
    0x41c62070506889500484413039025130340701000040c880c0d01c10022610080150405003008101d0880111001038441d01b0030307410040c60300303900d4028480078032928000701b602d42c4848903010220103440c043c00308000c01c0188500d14007032002c52042c62040c10401041d42c04800c5c454410383c484601d000074095600405825072010402051082c030000301042108094011110400c20303e00d486001c0c61044800c0503442081600104100d00307008002d40086c0010301005404c05865040800c400d40111814000c507901c03c3c4801c1021201007002d2041022003840c20108005072600c02942c0c4444c003801c000d019000243c0040d08200e0280080481558020007460a05545e820b210b48036030060001614040c0c9020000105850301e0001e081c100c40700440300310b0460b40c0d0810540055104a904401555002c03c040e400b0070034811549405400240c40d400c2e250600261589201c0900030007800b05684100140f107220901c0c1206c21794000e5015040e141c5034902440420b01400d03480d40803a81080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 30199726 1250 30198476 30198481
    0x1b060d0c020c0301060e130803060d06020703170a05090d05090d021f0318021309020a03020a0f03060609060501050403080d1407080f070201050609190e0601060503040c060503060604090902010215 86
    0x9030701044078807001004400a01445031100d00c00c0c003001354181c0c2d580848154424842c000200318001940d48100014141442d032081a282c0800342c2c1e2002d20102c0000d01c45c5406030741c901e0520244aa0440003208080219261044400380e071045850484801d0000100d15040380740e640d454036107086680500791103d02004141412503e403488800744000c24140031609c2d922000c071000341e50320190003c0a070900c00b03159511540081074204030903a0402d4101c01c2c0070016844044504000388042034940000780d2440c10000c0c200c54142d000790030010700b040c0040140c1c2c0c0e8420b0a030750070b59400918181da078a0991008130010701c4034560001c0010080f5041049145e0441c0307550327219005038560030020740d5800d00102e088810451301f296018444070086440c1d00002510403030200c41590b0b00045100040008138a092001d03804040061800000c0000b0058218000c000811050030030342d045003003c0b0001241401940100c88500c0d43e60140c40081da0320800420030038119040b0309204030b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 30200976 1250 30199726 30199751
    0x1017071b020a080609060915010302150904110d110910050a050c010501060903020f03011e0b040e06010e09071e05060d020f0d06050109080c010c0605040201140f04060305060907021b060d 82
    0x11307503046072420f400d40680d4001820083d1b0104201540120403410075800b03a0840d420044200c07100308000460000c107002030445603e55100b0703a0b110707201000a107070b190340e4a42e401d5019112000050199040140005c00607511600716410342100c0a08025880e00d1108100b12141d000d03101860000d0760808000040785a0000e40e0403060b80e0098684900407440d03401410300743c0300c50941c003407140c241002c191485100d09a000d0fa1200f0740040c4080f42d40078080001340d191600c280c000b03100506c1f0000a0141d0003504100303101c002c141c81a500c03441d070181e082e40300400d84060310610340562400546d60f078483c0d616504403154401c0700035500380c40d40c60500c4924010a2940140390100d40040000302d40d400c00001d1424200d030b01695000390420499507000301a041c081c000b2814820b144c2c0c0b0801c1401515809401c0240308280b00d40d450303500d0800e008058450140259004801d44000d0012081d4003240314910503d21190118208201601140952042c4052081030314a86041c07103010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 30202226 1250 30200976 30200983
    0xa0903020f060a0b030c010c031d01020f070f050a080601050306150d060903050703021204141309050d0503190605060a08040f02090108100e03030105180405010207020402030f04021017071b020a08 86
    0x1895001d8003102d01b95280381d001503415280c0c1c3c0501402048a000b12094288210140b000b0203903010310540303c4401403000c1d85ca2501d981a04580f01c0b10092031310038410ba00305a4917290042070000002c203403d52400300031a0b00c0d0400600004110a100342c0c03030917201d85801a40101681e4040401c0005005a0500504a40103040304034010f024005201105020b2481031b10180ca014240c3e0035058003a0800700031141c1c040c00144040710307440c4d00c5000c001c01c100303105805544285880d21a50380ca4001010401900f81200b80050246001400d2210b5103660003954100c66490030300ca1031076140c070706192410f1780b440318000307522100b18800420000d1000c1082c00c03014001850512483d07080014113600c9000902030320390000c2417081d481041300c2010000d59081401280014a04481034000c00c0030b9920032a11440c0d031107001e205210460500e041480903001c003520300248000c1602c5210010200080d0210082200039401c0303401c4180045603540c281c640c0103001a03880e5559090407601d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 30203476 1250 30202226 30202241
    0x51e0604031208070f0e120a0b01090914070308030c071b0b09030f070e062e020109030e010e0a0e100b030f0403110703050a0303020a120e06010f0504060308030a0903020f060a 77
    0x70b022102150001703006a1496001c1e10b050f48407111010360aa040c04401100d440450781c0c1482240e0b0b00c5008250b1248007140030300300c46500803418207aa81000c8043c1c2c00b07421502d0007681e0040f1070170000305600343c00396508810600d4400355295054100000040c00c0c7c8808040e0700920b80d000042d10500300f60060030050020303002e1b11156001220030303a80300c030080d205442c4545003004c00100c107442c180c41c0f05181c1000201004c011480403034034a0000080d003001c03000160b13655540e40b0341856002040251207400900c2e0035607156040b00d001c14194091485010031540c81000442d000a900341005009050a80c0344c00380c99141c203180101180b0740aa03000e4001c00c03915102c1018048002c170300c0c082a00d03001b1004288001250354102c0080d0b100429a2080101d4410301c0100040d0b9805400c182c0007101c40140322550410030f40d04641005940118803807031501e0360400005800201350303680041800750000c0c17407405a0505906102400c0d0941c030890080904121880085030312040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 30204726 1250 30203476 30203513
    0xe12060f010801020a0e13060312170c0301080a14030d020a2601030f080c0118050d0e04062303010902090f0406050105010f0c121106070e03010513020109051e060403 73
    0x11282d030b03141120b038200d10078011071000060407103942c0c54441c10501504401441c811000081c15a5240c40360101e44010344005400900c2c1805106903004540209070380004184010600d507502d01112170359201100c180040010078043d44010046005200390384140310100700542d03403441c1c0740200408008001c1240220204503444454078900964081410390380d00514481015449131211440e503004003084030709664a8640d401041203451010f00c072407500c554014812080f540c403000e0081e0b091804c045001e140352400c10030041014400365295012200245450f1101c1400800d01403c1c20045c043c1d0442507080510060000844101d480f580c00b500b8100301d0307a602d034001101c403c4a04010000003400c4100808041400714410900c8070f002402c04081d4a5000d07400a410040300710303130b820080b51103008000d11a080a024940c2d00c510042400b000d204217960000c1c000802601480e40221006095000030f010a00003890b120b0301700030061b80d1119501c1c90013600b07040d10001c011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 30205976 1250 30204726 30204751
    0x8040f0512010b01020322031e050105060414070f0e0a0602031c0605010504030213090f0b06040c08010803040b0a0908070e0709120b0f0a020904140601090506030103030f0806010e1206 81
    0x7800030000600c03400002c020164040c41c9883c0c00302000e01e61889014400e41d4244840401c0040040c8641010421504d040c4032180784184031401d001d030840340000c280a02890400d02c4040c512411001d05940c0941c107400c08120004c24245c040f240ca10480c54143d4100b10490000f207407842c0c0010180c0541d460906006050303400034010354003607a095101d5140031801c117102c140018900340440326410040a0000203d0311002d4807150103411413035030141c84101c2203405101c1281003d000716100090a41000d0400e94540724200e0b40ea8400c1c5d10401180013400b089a245041c419140714000b480302800301d03954641c854015800c0004191050b4000c03d8140300d000070314085029221840c1900034441c0d850076070345d82c44c10010390306000300701c10502c075420085000155280c0c42844d00d4103800303207000e002c585030400c005005440740342c00840c4110400e0004000095200701c02c28a00001c5180c10203191f10313040016100d0303032013101c0d100f6442640b1844070701540400050aa00c01c52440100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 30207226 1250 30205976 30205999
    0x151305030a0f020307170703030c11040504060e0708030a020a020d05010b090903030a0b0d0f03080403031d06060a0801020f0703030b180a0e010b010509010f14090405040503030a0c0e010e010f020a08040f05 90
    0x4c0b800186ca80004650303240e00516810070101c1c1c0110f03079a9110030b018456080c0f104003890000340072131703004640481e8699510700c151088540100300840c007501242c0004d515001403240065510078034100b009109100c01105402004402c0d0454250f00340c000d4a1640d590034415090368407a08215003043c003007460503000308810300d40b45030148001c503003111240301c941c0d11f0350710111a482c800820036018551104510b4a070480c01000311003000304c1da60003401d0541424001c1012050b0243d1000446a0040c46034401080c0f8080c201c5017420381c54280000c40048060100c0c283c100031384220800c01d030018040201103001c03600121018030a583c0204113400422006444a00441c041140011280030040c107805001d00d440507132003003c21009900388581c8000190544004540441d0150008000d01c40c040e03c2500851030981c2c0b10f030070b03c901400c0341e030400200304105010896040081c040740081809009200c900e202769001059282e483d9100c8091407410a1940b148a0081514590 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 30208476 1250 30207226 30207239
    0x60507020d0e040507090e09070f0e010303210e03030a022a1b010905120309031005040b070309020415030c050102121c09020a0b120114040b151305030a0f020307 71
    0x40403035400007503488035914800300006110003000c00a0242003400090303a00031843c1c14a01400c588074004420040c1511401c00c29030300c0d980f0318582e0000019801820040c4002a044031580c0030315401280d2802c0c503c0d840c00d9040703024202c0c00c0d881d04900e0000205200b52080c01e81c0050003042440801400d030310145841110200600c062254001e400904841002c641c002452003180401403401064054a50300001c2c00540200103003c0590f00010350510b190030180801c0c80c86441c01c98040200b880c00c0c0d2107180e03584034000c00701ea00b015a1254807004669555010501c0302c006113142c0d000b41a22807400c00d20b144018000c603405841102c120b000ca45410340111a410101004428205103514082401170714440c0000c80c0e2115041c0c00100b003815a08000e410070300e56070a080744079075141c244581800c10b42c0c5210540030350308040048038261070b580d0315079100341f0410789240e80c1e070301c80156001c0081c9150b40100c1c1e85401424030007801d02c0740311020350780d005008400741c0741030b10780da1365 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 30209726 1250 30208476 30208483
    0x91407050c0d030c020a05071d01050a140103050403200114010902160f030203090909010227030a0b04060f02040602100e010c020601030803040204090b01061101060f06050d051005060a020a06050702 87
    0x714080707641c0091911a1041d03c030f41c10203894040140102c4103042d081c1c2e6699030030144190480f160980307920007050000400051086c1c01400309071503080b852402c1904d5258046240f01c00c0d103061544420200d41014071600c010525602f50114013981810007800f075a01a24410030501144910200041040105c0b48229002041d80e400c1d8a003154080d035171043c82d0303140001815015400240210602601c900c2034151007031160500042e0b58444519820925444019029600d03917040360a01c0d4041d1000907207c03c1c000d0300030080041543d60b91070118040e00c1c0d040400f01c1081c2c00414000b5181c0e4000940c8035180c0503880c82840000003440c8868200da034040c1d08400103910a60040003c50105401190428001b501c0400e10108a485005005800380e00200000d855030381c009154403400e1003118060f04c02c4080481040d890008020158083c41c0c1c4841c0202e60f4840114860580900d01d210003000d01a025645511020901a4440308051015955213082c4000a0380d900e2020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 30210976 1250 30209726 30209737
    0xe0310020f040f090f0f0b0a12050f03070b01090c081303031a03030408030702010801141005030403020a0818010206130c0b090609030106060302070b010803040b2a0a0b010602160503060c0c03040b0409140705 91
    0x60258020180b80c040000001032110f01c06030340a0207102484c5030b50410334001070502d80d015100040c04c95240c061600700300c881f46400754042142500070f01c440c400454520060003605031402140006032810122003141400e080035500d44000600050f40c0b402c08409411824000d803175002d4240c0e81c2c1c400207100702d40004040c175808461003a40c07015690040010710f4015010b0b01c100c4002d20798645c0c448035035070301610304039031070031500d2100c42615030b8104110396001015480b9520110a01c0d91503034109841313801100d18030301d000303c3e10325150703201c51090b2108618010024000d69a80b9400a4000d503c108400d4814031200360010860100c000102c0317003211504074446140802d4460f903450030101d20210700c4154245441d044001204c200002e90202c0d00500410305154542000649008080d00443c406601070110400007580c01040c0c49602c22051280035580300ca00702d0f03c0c02d00310b1243d03400512242d0030100d4041802c4095601020316400c245503282501c1d1540403060b50b0785d0144 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 30212226 1250 30210976 30210979
    0x903040515070b01120210020118140f0102031603060605040e0a0209061909080d02070609050f0a1502030307030b01080412030b03010b06041d01060e0310020f040f090f0f0b 76
    0x8200400407414a41d2402094000e05030301c032030514406a544035207074502a0f11001c90101155010340952500c00408100c2030b9480c0020025194110800004541020001b816030f1001c5000304000e24400c1c4013040009546000856492034003098441030390006640e0070340002e2400d100403552602800868066483e120341c0140c46a6a882601c8003a45c0420b903042d80082050048824a603e2a51507804102c4240c803000702c0942044107c0349840c4900d03001004641c130520f0104081c640040442080e04d4050b02d10201844098000c102c200c0042e500c031149400750f000c5940c0c400c0c1c1d808400745004000e15a028070042ca0010011110b180b0b00f950041d1100c5408442c4c21410360003980890006240a00041103080d81c0034006207050b00306074060041c45045c00100c2d211071704540700c218050500d6062902580030220301090f03a07010060981441640e0004440d440e1004020680b00243780101300120b07a5500c40131020013410128022100300343c284031181d01c60b0112805000b050510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 30213476 1250 30212226 30212233
    0xe030a1a060904051f0603080a0c060b0609060901050f07050f0a0c0603050103080f0c010609060609030204060518010e07020a050a080918062b0b0f041704030b040b0402040e060405061e09 82
    0x1085c0500004490014006035038156841a0000018019001429400b9040c0e02d079008080400d050640542e1200d000b00380c80b071002041942820b40c1c406040d542590020b1074000d4550070101214141e52080b110050719512030414000040600040c841840324825041800c50701d030380b624141c0c1650028000206003610a00104030401c60510140c200b901d8032500100700155940700032401c03201c2603000308000a60b0100d0910560505000d418014030003541c0d58201500c000c141c071510b070b11040c0180c0c51040800804520314a1003000050007081c0c101050790340340c0d2a6450030440a91089002c3d50081181000c070240102010041a101d004007400746070001444641c0d0701d00c01443c08200d0b581070321200b06408003140f407610800e4481c80390300103029443c0c10942803041c0b400312071210701d00901008100030b200148407158110f41182c0d000d0b0140384c0545852001502909520058185612580003000140040050058003d58090a0794030030101c0764000143c0c02c800c01c40391000650b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 30214726 1250 30213476 30213493
    0x30603030703080c090a03030305060406170601030206030c0d020301151101150b0d021e07051603032f06241804020d11030a030306050a05101e0e030a1a06090405 71
    0x240116850f66020506107081071a0400d1600003d140c2041170304240c00013a5030310100310041c10310b40701d108041d01290018240682c1028500c6940d840d05000003400b440002c004100300c2c0381d03004259010a820480d0039500c030344e1a40b40d0400c5c5514071400ca200042c134a4840900d40030301c103119655414090200c8020120b003014120354066200114080245908000149903007691500c900d2035804601d000d25554603060821a02d00800d0a0010350090040c102c20000241c10001d0100700e41040700c0f1f1007421840807480d030403401e20005400e4005000c2c9004100402d4070421103007103220014201603030354248200a01000541c83d1110043c144e141c10003140151401100003d000781c490650003500105810109081c1000c82c031048012a03140c00c424421490a502c007038016042c141c4544c420080d410a000b0502020b400002c4401150b4006090005101d40c4120f000315401408440c54442039162800c40350361340403071813a040b02e02c20380411920b1400c0400c850040350080014040780 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 30215832 1106 30214726 30214733
    0xc120f0506180907120f0602040b0909010902040506070b090102091807080106020c010804060902010306081906050a0b010503160903020d0b04030206062202070c0504020f091002030306030307 84
    0x501410003003000740a00040c2070000c80b1041001c5150350b00c198141b0703000f81e0401d014090042400041c020403a13088010044c441a081500c1150460380d0740d00d14070049004038001d071580481c00304a2440270522801c10b054015210000040c60070f038030f6000280c000a07600d842910300107406402c008145422010581c0108881c1c0050301d0442590800209030840c000c5c030061245036917080710b1080d039100341c0c030600242001108440b400c6204104803d0620310300031084580c03a090a000800640d04d0b03000d4100c08040c182c49050a5403a80c5582c00e814100251a0a007000700451000016136112815400d25502644941d41c15003400c1c10001e050040080c01c0e14003030401d0303504c041181d0164841caa480140032100041c1c0394000c500d80041080f401d517000360703440341c004225420341c90a1361000300441c010403034507540100c90b40c80b0140c0c4c072030004440744c03a0306400520142c0e010 = true := by decide +kernel

theorem cover : BRFrame.Cov 30035976 30215832 := by
  have h0 := BRFrame.cov_init 30035976
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30035976 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 30035976 ≤ n) (h2 : n < 30215832) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
