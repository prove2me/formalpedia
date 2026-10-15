-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3942
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:07:29.028258+00:00
-- url     : https://prove2.me/submissions/0e9e4aa3-a044-4542-91ba-149f461bce51

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 708812949 ≤ n < 708992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 708814199 1250 708812949 708812957
    0xf03120e0c060c030903010f1506021b0f01110a06050f0a021e0d09140c0102010e030f1206010e1206070807050f0f070204090b071713051f0f1812030c 66
    0x202401d0034040e81d9800b080d001001400200106000c0b91000d0088030425000c0074400640689a90760404800a4a804c00c1c000c45d04203201c20940e00c0d03c02410b41c0c51a00003100c800d02c20400400051b50400707a034049071841030140759295020b00000d13a02c40343c4603000c14009840c4036076807040e00c2c0d02284201d000049400e4000241703150094806406004011a0f640002601310740a459041c50305c0c406076508a110b80c00b0074400325465a080c00b07101244818003000314100155424020795030701400c014007c104a1940c0040c0c0160b20840310841109005030180c0c0b542c4e40308a102c80e444a2007200c92030003140c0410042a011842070044510742444080c01c5800c04001280b8001036504c0400180da00648480e002c001141e58640c987d07005040541f15140c03000411401d507030340c140c0b0040550700400020050200440c0001c00c54050040f40201c00390320f00030740c02545c000104401040040010f15101c075800050034240708080310240100801c807904221403100300d06071020302041030002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 708815449 1250 708814199 708814213
    0x30215010f0509070305040303020405030f0c0a0503030307080a0c090b0a02011b090b07060b0307080111030f07090e0103020f010c0501020a170c04061e0c050a0b071d011e110a0f03120e 81
    0x30b17209500254200d0302c0b034900503181c240d9400c000b03882c1c04101c2c008078580d500328440047d03041c41c04440d183c008000c00c0d00994118500000080c100000040a060740342c1e07220850811440e100e18000d102505074590141e80780c03040300100a0007000a01140141440383e4800e41d109180559440c0c0f04440003103035198681012959140040c1c0341d0000307840e0701351103011004140d2581c00e0141c0e4a0080c1c006500e1516850581e045400d07120028289806214000c0818400c003120314000905580d01a5103482002d04800c0c0103c52440d05040d0240c42c3d5440800d64544c00ea91210420703500680391890000c090301e5038216501ca5110b14071a003c0861603c1440103512851030007a0300b2000c0441c104045070305002c4c0c90302d80c10031130341700400c5540818460800500d80d400c10704020307070180e0b02400461543c54840c0043d00e20484069200c0310400b640e43c101d00d941d44103030322078004071840754240c840d60241454036501c51a0a10402c40204088085c02c600325a0503104454400350390300c0040c445 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 708816699 1250 708815449 708815461
    0x20414040915180b010303020102070b1f060c022d03010f0506030d260c03061005071a06040b06120603010b01050a020a110d061b020c0f01081b04050d030215010f0509 73
    0x1440844049040300c0007103c0c0d000d0201d0040d850403030007107009400142c0c1e183c40500d40341303000f040b0041c040c2d0030003840c02550388a1102280965000d0300d1103820051542c0100d40002a003c3c1080705090303d450035580c1100440300b414401e4111001d406070001d100d03181080031b840c407e43c1c0c0e049480c0e43c0c01d0b601c172003054003881d031240c6403e50512580c00d081c000040c0f1060b146120074001103810b444115030000c240600c504000c1219441112203252490800c009541c94054040c5031003c0d0342120640400071490b141d41711b070710101d0049001490740d503aa52501c40e8070010300300110b4805101e5441c00d06d801c15154017030740468000c50280d5000c0c1c170003101c055507003a420180503803a480e00b121001c0c103440c0000b4080d104181d4000c1044c4d100c2c42c1c0d40124410002c0c130f070144007203455001714081100c24804c0d0340c01035262600300803c0104916041e150355030b0801c2a00483d80320f56030002500b140b8030141900400d90301c810502c0c04490700b100d0ba072610300800b102a8a803203041e410680799000592 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 708817949 1250 708816699 708816701
    0xb0a0207030519050a080c0f0d0b040e07030b040618020a0b07050c100305060306010f060f0311130b1b01050114092e0504050f060306131a0a020414040915 68
    0x4020710a08080d410301c443da6900d00380807103110340600c0124900041c602c00d1341e6080612194000c929401c0e0310f18007040a11108168059204224406038a810440d00f19544a40100000345070000c202d902d001c3d035030b003090503401c81c0c07d0b030f410b40d11503103410340d04c044550801102d0030105401500360017090746003240e40915903006102c2540c1e035024900c214416a07070f80c80130f1440c04040c5a6030100300d5003082420103060440680c001da64150f0710040402403150010380440c651170903414005100ea80349016000740340701d540b15038003400190001c0032401001d070038080c02c1c046841840c01240344010300400d80c2241e0f4280594200c0201400d1420000e181c5010281e51025400b47c0380030300010544030a51810301d411920a440c01d05074442030119007400e104060344072001002500e900d04142010a860300800f406c01200000d00904200038041b074001120107000b84100714945501e042c03038000c0d000f074016000c0e0110f110203d07004809145420b005030203400350014110b002180071408914 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 708819199 1250 708817949 708817957
    0x306010906081b070b010509130b07030902030709060b0a080c090307050f041b020d030b06092103040305060f1e1e151e0a0e010e0712020903030706150603090b0a02 72
    0x4203c0100c02d1800b0403600802000761400500c038540c4071200d94180002c108814000504007024041c444511002080d2240d001e00c1e0802c0c07450500141d03405050000c0f078101030742c68204030f0300941072020000c8c400d002c01000300001c82c015030ba00c0c400b0f07842d41d8185c501148541600d00741e16600000b0b00740910b01d040c0b1070f00f10710004020b00c009402c11200100a04000c0203196100141c2c00402003164001e0301070040465440302228003503c1d200c1b2080004a0003020101c24a9110151070302c5008a01020011030b0040c40d0808100d42e140c1c07a052078100a03400084608110480c50420401c00c50940d1400a9000d800c00d20305858410181280e0041058001043c21058100c0d03005d42811079112140380c891200000009058440c104070141700c020040f80d0301c84050526440c0040110a08441c001c0381c00c8045031904c11a14821000c03580064040c4082c02540350200141c40300030400c032540171461104040e80024485aa1400250200d55001030080e19409105000030244482c84d8020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 708820449 1250 708819199 708819211
    0x30c1704060f0f0f06030219052b1506061b2621040215040803070305130320041437050408270d15060302120d03060b030601090608 58
    0x30f481e00b4504040c0040d21020342c0410303907240d542d203400d00070341c02c09114070150902e462540c20681403414001c9900c110410074a401048104082511030401c0030605642c3e107030300845041400040d00d44101c00820880c484c03031011504404a543d007002c4030301401c0500a40200b100615210074001041440603c10701e424140c1001b080407150f41d0214500d0303012040c40184065a82e49058411310507a50b508060b240e1009805010070481103030000200c0c0c4c0307000c3c2e0520b883d6494040e62681c002da025242d401c02840d22121030903400007a912884a60b40605003220180012428108540304070041a00c0442610704213021840c00289441194155a480c0e11801c0044580328000b0300c003210405e5604881411001815000b4966240004505980e450401404808440000443d00303010090700418084145000c52003444003581302c0401140c01902d01d01102c4019a03940f901c408440c20990046407030500082004d40c00c100a4a10585060b154180e280c0d08080302500c40ba1402072070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 708821699 1250 708820449 708820451
    0x30308040201020c130e010f0902090c07031b0b090610050123120705070c170703020d050a06050103030e04150b161704060306050a05010206040b01170f060903030106030c1704060f 79
    0x4000c035192203113241c0111417500e482d00043d02007403007441c40d03007903802444002a8040c280901200980c1e85d00e13044070307000180f1944490b070320246031074190b503088804001c2655010340c8901d50021300803461000b40c4270742c2d00302050b240b20751b8030300c00b03524031401c40d501507580011413140030403004014424000492032400d003882810140409082007214204035102e03400220042581d80400080c0950750b0041d0000704c1c030003c01812440d48140c1d94241e1444040c1c03042d00d010b950942448418852802d0050f00404180803a40e1a410302800d11400c103441c2c6030140789440400c1045121801c40f044c16151021075291030b11501e106007004102c4c1400058801b1001e511302104100301207130040c4010a8542c5001c00d8151400c02045001005640400c0c1590810000c110024024401e503d06681943c6481ca04003460f20013224600019200600168455001400302c54207000015504907038032964203201000b94060115011042a16404a12a200c80100c0e00103411a0445108d140b12060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 708822949 1250 708821699 708821713
    0xe061518090c1321140c0a080a051f021b0c0901080106081504020414040c0614030c071704050613080705040903020d0e033a180911070c08100e1603030804020102 71
    0x17a411a980990001800319512a481c00d140c107050104003440201209009080c03000c01d1070700e0700ca446001c1036000ba011100c2aa00e0b40c0e2004007a0b42c103503031004402d030744440c103400c1d055010b03207555022202c16148101d480c0400002d007403105009003010b80d01035101400c2c5042440c4c4070b112403000007400882c1d005458280c0080030092044070f0503c12070045505029480c500354004d4000130240140d22051a410000c10002000407011180f03610342c8801d0001c3c406c0d043c40485091401076801190344038a00003102500c0300d42c1080008290b46081056580c0300d540c5004001c00c8030000c0348001e025812100c034150106000d145480703030f9100054180e030801c0e20002c1c4035510350070b00e09212103107800510302a41c0700521941c60400d84102d00741000d818042c1c829aa450b099002032080500b40343d15030311014103142c5180c094800c010341c0000030400081c2c030781c0c1c1429261000143c44010803440c0c00292a0003520028402e50307100c0016001c0c03c05142152401c5881ca0340041c0305906500c01c1f00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 708824199 1250 708822949 708822953
    0x70b0f07080d090c1e032003120315040e0a0c030312060f090c020d08060f060c0c0a03051c18050402090402070203120318060f010e061518090c1321 65
    0x7020740c03e5010b10070781c0340d50029802c0240245001c045142100e07845004840d0520000f1200080703a2482c0401d2011140c0c0c10310a000040d00e0704035002c41c5030005540c04001e001c240c2d0944050502d460400710b905100e0010507564465442180e00009403801460300020000701c1c2c083c041003030f040c4900001c0481c130b07692102d0b0200c03984503080c1d00810045075a2200c0102803907050060401e000315901d0700c1940e50803d507000403070748101c40da907040c4980800100c0075589181004443c00a4101401d010115075603400c02681f1041641420b10032004030007450f48840348242052980030b8031030145071100700c0c28030092100a41084030500c2d0001d42c00c00ca888090b980800501d0a034150030a01c255880c509075450107138104080313001200d1548170000340801e45d0046841b060544058000031207540d550b240014081125099001d0011500040c0458261010040110280000b95070049640c1c540921058180c0b1a107425100f04240500e41804402e0007100e81c40001c031038071141c00b41d011003c0d0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 708825449 1250 708824199 708824201
    0x1110020a120c0201120b0901091d0613032010090609050a060603050d11100b03010b0909030304032a02040c0e0a0e040507050f0d03030b0102100e01020a11070b0f07080d 74
    0x301072a0000b040c4505a080c00f19a0f000c0c0304412a4011200c080c4000d4400e4004070b01d80c04418003806401c243c079241b404074200c480c0803440038100001000c03211103092a0b03061a280c0c81c1d90700303c10350000d00d5181d04a9a00211100c417110700405160060a00c1c2e40710780e910300010b10341008202c800da41c5500c440c0000c940c0401c00c8240690180c80c1c00a001c1b0300d0351804d50300e02011608403000340240c01000700c5440d80d01148051150305204d90100e0a0f44041c000280103146401c42a50310140c51414000740d035000101030741c85a8402c0c1c4441c0f040c000004440300c82c40050300961450001448001c000509017a000320609000e541009020500c0110005268170701e01c0c0c01184955058004120500000f00031b0340d0300400040e2403c007211100000812107111224002909054552151101d01c0e4403c1000d104c1880c08030380d040000e0410305071a24080d40c0407401c0580010301400180070070000106058044900001c80302d480e0901c422580905078120800c140e490b16014481c803840348240f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 708826699 1250 708825449 708825473
    0x20d0c090506010f080915040807080a0c0501200412230c0109090605240906070c03030e090c0406230a1e05030105180408090d1b09091110020a 63
    0x3206102080c00d152240005244602c42e022103401c110088090140e80d050111340002165a0000d103140c15540e1030030032030b000d48a242e42c014a00301e00020701810851303004100c1025a8800d02c001e02c00500e0202040005120310a41403198400801041010704686140300100d00d01c2242d401c01790700d050140000004200752103080c0560410051041c1660340012240007424440008011003400c040220b8040d000100b0a42070b1341064002660071005d00788181c03180700d00010201a41c0304070074030f010035020880380310840218404548031140c0d45400d0300c102e44100c8240005030704180c640b07030b41101d06034034040450918941c480c420121340c0a0800003441130000c2c0c1c0c1c50300b40d0028503e11842c52030310103800d01c401c200441400103020701d6540c41182c04554040ba400d600d9070761928180b0301154899203040550090324030007001e0030004002d103c590045481c0802810060351401c510b0140e0799200c8000f00280010003074003d040c5448149034455856901c100c802c040505e03a03e40c0c00d2100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 708827949 1250 708826699 708826709
    0x1060e120a0311010e010203010b040b090a030b10030b06010203070b071b020d0606150f021002030c160501150603151e050d05010501051c020619120207030e15030108060112020d0c 79
    0x1000310b400d180c00f18024041d16860441a8000310300d190b01d41441002140a18050782c1500700000400c1c1c40c8594402d50500040c6401c01809103807400c09032000e41412045100484c1c2030280800013411540c004001d507840c4d00e8104030140455600e8410481d00203842d0540100c0074030800c03a02c00d0140e254008041c1c07540c2e108000000b00203041840e641c8121901142d04401c100030000140a441d40c0400c01c2c1940c2c1031000b40240c1c0702d848090716102d440c05610390480c500c180003c4c5502c103000054100401d1191001908a5101e0316050102c0070b42d41e02c80c07080b01c00a4041c0c14100000c0360000f00144524500c54051185251220b0015889180d00c10040c0c03007507074407040184010b1030002e03109040d80360201a2040584000c0c0d001c07624500075207120000d1000a200141100b0b070203640141c406100f0484115540c069915001e004038408020041c01a800d0321074080e00031031140203e80c140c500c660028003540e8a40f9071002d41d03580070114200e030000c4082524400044045d613144010704 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 708829199 1250 708827949 708827957
    0x120a08060a0806060d08070501021207021c0311070f0f0f0c060801060f0c031805060a03060303090b07081b01020f04090c020d170c0a1412010317040e01060e120a03 72
    0x1090036810400e80e040c8980140300250800c80c14088555580c00900e4103542c0c0c0100303a6900d88a00e400d080d80203008004082500d100c0d030404011209074040303042a04480c0f4255a00784003104200101e04035444244445100c4d46c0410200b004150700080e007128031f51080c1d0643e004540700390b0316003071040798241c012566645150418020144c010320454050141460300c8840c200c90054028103a00c071440018090094803200d503890513800040f035001400740500a244d1b40c0c0d904142c0140103004920090f40028401e48010507050560000c88881c103400c0b1900c1400c2c41106d612080741c0305920300501010759401c1209219400da080046c20003080884400290000c004102070705028001d0f02540400090304091090600e28241281d01b06221006058880400c20020780b121441d42001d11781c894408246444440b0114001318181d9100d0f285010a42c0301c3c0d0321040e400780c050382c00b0700a1240311010041c8030a61045450046401c030080c041c003d400032014056003007a281e844194006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 708830449 1250 708829199 708829201
    0x150412060203011805040b04030e01020a0203120c0f030702153604110c060708272104030503070f11060d060e091516020f102f030612120a08 62
    0x142c05244449007130a41d03013280c14002e501d015914084c00c00c400130300050500c054401d518040d41d10820900c041c05502808442c8150209001c0840c2d68005a506000c0d034801c5c2d40002440381000f00a071400164007800d8940703004400124200070350001000c038410a034000d26802c0c1e5110142c1302e61058035492000204411580c0024002510310641c06680350310400c10000008501c00140076030300680510b00301c2582e0701c0f03100ca0150580740d0383c04002445a4090500300c44448045008005450701401e4400303004070740c0040302240d000382c1c40f02038482c0c0c000b88201d0340466896207404075003c2c42403504019004000d0006403858020305e0294050540d106c82c1032003803240e04095140c0298000d4002c2121800d0612100f0120740c0090100000140c0d55080040d054003c21071400e082c145082520046041000c0d080008c01d2035070420002507540e070030794070881c110910364440b15900d514401e41c03855503101c05200d1080180c05040100e07219018519000e0300003074020304400143c580d2183e8071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 708831699 1250 708830449 708830459
    0x409060603050f0609041b05060f0d05100e0c0c0a0210080621070302060d0b0d0311060106360906080c13180b0c19090510081515041206020301 63
    0xc03610003c3c141c01030f182643d01401255030328000c01c0f40c0e0241d8007010b1040342080c040050b286160039580019085207021802030b0620440e64060880541074000c2080a95501c844041d515141c9105121181205002081d2411110001043c01e080f102d005c5403070129603540440c010b0240b061140001031950000d2004500c0c240e42c1980c0808090300c111100c1100040f10680c81c2c0102e448000c0c410080003400000010042d0030413007003a40004c10342c107400a424180581100c204500480d03807401000004a001c90103852008000d28654111007006101000300d41cbc02031a564201c80e030b41e20822440090840001c0c09200b001c1c00c1e22602620b004000c50f400d2264100e200c0090140042c01c100c1c07a160300369102a070a64941d41c000480300116112100100380a20a003087d92180740181e4240008035900a1000300849a080c0c40301380b4146001d09089400580503220740070b40414031091503200c1e03d490404200b0300820400071a240c56990403038490310f2100051b00301c5205401100400c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 708832949 1250 708831699 708831701
    0x1a15071b1e080f0c010e0d15140f010e0c04031e0b0108032221080c030d05010e06100f0e04142518030f080c100510080d02120a050f0409060603 63
    0x510542140003020410719540002e020b5090100c6c05501904640d00004280000c0e292003418030626200b0800c03040e078803c40f82400c21901103e402803601e21070800001c2e266440b20394035100720218900c16041504503501d85a0780c44061082108444014410101203224050928000c056401c025962402560300004d50306800c80d0328026201e1b0340c56410030400b039100200300f06610168030346110500c0c1a240017005401840742e500320702d100200707807010849041c0d8001c1d4103a840410050102c0d80d00c4034100150095400118000202006c04443c100e80c0100c004512a0500410104100034220110040c02c40129040e104500c0c020329048005840c494001401d081c0320300d040c041c01003c5101a42d508030f42da07c80204803801e18050a401d000c501d4059039002c0c0b04480964410703e600180902c040d0005841907103100518a00c0043d00c042d0000ea0f1075400c0490780c01500342e24030b445000c0701c2c10390022261070382813080030441001038161550060001e8100c01e280020034a0500100030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 708834199 1250 708832949 708832963
    0x503031c110702010903060e011803030f050c0f07030f03180609140102030c121f090c0908071a0c010e010e0d090602030f1b0709020d1a15071b1e08 65
    0x600c425002c105540241c1d91201c42081542d0b04084003049042c1425600d50042c018110014804403540d40301c00c04269068000f8200c0180c1e00d5070074412500c5150040017148284c82c003890094008011910000e800341c0c40c0510081e4440c00d0002e00c0701240c40d0320f1079810010038011142940d841c0580c404002c403005140e001203100300001c6082d460024016246841070444021940b001c02001a60760750000c003008402e0f0601020007140141d85c0e040c540c0c041d080070280340c00030420a00300032850a400080e0803040b074440c013107610084000200b1484840e480746410020075500e403403000d641c110702401001154440f03103000f454002c8040e8401050318510b508030390219001041020000882d0505880c1c1060b1405103654405005000052074181582c2c00a8100c03400400c1075008512958895500600250280e6142108103070401103009030380c07038044080710000e2017032a01044c42c0d0481d030b61072a0b400318590804242c88050700301418601a0f01402d041c03004240512500c4000e000c0e82c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 708835449 1250 708834199 708834221
    0x91e010b03091e0a05012d0b0a061d04020a0207030b0f040b151207170c010302030c03010902131815080a0f0b0907091a0f010c03050f03040c0503031c 66
    0x142181054220700341c891a50300b81c0300b000c189010b1074003c0700c55424806032030a5070b8810001c2040035151116141016510940d002c0032178101052403810a0380790080e1440c04400421420030a03044c102c0c252602c00031020802201441949a411642c5a078401041e150900e80c0040148500e949001c50044200414204044003040103120001d1803910005802c0000411100b50710400d00010542c0c0e918103003564036082c41072590008001170443e5200c400c002000d4180c07008030b038102005500f03900c0240d80c85c0003102010401000b81c2500b9034040c3c940074600c481900303401603544c3c05106907005000341280b0348907681c9880b96403410809000300000c202340d0f406001000c640b81c60302e800704100f00a0180c030b000c03104000590035040500c0040c0290891880c10088000344042003004681140500e90140003004e42d4130313207903601903081c4803841603150b0780c0c0c41c0ca0240700c48030069003500f01902c1200c90320b61101001c1034542d02803010381006043d125000c522120414034140640d0910b10703030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 708836699 1250 708835449 708835469
    0x2d14160506041215091a0106090501171b04030b09030d0612050a151b050c070602031303080a020106050a061206140102250819030305090313030609050c091e01 70
    0x403c812180c40e07880014142c0c111080d010103044e503640c20400751281c01700003021480c1408205250b241030890850607070300d060703403021905604c0d08019181c00b40402600400744000c100050324445070164602d02c643d0a4405c0c56003071580d01d039152180f5071420f4030415500d400106681c0307441d42e80c6225450051a88040d03401d400305039603d413152140c02c2c0020243ca100d6042c84150011890f680100050b003421601b0b00c40c80410a03c4000d086400242401c1881c0c045d540b00056540e20000c00e8a030440d0120907003503041495582e48441c264012000d0b031040d5525404002483e9035480300c0c10f4001d01e45a01d0b003e000f1194440c00900701c4001d90800102148222241d51440e640000e14203200482d42000d06000204503e11507400d103110360149060b84141c00c08100550852a034185032280319407000d00c55504c075055281d859000311088618034188100b0304001081c00c942040400d5070084041d902c001040901158020030110342c403404000c090010348107541c0c2c40b5400e490040035407181e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 708837949 1250 708836699 708836707
    0x4030503150f18041b17060a0b100507260c0d02070e010b0d0b040c21060506030408030c0c070801020406021009152003040c0905090a2d14160506 64
    0x6081c008203141c20b8400402400002410400062407103c0b10b0b4464881c104403807991034003c0f803120107440460070047d0182e9404100000224051035510b81c00c000c3c00782413080131120341210940c10401e81990541e0032100400103801142c61220681c4101240182d0f41d00c4041b0b407030034030341051a00d002007154003459040201c0090030b569241500d6104001540e00c3c95100d10a40c046d090140d441c0358003503c0c000000b00c0060b0070602203000c225910044150456602c40c0490231034041c2e1081540183c4108006000030342c0300300056502603a8042414107218901e4001b919200f02c82d0801300d5903270360019090054036010007040c580216644020f000500d1140e0798085541580c1c0d00f90504152079040c01741c0006840d4a1201340d84148518940d181d2030613042005850f502442141d0100d440c100124003826400b0590700d66141d00408020801c06080b00400094112080210808240d0354104400502c02e03c4e40c3d100980603500007400c10b09000c1806040440403680940e100d010108 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 708839199 1250 708837949 708837979
    0xe070e100207091e0216020411030403020a02090c190c05160609030f02041803170a0c0e2e030203041202011b0503040503091804140c0f12070803030403050315 70
    0x14008050b02c00c42d00000c035404d0b52810f143c82000c43c020044420f22070000c50440480d4000c0b001d07800029008480a01040c000e040c01038840748401d54019005030000800300340942801060503400101c6050007500c1d1120b002c44894512404000c46400140d4024024040c00400c028075185684900c9044080c14984031014005501a00c001410340c45101803100070f540d115484141d404161000342c4201c06040c3c5001813044086051208400c40110b01140d10500944110224104661600121000003e003004000c00d207000c000381c42480c01c050014084158200300c160380310003075100540c40e410540381a10348944181c41d80300071685003406c64a807818201d800790416a06600707280b5503a48603424042d00710304c200350016402000c59811864210041391381d407071042e030040c005580380076200f65086858228030401c0301d40c4585400f6041c02e191421500301182c080070201240c00c1c441d03517017042c503003140c004490590124202104101c1c83e040080d01144405a0884030403510362224 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 708840449 1250 708839199 708839203
    0x807050c040f0b030d0806062b0e01060b030c0c0a140a0309120309031518110906010207050609041a0d05010b2418040209180a0b0d080306010e0d0c0e070e1002 70
    0x445c10700d00401c000c4030301145035a110030084850080b0010340203038403000a10428015954646d0820305001d1400d4400c8104c0b403010720512090700c4980e210349c0c0c515100d5101d000f81580140070741500d0390040e5000d0800080c40c0e581c401044501e00d502605503240e041c00c001c0d1800da441c2d800011000c00b40184840000da110901034140c030350100154146160340365040380108421103894031882c401c41d48907020701901d80e0008050345004c41d001c18040d03544038012a19a07149100b020380220f0184210003c070320b0540c01a014440800c014120041030002c002512400c102c00203940c01d941d50b4085861390f00b00b2141c09034042d82d403078121030380910046100c10030b05c0c070400f4030240c40d2640598040d02c09540701d4044424206008000001c44020341242c2c3c44030550503905038078143d2400307440240c0342c101010703040c00140c1c201100c2030565030790f0001540d40702d240150880d80f202c10b940380030340000c001b410120007070b01200c001908185480c1c2c8025203d16134003030420b4410100121600002540 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 708841699 1250 708840449 708840463
    0x615040506030708130b0405070f0816060e01180b19080412050d0b030a030f18030201140304051e100c032a1b08090a0f03050613030c0807050c040f0b03 67
    0x70600d0806441c4d5a05e60280b02030106030074008020b03150480900c000d000001031a0000d407541c1d100419903550b620340c3c00e0356644a1000200c41c074001200030800000b8001c3c0c40743c403c0b66006040840f043c000301000c1d003044000d1500f000f407506070003040c0c99440c1c02642840c00a1110709052032102402d15440b102411504401e09108002001801c1d10303070201c841e00510103505025003141c0411005140c041c014030010300f00c00d0300040034a08a22881d0740000b000104481d0181c40b4080c1718140c0402c180c0781035200400c00d481c94482d40b001004901d04400c0d900030079030520030241110140901c20300c0141c1e110190f52404141c01d0100005208296650004a45a00c00f6410324000e000c000140c0710342011281d40c1800e504080d040318140a0b411000701003800044558801654403006000c03034003c0140005001c5038408000103407000b285001e0411540d01034100352580182a0b078603000707203911694084440f0342004200e40010b080034018041d00311001a0144004040800426541c900b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 708842949 1250 708841699 708841711
    0x906060706052d04030206090105100e0a06120c060801050f01080105060a0212161e0c1a0f1912060e0714090a060807170411040203040227061504050603 67
    0x7964001040845149074040320035040740442d001000c1000784003d460b070410864090303000d40550030000715060010300c2400c2c8110100c02c421380c00281082080907842074028078176400c840d5150381c0410202200400e40c04c0940c170420000300c4141c245807004060030780c103074001d5005411a116600e81070381c000c06464150761040d03400d00d4460013880c00032464a140f50580402c4007a0024141d0484040c1852005c0c840c0d001d042009005041d1906005130f403c0301050140400441c000103100d500007100424549040202d1128108001a5004905540140c025103850a0114408201143c000240290200840c6c200300880741c40c00c0c08010340d1110081050003000010b2800c4540030304203400796100000c018100e6402c0c191590340141c41322505503007100104040154860220596000e0684195400380031402820001c0e010302001c2e4001403c2282e00450701c90b42ca091708103c441c420b18030b0080c20340e03180c210740c10000144450205c180500c2c01c0002002c01c000c0c000b589900c001c40341c20007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 708844199 1250 708842949 708842951
    0x91a09040905010f090b060312030c120601090b03100905060607260d0e0109060e1c030902010c12020d20120331110a050919270c050906060706 63
    0x10071070789801401842c9101d400b150882c0b4242d80b00d014001c0c00e9098030b01c40c1000342c4c03c0b901d0303182108000c4003030384c00103c0d1680040181002043c007803010100c420364024406050880780c2c81c0d1603511aa80380d40088900ca103041050480c1003120b010b10b80121038000380281c44480c6890401d44402c03e00320517260142504030903480d1100400000c0108850302c4114000c400c0101100303400c019406820200000d541089c00c1c04141800708001040820b20502d420038001c2d82210042c0c1d0070347c054244108140d041c04140e00000022a10070440001e40a00c540d0240070a50448a4098918840c20600400c0e50854807906005606c00050100202d40301d861800d80700d5031101c82d031100d21411160854090142c07403122901c88618440b6444685220b481c6401c512040b04040c001c4000d030622503154005144030109541c040c400700c03580a810443c0002040d1007079100d0608403181512100500030002003c00181800303c9403605401800e01100c0d02446810184e001852500811402400d01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 708845449 1250 708844199 708844211
    0x130228050d0303021201211410020d0e061602070e0a02040807081501060e220f05090d080f010807051009050a060f0e0a030503031501030209031c091a0904 68
    0x994505024100280030041c440300140d1490328000780a50031400301450190a040c00114440703000307a0300c0414a101000204107141056185c0a00d201210030440106000b18008106240c403076000600d424a03c01b4004540445010360700da01e003180090851541c5844483c2ea2880e096003c01d4071803c0360603450f010841601c41e401e03201c000f8451a030110204d407003194030004800c000402c0b1040032920f081d071000101d03a40c42800341c2e0202e07800d002041d40000120f128507074414088802ca20510b2080c0c600044070300224000100311101600d000340745a100c003080700c0301940e0006080c0d034041c7c0102401e00040d4508a2519514044c0380212442801003412204809114400c1c40c030040c0002007641c200f41d0354583c0044d00c0514444c8001000424207510301d182030506240220803203503c100154a1981c9049242c200507500044142c1095020041d0341d14aa50401103160402c0e1140118403040700030150143c89030f00b5990124404800e0502a13620b40d0070714206440c408142564040b0320 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 708846699 1250 708845449 708845509
    0x130e030412150c120213150f020727020f0904050c03011415120601050d02031504050c07020904110103020904091406061801181119030e190221070e0a051302 69
    0x15094654005031304003100b0141c490210383d0b002400a0011109400750ac2d05561141c8410200e0241d80780181400802c8005018100215500602a55260902071b82c100950b420001c0c1c141c5000b80c643d05e81d2000048014090030b140c1032501244c818003150101e0403a00b540311441d455001e0031401a075010485000292140d01400440c1c80c105100a4119903e150846401071020320315441c8078061454000041da80d41462000c9600454004045031507681d542e550b40d60741101052242410182c0a00ca502c20a460301d00030540c1203841906094082c3e1113080b101c0b0315000c4000c0c4010b110701ca507140c020101d14403100866054a030710302000e004010444911401501c8200988c664400300010580036054800300340c20102d11080e40c0600000304c080c00403961b03a2008100d40000500400301c0f0000526041c01c0c0c10202d00c0d0004081550844400010f5003800716540c0010003541584042100407083c6200303e0b584a04c2002c0c00d5031441002d900400da0410001300c0c01e4844541034a01201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 708847949 1250 708846699 708846727
    0x30312011211030a0501020d0b060304330905100c030204030f031101090c2408013b01060c031103040f03060b01020703021009030507170309130e030412150c1202 71
    0xa50b40c50098116501c2c42c0d01c0e46840d070f00079400b070000728000b140b4110104844d031821001301c80c002c0780c04c0181015411420600201c0090405c00f015084040070440258114503501540358010702400107400b42c001c101c40000180c84d001d4017240b0807d031040109000290000c6e40916586405103020100f14054010607030047c50b06600240c03c0b0310a50b400011403030300c07145c2c16a806110240700654140c5a101c0e0a807486038003030058210214001051b900c48985040012101e4880200c00d01c4840c1464242100344260a8220600140385010f00c10241600504182c030348a40c070b800103615040c60b26000c00136202d66404000d1944c1d8840f6804681c903882003040760040c0d43c004045003042e12100c83c014003a074806102c1150039004003000010700a071200c1c40380310001c607804040d61034011102c08020039040c60159140300c0c1c90b41c0e220039186002040010b88042e0030300003071401c0300c080d50741450004071a070f4144c1e0107070450904541c0c501c25540844400721b1403006220142c0c49801c1c84410203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 708849199 1250 708847949 708847973
    0x503070203120c04441006030305190e0105070201030c051c0b10091d100b0309010203060a0e04050c15091e100f1425031107050303120112 61
    0x1d98002c0c4000d01940039801da0042c000c40b0134035016201e0004c0200c5205805540e100c0341d903041e80610400000300a5901c0c0145150320340010300382c0d0003100407030403004111415600150001600412100081c203e04143c51300c07101110b041c4050748640310400203101d44141000241056120041481e496005001303541031304245291640a105407810120010710100c80b0052007a089400500807040c0074441c810241c5030402280d0003440d201d10307000012500d0142c80400c3c0488404030005000d40e500010314024801c820000d0307074908114042002c04d0005802c000208070603003040c0000140005003048a0420030ba580c039240c80022201d451040c0034010207660454150b41c010b031001c051104504d001e4110480d148040780f00e0310030742151200c98255080c804100058600543d140c2c00401902903690154103095030001401c03260480000d51940c2203000c240600060030785094184584009000190000c5040502044031610744a0041c0325801120000d081d82006003c9000001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 708850449 1250 708849199 708849217
    0x601032322051c0e040608031e1201080f1c050307030e030d06090228020706030902061308030c12090f011b0803010f1e05010e010302090109080f151f060503070203 72
    0x51a00500003030864141641d901c20040c00013040800503588518040c4998010740e25481e000354103120400a0798008c900c0c005040e400c03c140188058880381003803c5545018142c004003800b444401c03590101e14290f0303420021803c00f160f0300e0300700c0c001903071004c107032035000d80f4030700d40400c0c000d0310f10301d645007540306a09444004a06200d404a40c181c0703140c0080800d00c000a2403608955032180058220414402201c0b0058011101c03c100c881d21981004403090300051407240b07021108a24005001c6842d0b2010119410206000900c0c05081c8000500300041443d004d02d002150700000740e850709110701040c14400101c615440e0b114901c80c200e51072540c40409a5904d5844610613040f010302c611a40a0186c04030381c014064a040801d0700d41260ba0684a1010645c0c0300300066019403ca0040c85040084044000650540401c415182d440681010740194800d101000d468094010700c1441701690f001020b00c0d0500c0501801030466403107143c840c2d02c94981100407420740c8166010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 708851699 1250 708850449 708850453
    0xe04030e21061618060804020d080f28080403090b0a02030f220f0b0304110d0f060b040b0118060315082406040510051e1206060103232205 61
    0x1004004030510b440ca4503404602c2d15038680c040d11302d842c0125450b540c0c0c080c460001c1c0554000c240103040141c50404401d10803002d00c4e04009890952041ca9006110810fa2110a904c1c0035440350030842003001c041d00440c03034890074514158402915618040c4540c0c10300180002d0341e10229803003881500c0c148200701460076501c0d08440741c080c0b00344c5d5110040311080c21034210000346c1c00c41e4600350f0004440c588090701381103a6990700d41c0c003642944c946105402c0221108840000f0f071040807580390b01842024001a505404070520081b168061603c82c1404080b0001602c0f110403228444200c804900c2d0100c1d041501c141c4104488601d41e11011303a510030302600b1001e400010070304081925005032081002d5403031204020a651054030021400d60400f081840a820080060507524003080300110451440d5008159594016103044000b5000f5506100f070b15030381800303242002c00c000705601302c1540e607070030b685002d40700e0141c50088a9505000440d02c101e010b10498100d003904202 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 708852949 1250 708851699 708851701
    0x21503060607050f0109210815010c02030d0f12022a0c1e01020d0e0904022107060314071103030f091221070908030a05070f0c0f0f0e04030e2106 64
    0x21300d81c0604264001100c030b080441400910018100904d0700341403081e40e484e4104d03a02c40740c2d0303170b01c1415401e03140007810413840700c4120b005600e0410490904408580d50711000007a802401441fa9507500840d40045004200f2400405108500c01c600d402c6007901c0b0204100031000564913251010751440d4000ea100403540a005034981e00e0a10305807401e80035580d01042600e0215030742c40207150380c01c2e03000c881d8002050150600c2d10281a000d4a80e5061b19440203419400ca03152919030b912880c0000d449081c0400380d00385542d541ca402c0192818001c8a8040301e0401d65203174000102601300c8610f16100207030200700100128150340c001084490740e07440c0010815041e10003403420407034001d03802c10003150a0340d208d13407d268103c400c07840142d800c0210711102291070b80d0003100c0035504651441820b101041140c02008000c050700324091400a181c001c1060300100241e02070740000140c50104400309401034480c04e49442e04844c0440c81d8040514070202c04081c840549500d849030704 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 708854199 1250 708852949 708852973
    0x20a0210114012080d20040812090a1a040e0112020405071805040c030f020f09010206070203041d0711010f020d060527061c0804030c09020702150306060705 69
    0x40307030210001d031a60424542c119001051100c2d849001c0c4140d01011402810000115030000d01400d03003951200c601107180030b811941d00744000d1001c0302d08a410300001030200001401040b00310024961081000e047c6030503000091380c0c00007644242100f201d1440301c2c0300c0641881e1030454024004943c00e940e400e503168050ba4580c2100350340704901aa01c0c08020481c02402880108035001e0100c20400d0300c81c1c00d100600001c3c0c202414280c0501d5250000e520188101d40090103000d0440341c0c44a0300c450740040020700e00070f0080c000c501950401c1005001b0700007461481c1c1d9220502c40300003212034843c81400c8421003c4e98031044543c3d441c1c80040701e0760402c3d503002000005004442404215114020041110141c02030f808400d4500c0b4480d402070030884a409500c00c4c4001c1c0742c150f01c0d01000300f180b500103120120880341440e00080c24820420811103600180441000031401d100681d80801d40075074402036480e09800c0003100041146d42d40380201c4032242d5004c000ea6142d90010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 708855449 1250 708854199 708854257
    0x301170f0601260a111003060302030a0503031f08060406020a170a0906060902120a0f1b08010e010e040816081b07050a060e0306010303141228020a021011 68
    0x1001240f0314000305046000708510000410303c2020b50845d000d40c0c03940345a80200441c140c0d1804100c8140344d03c5642c0000581da003880b140071118000c4020316500e00c0c0c40e003560200c01e203900115440010090350244411100055480c1d40658050f2006a44d4000c41d40c00780ca40000008840b66960906000c206114200d13400820308a4480d21043c8071042d240c1010030183d01400038120b20007032244002501c2907203a074002814001103540c00045000481d07a240c51034288034918140811055401080624500841c0e9801003014644989550800c0c0c1d8800d2114420414487d80051000040d5014805c004040320764011000b500c00c2590300040c00c0c210b847d030415101d41403248461400001e041e90041180f0303000351000401620341a82540d509442c203c00b12082c01c81250f100b4000e00c0704081390b100c00300f4010f60303032840000900020284041e440325800d100b4903540d01c3c0148051610a500010b06800c015070040000c22030314042603043d01c441c0035040da9900480030652445014001c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 708856699 1250 708855449 708855479
    0x4080d02030a0b0f150703230403050d0e09011d102120090f0405011b0305060f0123090d080a03050103020a0906151d0406170d0c080301170f0601 64
    0x100b07490411010802c4d8003040481d6103410f1803c080d24000704001d80003e0700c511151910b4520301504003008504402411441d03130000e41007280c1c00e521001c0d907440c0042d0041710304202d82c0c104807625030b000d40c10585030030a032a103c0c0300d148020351309031000304010a88154110001d0b1030300d03030883d000d00c18050100d64440d415065040d1015200721281e12115015101d00c0c1a0100c00605140d15948031a60541510540248280c0305550385900c1c2ca00c2e103e07401c0e001075070812202e6070085414181842000322a8540140f01410300c2071074600319000701e2100c0001700d07410310810002c0e5140c510000100d8482c01107080020b080810008001841640503440181681d00965080d69080c0e102c5504501300d80ba94040c80014040c4144024403041c4110b000b00071004428202184440e11000032070f084d41c2c601d4101680c0300c1c01012801a1002c0c0400c2401d9001c1550326014058000036168030300144411300038107030600350481a820b2864420840f290032081d20700c040b01c07100c1d030355400c11102d0300c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 708857949 1250 708856699 708856721
    0xe0306162309010c020105120c0d0507030b0906090a060315090c080d14090a0e0f041203020f22030506041b05040606021504020f0a09060510020607021504080d02030a 73
    0x40345401002940e45000003460004540d40c240351400c0c1c0301078011350300000c85a604904103c4100480d1403039423043c0900364011000c4006558a07050407440450a8981c0101982c04061038100c4149441c1da50b560728680240f41500c4401c1d5a803100d180d244064821034001401011a10500c070070b402503682d0196489a004200001c0816215009641c4444142c2c0c4040c00284c40a441c240d0044980380040003070f500020308010401d50f0700c2c0040820041c04545407036440c1d500804100074401d80c0e01441080b40801c0c60b04503e04011085404d131603001d00480c6030a40800c000c094030500c2c1c04459802e000d03541050803a640b40c60189403042120500081c42ca5030001005400181c1c1e040902448050f6200342d0094100c1e49404088020b504100a03c140da001d01d601540c2e0701e194803a0030313607103001d00324000c0041a85410f1009204101031b24803483d20456012030100500b2503404220030035506e034030038141c51a07a140c0703051004079409100d401001c1c0718400014001c064200f50300c0110004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 708859199 1250 708857949 708857957
    0x4050102191d010e150d0b0d06020c010f2003090f010e1b1c0602361801050f060a050c2a010f0f0e1302071101080a021903020a0e030616 60
    0x4403442004468884004040d517400c9510b0210807070403c21202d000e4107400d0401c3c080026800c401e480000c4010500c1107040d20140d50000d280300401c4000c0c0070703281403140d42c42d80a1002242d03600800550045c0f01c41c3d109400040800802d03400e49052003c07407242a26000244040b2a80089081e03c034809002660b5000707010340381440450402d89883c1c2e140100441d20341d40c88920350384038603020f940940002898000d00d09810442c0d240c3c5000703d00880e036400406010500003050521441c01851716400304000190340c0104030f01d580e500c0c1221600c1106a80558881d80810016503550140800a01c0790b4062105100c0540343c0707000d500c00c2040e12150200c5083c0c05840015a051040101e030384000070a0014070100b094094601c02e800e01c81c024144280e1101818104c40c200e0b0400c2008485800d41d00c00b00040c40d40c0d0000e882504601c904070118a00803803d81d94000c900b2000740c408041c07640220f003c901c1c26019414002031008080c1c1034694a20f022640340042d10041c0300144086 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 708860449 1250 708859199 708859247
    0x10060c0507120318061e0c11030708030a030605030c0d120912050105101707061409030604060f0506010f0c0b060d0b09010b1507050c0f150409090c0e07080a050405010219 75
    0x14840c02006d1102c001c15020f810611181e00c500b281d0402c03202000b41e4544840c5555040d40d91000c0241030014141d4002450b00c55800180090039203000ea40a140300398003881e070b0f1004907514000c0101c5440d6100c900c0300700d000c5400200b5203102030254444424141001010000d01406400461088a8900c60509102d40310b4400280440e40c04042001c150f008450500405024002115246003156a000d00f0401d48030000382c0b40000031a4100c840c00e442e10170b001d404201d980951030b0410000d082c411080394070024001c12640c540c11028152846003070105c1c415407111051f4400f201d40104201c1c0d02403604800090190803011002c0307000300d8403100c0d0281c10740c00f00c000382c0f5100c0360f000740540133048071582048500230301418038940c020408641040c40e000000c0c020401401c8004000c01c0c80d00c0f403402c05880c0c030519035109820b0b2800e003004000400d070b4003414150388010800c07000103582c2c4441c140540240a07103000c01c48801e05200e41d12079060b030054505954204545648050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 708861699 1250 708860449 708860459
    0x30901030612030507020d030905190e0606040605030f190e0a022e050309030c010203040f03020c030d0906031d0d0c140109020901060809150c0415030510060c0507120318 75
    0x10350b004a010740001c6040c0560070061410100d824120340c00392402c07080f000d032030b0000030355075502103500c0310340340b47d0ae411003084400f00030034038254080400c4134964102417403d000904688401005200c1ca440c5040c0003580000480000b01d8056906500410002d44820f0400e541d0b1310300d000050f40b1801c40454440362800c0c0040e00820000054101103124080c0550103a03859000905140041d00003480310030f0041d002413010350b01c00c80c080e908c0b1700b81c00c080342d0030003034181100504028040c3d0007a0706045106500000038004031344041c0350028804001d09a40c0d00a110514004000c50190001d840d0f40550300200191071140540c800491751642500f18500f221038111000390040401001045503038044d400c00c03a03200f103000b01a10175500f1400355185094000310b9000c00c1c500310201d401d010814240e0707902c441403480c50034100814101031021008071043c6214034070422480c6a1600300f005818448980200028070250311600c695160103001c08051806117040780d03450a500140d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 708862949 1250 708861699 708861719
    0x3030c170106050406050c0a0803040803100e07051b1c091502070e0106081305010606080f0c030603150c040e010b0a020f031801200a050a150b030c2106090309010306 73
    0x20482d10507031101482e1624200003600e0640091010080b6030080e940c41348045074014004520580c1329500b82e40e600c2c600103d01d00d0381d000d2280c01984c46800d40a00f0004002d4201d0b00711031100c03640b001d0984901d880c5603c1d01d440c00d28614102079152400c003111a503144e0b04446c0110a66103075242542024404c410100c1c3ea030710380c07842000c0482003801c004124041c014000c00d1341010301d00010310180c80d0680c0b2680d00b961401e51080001503c031604200c104c1c101d280758980c1049030300d200c0c18a503040140019507542000f550304941c502d00700c03010588210180088a004140c59070030300c40c2540c2d5035800358a442c0c1003081c00d040580074003240380d0003074000401250030311281680400c90301241400115480148101181c8126141d0f103940140001c08114134004144110010400086189030500002180c007000030400382c00d0002e03a1205540106660308201000d5500c8a25800280010314000e28888003104060003560103114203050003100500c0441c0e0280c81c1400382582d158070101c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 708864199 1250 708862949 708862951
    0x2062101140d2301020f120109050f130b1f030506091603081b0304030c090c030b040204060e0105160b01170d020304050108040f2123040b0921030703030c17 69
    0x100321403c001c4a200d909485084445106030380f1038001810100c0341e0740303000c607540c3c828211680041805070040203d0506401890344c800d42c0e415424a160814805009a00340c4003403000f041c041c0602c0000d03820000c400e8a142412031044a605200d0356642421500c8d044103960560160040c1c00803607007110316640060080f01c0d07225040340c0c41c0400403880320b12101e002064200c040c0c00108030000c04100c0100c000f0020b00724000703000400641c3e06074007808545044020385d00550051100300301e00c542102e107800503544c081c2421969035a030f51800e10407100f0105401440c0303280101c00828050400100f50903902000001c56921151554099a40b8002c41c030817180081c0340e200c0081c0c00240603500c2590340501c44c0100d803032103811b0021514403842a1f0108200000c0601041c050400c1960365040090100c0b15030350342ca424244952442540301d000da55500403101c1d11000741b500740c0e4034a20003003204801d50035280c49040030b02d0018003402154410000217070a0407504100010251019 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 708865449 1250 708864199 708864203
    0xe03010902060909040c2c13030504060309080403082a0102030405060403121b030b0a05090609061c06050a0906060644190509060408031302062101140d 67
    0x4904040700742082005020001704202c3c1d4804400c40001802d42c0f00f0590031104a40012548007018405182c0740c005000040000000c1014950340d080402c3e000400c0314156801482c01180503e2141021010f42c456a0700060443d417000603450800d4060b60101c4400400c0c21205c1144800c61300e607000d0a034001600d000d004c5811000110340001e018800000a81d50740310300202c0c0140c0c1000d07000c2240c021013030003013000c07070b89500c3c4031241460600c0c0b8102c00b404040740c075040300303041420100342085d0000b00258060000c007410420700c2c0319009600306001c3c2c1c0c030503006e02c032a152002d1510083d01c0311300d40c100c6850341850340c0440c84a007d4030030307074034240030480c440003100b44001c0400c0c04640e03c1050390a64450441304034072050b084444002e00ca2000c1d03031190340300341c51145840c4d41118001412394400350880350501000944100440782c2080c504080041041400d000041da20700c100c0b84d031410000600a10b5034042d803035155445040742c0c1c61201084010034907100f4050b10440e41040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 708866699 1250 708865449 708865459
    0xf030106091a18011e09050f01111b040e0a06060306050c03040f203304060230040603054014030a090f08070f0501030f09020a0f060e03010902 63
    0x26503070318100309603031a00c030051400b450b5200007429940c1110034554406400246c8010080c03142e82400489000210000e103400d00c0003c1d08aa081c584900031029401c821483c442d50280040e903858111260002d00c901c10f5581c0d400183c54104e0050000c0e10003260303401d00341000039102c6800c110075240300c4d0f0f40245820410620a80c1c4141805e0382c0c610380380140d0840c0c40380c201059181d440700c4a003082c0700100c0ca0908003544040d1104042101401c050700c2c2041084184152036010891560303624100440f000d111440641084500022528556440c00003003030025000d23034140c0100e4020750700198020b16040c0e00e40d002da48050020228203031035030101c98084107903651071a00030043c41d000d58105004d680203403c80a0440e071180000c030000440401052001040c40c542d040b00a1540c5002803011900e450711150610115100e814185965000000c18003215600300ca03506603802071104200540300c6013940907180b41801140001840103070407a04d14101481400c021130380080c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 708867949 1250 708866699 708866707
    0x1b1e0607080610171801110d05060d0201090b0c030d020a09090b0d0c0b0c03090301020304231f021c09051f060f15110a0305030f06010806010c0b0a02040b0f030106091a 74
    0x2100e031396840e409413113090316101d0300092440e2058280728803045400800940d07a922100c280c40d80042d110003400281c400e5000303400d1a00140e0308043e070241100c0001c00050303120f1400e000c10300c0c1140501c403580c1d007440c4c1c0001200302250b54030079103042c00e41e5003c00f010880110400180200c0d03028a800040144090480500601070101c000d001494828000c481c0350140303500101c1e0036600150340494a04d201c11880c0340c2c05440c00c1d0031540240a80034000c19585c04200340d0b40c0d070f048011030740d5016000e81c0094041c1c0c81800c1d841010303007a007801c1c5800340640b458524040e41e0750300d04e406240004a404a0341c120400016020b42800c0381c05c100c0d070304515107003031100c60780052081c160702c0750a00c00c120444010074182800b80078036440c0179481c1c060301c074580784541c8071200f44014003031410018400d040040581c1c0101503020082d812810820441e07440800440081c0b0440d0444a42060086903941208040c0d100a60594881d82d0300d442c4039036a0751410102c541441c1010000d40c1400348 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 708869199 1250 708867949 708867977
    0xa0602060f19060302042316020c060d020409091b230f04090210090f0e0412320403051203010b0d0b0d02060f07050d020d051b1e0607080610 62
    0x140c94800060140b2000046250703880d800541120262114041000d40c03031902001d20109080c045a4069080c40b240c11400701521402500d5102d9a01128800c140210303004030030182c1b550595000e413510724001c000001c40c50601d8007604540c03609014140f121000d000c10240b4107801d0064040c8185080c01907102d10350320030000f03030000e08089d0341d405c56611142c0c00702503501c2c856030781035101c110744803105014108043d0f219100f6103904100a01d400100c10b103c00109030340f80c2034440020602d00001d81c100340c540041c124003004c02c030982048035101c6141118244000080040740d20540494101000420208006000920030007101d0345040c4000701e00840990010b03041c0b8070307000382a0840e19403070340d00180c807642208421417020f11012401c0800c0000400c400072000d001c50004003888242d00d03c00421501c1400e4200c005502d003031200d041250000c0120f00001506108140c0011100e0f40e80d903681d80000f2130310300380000c030f511012840034102241140094031459441d111202161 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 708870449 1250 708869199 708869221
    0xc04050a031524080106060207121b0e0c09030c03061605070312061d060103110d1109030102030703020c0d080105010c030509011809020c07270b01110609010b0a0602060f 75
    0x90b5200304080c0343c8442a4881030004800c0140303585504441c00020981049032079421990315030400780965101001c18041c1030040d00e802d540d490390212548141850005002d60f0314000e1f0740c4051903118914007401035204014001d00322009040e0121642ca16030740c030815540f020242d03016002c00750810b051201462040008000c0b035800703400c0000c03d4501c032440b08000c0f107880783d010f07207128402da40d0720421400c138000710750707411102c2440d00b44403220040b00c0d0500740c2d104407901c0010a541e241e129243c0004100140c0f814801c008008548a240030000039001c1e42c0420582151400b4821030318020501901da101d0603500c040e91002105100c694041d12103600c00c110041c144082c02c4013034401c0315006418240640b0761010301584076454a280c040c034164007600100507028081c50300300e40034409415540b00400080c1030105104900d500161445010403000034454021981006001441504102007814054807100000b59881e9404c030b072200401d5600b400b038a0003032404900314580c2c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 708871699 1250 708870449 708870473
    0x32202222d021b060411100e150c012301080c09160c03110d020a050c22050402010c0f0809181504110f2208010204081c0509040606030b03060c04050a03 67
    0x10340805038000003441e001d213801c00880c2c0413907203843c5030305200020341803002044403160701c04e041590345803c1d51400140000c84040050030580b2000c55030f101c1c1420250060603000c424090b440842c114010080b00c410042406000d9192140000c520784504010144500c0343c42143c17200305410b282c5100480311040f580b24240c1c01c0005e1888540480b003000d11500c00e00181d5a0000e0880c0740442c138146041c6041905001e00c41e0000000c61400c9055041301ca4400800310100010b65640380d100580c0e4404501034080e1030325045c10360503020402e0200c002e0004000807076001040040c005c0c2800f8000ca002c403100c04600d01c80107807101c3c0038105034002d50008030000341a5030800c00c02c2d200340080d61304101e601d00a0242c00605c141b0b2200c0c1c000d04040054000500254905401c0c000303800d984031406042c3d44c05c82c00e16500000e03201c6105809690002d003000f007080c4151640c51500502070106000d07000e01c6806510082800340d4102d03012a8226080a0188442d4915648601401d00c103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 708872949 1250 708871699 708871717
    0x1051509060909090109030f11070504051801020a02101a0112090501061a0406080105120a03050c010b0402041d1503210f1315080408032202222d02 65
    0x841444285680da0703e503034000c1c0c402e14050000058606444c103008081100440c032541c1444060313080b50695507001303e810302c00e4540944010800d521881d000001c1c0c5c220035201000c1c15440071449804055000c5203a0fa403c528400e07041c03000c1c0034107540300c8504484e4895054040344400b9540e01d4a8200394020083c840c2c05000000b0345117594455108100030052580c0b1030381540001c05008098210191034094181900e1703040c0340e00710760000265038400c0d0030806000d00a01150715030103036500350800800c44a000e070040d5207650b92030158007041c0101c000384442140b0102c000078424100350540d6499854020010101c10701001035021080d10402200894144100440032006240c04000c00258940c24800f0544a242a500800209c0c0041c0c030241044280402d0002040e489000d80c1d03000140c1e60140d0030b0108054014004031002000000d4000c1e100304140c0c2c800803407000f08000c044076101802d022849848010b81c980c0021455402e2440d540d505d0200c1131346403190301400c0c1c581 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 708874199 1250 708872949 708872959
    0x11010512010b03060411181915020304061d0109030602030621070807080607020304031e050105090609070510021506040902090c0d1506081603150e090c0901051509 72
    0x188540301a0308109070820640d0050000c01e00641d070034148500e1410700701100c860307403c12a002000d11047d00c01c40c0c074180d20803c0c1100480c242e0814110104004090310400c901201e606110040e49035009845a02c01180710381d40031120641c091800381169401c141c3d10111280d0a5942c1c1c0c078000c2d04040d00d000e03001000c1100702c070b899524008010034200e5010b8000c1c40001d1a140071149082e07080e400002c0b4641160050002c00ca8002080d90190b0768051513441c81806040144042c41410b110f0151070b940c01c2505015501001003110343c00f6070031000565002c00d40350020700415480c521140c800603404420384400700240b01002c0c5030040d000038008221040940c00250396404107640070340310740030000f544400c411070030700c100302a504191003000621032400382d028080c40b40003040e500d03213030038844000048644250b01030000c1c0d031040c5442e523220395114121104a4182100c0c031140500ca0300122241618214001c14102d40005211610070702c60000e26015542289122540103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 708875449 1250 708874199 708874207
    0x31e030c010603030309060b03030f03130206070b16110f15060d05030703080f0a0510030210021c1d0a080c0d080906040303030b0f04060608010b16060c0c020a0e090604110105 77
    0x140da003801044001c600a5401183d012a10b0401c00115134950b115144262300070401c5c685141d080c401681d030310440160203240c1201c4035001150651160030340040850f040803040240514500203601d40a40d2296140d9508402011070706580752040d615006059212800c1002c6403400c40242d01d500a40162618042c0d2240d42c0e41d55207035810030282100031070811000c00070039200d000381c1a075100c60003007001e1019040010042003018414040603002d1183d8694451455000704002004c4080d0b00359546114401114020b01d80540c44400c02c003018482445000369240c03091161042c0c03101c800242035054203640401108070403403001150000c2c82800103040c16601c0d40060802180030351808201e4004040070402c0a4480e141614411458110244400e40e402648981500d00080c0269070751102041700300480715041800038181418415240e01c0316a028000d101e00740d10984809103c640c80d1620072022450458012040703500c090001008a400079000340c44d92401030420038a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 708876699 1250 708875449 708875467
    0xb060d021206130b0a0c0504120f150606020c060c1c02070e0106080708070f17070c080706090b061e0f130c0c050c01260c040806070c020301051005031e03 68
    0xc02c1d4040316000d50801e621400c10052002844003581c1c00300c1340510410a1503d034080290443c0954010317403065140d04645401080034100844074003030303005610719162114148240e000f90815000b000c0050050f00e00c00c40043c14500140c0c1c00941c10b003400f602c12103090f14450203409908074280c000718481ca090014034640340c3c038440c5001c0c002580d103c030841d1608070400b82001002421030810842040040621240d1203081c01400e00180c000b10002c43d00e40c1c0408488050202d5005000d00320001000c1d030421410b507101c0080513206004d10301c0d060b41d50b10b0030080d440900d00007548013400605a040c126192010161404c260018009200241c900308000704507000d4a0314100072440e41c0f0741003014004104140c5540107000d103010350f640c00c4a400710089039440c001241c4040719008001c2203803a0020701c1907802038425401107903044c2ca00030100906007081c4d80c9050f0301075482c06010235000288140c000c02941e00143c02011916604417803288004848141d020841c0800d02000c1c503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 708877949 1250 708876699 708876703
    0x1b06180d03200c010305070f0815011101061d15030d0c0602070614040b160504050402030c0c062e031e060b040c0e090c040609050d060207020d2901030b060d0212 71
    0x11030342d45079030010000c5441e450300140c1140c0c2e001c1e1900c01402101040303050b0566110032070541c0f11304080c6025150f4100b409c0103980038241c81e85901019406e00307602003954000400d100c8108001e800440c00c4075150403420314841c40b178545500c0c0e059009248003268460083e68243d05480c071a500c014a080403d48991040303d418090001205c106132051000b4065034072141504880c22001e10010116a000003030098441c9100d4140129000b00019203802900740560344424421030680d081864050305060106440310614004d0340c081d80c185c82120084610006d09682d44019500c0c1082103903422a041c0080030300c0c040b1980341c0c0791403240c403050702c03a8021030081030440c1d11103010031a8030b5410004180401402054400310900c010810716500030000320807140d06491840481102c0d081200180c03041d8400607400c800d9246001d01006825044a041d00c1c1c000c0c021381d00340040e089404060410700f0310001d448d95030443c0208003180b90144007052100d200405641032203000ca07a5880c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 708879199 1250 708877949 708877997
    0x1e05070609060c2304090e07030b1e01061701032307080d20070509060102070b040f14010503070903061a040515040608070f0e07050c010e1b06180d03 66
    0x5810365129005464183c1e0040200e08900000001d0608048011303000500240624442d0000c44c40c0c4810b01c4d840b1503141484107a01640d0015440da8517071a207503d4503508100d19a030301500400010780001151449076076040c4820400642c10117481e40385844003511100448803860b03d184000c10000a4004104811401041c412010380104810024040c0040c02c0e8014002030404414041d00c4403c80041421002d0f61800c9942c800552a5040104d10700311282d000044440307400180480d41003008200700b070442d1000d102668072074000074011203244c041620304d800803a00088041c000115181c0010300a03184111102d02c104581e48001010386806850020520700e10480d014098141405058042e2400000820103980f81450304c613090010351140110512a030004256024462021110400400d10080c05a07940300440e4985914064030549242801146072580b24104501940c1102110500d07244c22044040140300c102408002d048042281c022146c101380c0b44511150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 708880449 1250 708879199 708879203
    0xf2708030c181e0108071103070f030e090f040c05010c031d060d02072004060605031f0f0b1908060102100e0106091503060c030203010b07020409060b130f140402011e05070609 77
    0xd60380004031070f0024100b41e00282030002044426042074074106400811904e10a0340041c1c44800c0e00803d0508554101d038010401c1e91140210051180010700c8000080c01070340503074104a001607460005503400719203640020046000c44005507076540c41452040c00c0350001402c03451505103404852001c99200000488000d03180c80a1219011040c8040824140d01a07504109180c240768000c0c041d40001401640d140d800b0408186190b140c0d00307074078001000d01c400b0303080b50652034082c1404240c01041c4040c880000e08002018a03034403410b44140941d04c1078014103001500343d07071014050520400807146e150f480b504005818407040c03043d20f06800c48100c07980106811803038402c040d40c0e0414840c104160040c80103016000a0208036211154101c0c3c000502814600d0484054580c031035181d81d0084840c804410100a5a0070400310624090703410080040e52000001c0035403c1598042e0000c0e1f410009a0b807110610788500400c400c0314202942820055902d0100741c542004007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 708881699 1250 708880449 708880489
    0x3090f02060d061e05010e0d03032a0e1f050705030417061b0a050406351807030f170c0d0216050d0b040b15040f2708030c18 55
    0x10401040c01124015444c105020401c800000c1c604400200b082c4c0c81c0d030b042240702d10040c03035030641014040c0c1c0c40050404a004881e441440270b080f241034000b0008202c100120b05241859002460503040d0440080c01140d4886030035039201d44121000d80001c3e1007120305110400000c0b400828008125400f010a07000070000b914103a07c10003240b0f60340f402403851420051003508034403504501a01c050710a00c0c680f400036500014484540340c15880a104a40000314080802c10748401d0540c51040c486103140500c8504c040311090b40d10805840064184e40c000b0400740c0000e200c1030502d600040c4103c0c0100e040541c000b01b468206079080c1c5078600564450703801e0075040103884060100030f10044568605980307890700c2e41d0300380c0d14000300010010100e54002401c401c7c1c400002101e440d0000c0c00c20410101c214282c68002e005660707564000001d000030300e038034039030682d0a003481d0154005441400c40d03d9101c2006440d0b007101080b04421a51500303200c2d0a41c48001c01c100c606051559 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 708882949 1250 708881699 708881711
    0x50901050717011503092a090b0307030f11062a0115050d0609062304050c030613060506150304030503070e061306110c0405010e0a060806060d020103090f02060d 71
    0x1421482c0c0c40b001c0016001540c5004209001d02d0700075810710b81500d0b0401142c034a07940c0c6803c2601a89550b2440c14491180004020031040f113250030303041d0b43d50b210040000550210070181d485000d03220003403135207807000d90f00c0b400540380c04241c400c0d0040c05071403039060903060031080300e950355007482c035508040e00412a01322f480d201740542c00c40350138403030010180c69007440b0106141d1591803801a00850725080d00508005541c1d1104034402c0000c62009401c1c01e5500501d80c00312010f981c240d40724810524045842e00d004282d0a00503083c00b40b52540038070440c2c1d200001f034040203007290360209241c02c2510075160068001e5229500c41d54071142e072460264009011002000a10784c02240140700b85c0201310a501c1c5402d00f610304504100307800011a010031031405090309100c0c0e1300b10341814000541c020f0f8030342c0e00502417410480705018003074441c0482c03540c0d03c1c1c048030090f502004002c59a070155010b68890882107003d0482c0c98492903580d00854101d500400c6182c0382156680 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 708884199 1250 708882949 708882961
    0x111f0204270c1d090702070b0309070f08010c08062707030207050d020708032208010c0309051209060405090403051207050d1d0307060203070507061b0f1e0e031005090105 75
    0x201c51003800368802c3c108404000c41000301a080c0211503200ca034090011200810038240c02003003144d00070054582c0c45039991400070851a1104c90340d126a02e00b2040c46003003c10000d2048c0102283c0300f01a076640c20143e600c3c00704000a01d480c01320314811400000640c1401015010961403185005480260b0358000a1600501d0300e0001942c0c841150011032042c07203000c002008640ba004e110000344030f600c1d941d100c0d0300d050300400d540c00410650701e400740c0e0002589d0141c1000c540f03540240161407522003100840d130820f10032100702603031001080000303004070b107041040f054005010345042c0b03080c1440010303980040c090554001c40450004210318a036001d1900604040300c451500381c1c102c24450061960b40c1340500c50300280300d207401000140c9841c3c45070301503550b01c0c0e401820a000f007000e41c0d0ba5641c8141300464102c0001421406000021802001c06401722801000c40103507040401c3c400304c0e24420080b20482d494040c8000784400d446d242d0103030f00e0080d174075240001005e0902d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 708885449 1250 708884199 708884201
    0x50103050c0f0303131a0c01090b0426030610030608010906140c0c1e0f0a030f020d0f0f140915030f13020a03030807090e07030c020706111f020427 65
    0x402c850b4801c1d030040020100c0700c10301d1340d441d400302d40848220300c010780c0c11000110f0040c040c00c2c50450083d0300e000320200901441703082d1203000700c1c00340d000d0040c401e11007154407200a812442c070900c241000c0020500500b803640300190190b07082d140000c0c2c020307151200d00c0d094883c1518181c0301d0980b40c0071309140056558940c1d0b074004100c0b052491a0030014410035407180801801402c00000011501400901c140202c4610103134000981b4150311991030080c10310310300321010400500c11f0000c0c0743c41c46805041e62250740c64084e2500e0940c1908410304850514511f2411070040e182405040f100f07881e18403030200326a011205941d102d10b48070044401c5c0b00d600808510144046203031217400b40c3c80e108041d0096a40514054082e940c070f182e0207682e14483c951024030829441c10410950316850b40c40003509800d184d080c5c58185580b29000c49465405070b025a8058100c25491400c1514484480e406440380307100c050300b4a96101c58000301c07171a540310100d414450502c2020f11054072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 708886699 1250 708885449 708885469
    0x1615090501020309130207061104060206160c020a091a10050702192d0305030f07020102010b0a060203043b01030b0c030c09040f0209030105040c06020d05041409061201050103050c 79
    0x100b88000c41c1003c3c001000141da5280a03419103072542c0c1d00142900900c8050307000160811040550255034075900c3ca4000e40d1034030200c1c1d4242000c1310704405900c1486c816907010500b950000d00c15555681070000074401000c010227408542903008203000003a88a0750303407001500f2010b03103540340c6902d42c03401803003c5003140541c0d003054000f26440c18020300e54a58544410351152451000004404649480c90321080780c00141c914400032965400d0b40740480c0c000c05039580b00707a0013848014a080c06100314101d0300d015030b0015070018882400588070168482c0030792144154808160642c50210700e442501012440242500b418010300920040960042d080504500418950310307144404980790301862130400d1107241c64104801c0840e00c0c0750113070740b14080000c0081107030303007405d01e0495941c0103540714550160046c030342d03101851401441900c1c1140d80980552038420245000c1000f00c03c0000c0c907455004007400103070107002c04248a10b60103544104014040c00c0005d80400c801002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 708887949 1250 708886699 708886709
    0x3051b0114130206070611040320010c020609010201060e01031415070507110423161404031101050708042331181a0a021218161509 58
    0xc101a805400c48000104065010031001c01400000b21540300141e103610801c10003a00309410840c07481c2840d40d4401c000d00440f40729030141303040b5001c4210103240340d000c208100d50100307140380359003009400c03c6801040c090340140300000d0a10f0312584a000e00a500703800030380d01072003044031960201c1d900f003203a40701c0900700c01c140520074a407010000b0b207a07104158008102c0501492007520a480702d8016903055a0740540015000c2e45000b0100300002c0115040c5043c15012503d24454a01400092147d0b02c0704558079441c141c210380b112a0095a41717040c0c2030401c0020402440413680d00c80180015240b50710002c46894116024007450304640b03400944210500e200383c0000364004178404032420b460010340c1c561825020345d0744004042042c00300f05040840c0d0602010000310302c200044404880c5080038140c0c542141400807401020350303450940c2c01c030202151207440c0c840c0c0700455581420040340d007041e240d04410328501c544d580c06038800942c0070174140c1c480c5420101180c0949 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 708889199 1250 708887949 708887951
    0x801051308070302100203070e031c0e0f0315040c08010b060a1d0409060213030303200702010503091609060303020606030f070b090a0b030916080f0d0e0d060903051b01 74
    0x42030000c05518151541000100105030018240041500911035060f00542e400710840d10b9181c0000c02600e0350048902c0280b080c00754101c011000101c120000400072456601c10980d4401442404040c441c05226260b043c800c4481c0340745078010b407441c3c5e1072003280f1402004000d6890f10900e54296408000e2a510030041031018a10140d48001e082c81e004910300803800801d002d0310045401040000f901400307480c00015100e140d10b4140107200101c80c800c0c1c0c3c04000c03018186c4100e545052140003480c0c0d28900402103c0d01540c403070400355800c04684c0e41681c05002c0000c15aa8a03104180d21412354a62250340c10018543c05002a551095040c0c1c080c1594000c0c85607000d0700ca01c818021124413400110f078811141d01d864280d080a00030807a0455a0703400e00302d4009a450b02074542c3e81030301c10b0101d100401c0001010641401c50007084004050000100600b902d100410000705070b0400b000d203140c00c0101d80180203811189010f40c6400d551140b607000b800b070820403045850000c0fa = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 708890449 1250 708889199 708889201
    0x8040b1b0607020c0640050307030f1101260109050105030307023a053003010504090f02091501020f0708060f041a0a1a120312090c040903050310080105 67
    0x210b0b008500130260420841d98140d80704d1000c41c0412051030689210042030012803d9400c05410301002240540300a4604140303440c0d661042603030341c1d5154040100007040c5052080e000078814001c01c07030421814104198005c4002c0e5000c1c0354020800d41c901c207060600c000410a40742c1520a880c00341034242c0285140c9101a004144210b0441d21050032546a45090300400030080b1080c8014085a2442c9990b0654900b00641e81c6d1000305c1c014482010381d14110450004112414202d02040148190860380380604200080a800300142c03504112000c8050050752010030403841914207484482942e41400d00081c43d20602d844110903581c0900344c00d1012490015240e54020034030318460340e0716529443e0807540781070102d1280482c00e28040501640d1402a00b04400b41042020400c0c2405250802c11854038842c1114a03166042000107406000303514013001e070b008500008480043c1a520003090480744009400e0780040c04c04014403007107500783c00d0240000d20f03140c0300a03c0a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 708891699 1250 708890449 708890461
    0x5120a0b150d11030f030c0604201f140708220b040e04060902090f1b030f0601081e0c0a0e040b010e0613090c0e041d06180a08040b1b06 60
    0x4803040d0b40d41d001d07028441e00345060310b1a0750b0411000540980301e50580e0b8540c05202c103080d9a81c2c0c4c0036542203c0305610b400305209400d60180d4140001000280404280d10f440402a1608406481ca150800a405840c80036409002005240c480e10602030180d0762601c50402c0748140228551b2040f80080700c0c80b00304002002e00040d6002d032529002c00c550307951154a003030f40c018076020748020f401016402c2027255003602881000d2148000010307020038078030b402d40c80050a02c400c42d02c600c000700f0100301040140d40301e5500f00c0d51181c000e1324680c101c00a000c00007034401e2011103485840010005c0c11815040d404035171410f18040076201400b903158002d0000e0701444203501480d01540300444e009900312042d540240062100703040400902c554510010182d55500103203c0c0102e0030322200d4590380200c8900482a00003003409004039032a011018070541070340e00130b10f801c28401e080000000c2250400108010a0701c90891561204003070a01200542b40401e8030125800200070444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 708892949 1250 708891699 708891709
    0x14160b070c17090a0f14010f050306010219020609040f06060e01021b04111605010606140304020a031506030501020f09030d0c1106030c1b010906180c0e1005120a0b15 73
    0xc10600e40b4400c1e40c441211002003041c3d1200b40d80903440544105ca00011820b129981074103c8074802e0b42d4a540c80c4001c0c0c8016941444280c400c1d80c0187d003c0001c0da81e002c01e0030a2503140c5948000c120b03610341800c800000781542d10603100d00d0281c0d503072848200002034102c001000480000c5c005442043c0c10f0840e001d0a100296546d00c0c00b40362a41c0e035440c40300c1c040a00b00c0c3d000f89040411486d04003001c0c01c10a00804041c0502c0011a0b100d4100b0b8601c0310403032054230722807030380144410450ba00310764408480100c202d60911030240c54010210001d0000c0c00503002d1028103c040b651200030303d608143c03501d400080b4003400d0000c2ca0041d04041640440100100c00c4c082d00c030300c0c0d074a031220000c4c10013a110303100d01241d000356050983d801e11641904400c0d401e9005601c14003d14281c8481100786e442c50100003001c540701c154080000f48055488280d02c043c2200402081981c0c40001c41c3e071038000340052b91a9074000700d2901d8104070092200d6034109030705843c1c040010081c040491 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 708894199 1250 708892949 708892973
    0xc0206040b0309032203051227060c251703041a0f04060c0b010e0106090918060518011a0a0902090a0305120706050906070804030f14160b070c 63
    0x1650101c0002c00200e030301038204100c2c3e035205048034102524000c00e03028803520420500088441303010b03544801004440729819601f10070500f520a101c0340c424803080000000604902c95040740003480a61100a010b01c42072110400128000c0c280e10503000000c82c100300c5c2c5400c1400100020540460506c0e0000261010b84281050000107025030001c51002401601c0e03500219004c001400b190559004402500142c4a00c1850341566220381001c07101c114240030304000200c810070700700800c00381c0b600600040a000035511741010020b4803030400303950007181d2a2606400b501d2010f1081d00091082c080b080c440b041030511824000d030005080d210062003103c40058000c01e20b031420340d0741e1262a8000b158060100d55102d43c509101c101700d90004001a07410030310309800110135203804030703107a4800c8036999200c80380c40e5910381c3e05907400682ea100304010001c800348180080e10400c3c00820134a0550310823089007811030714000c0c2240200500d41001c2000100c0300c040001c00814281e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 708895449 1250 708894199 708894209
    0x61b02150405030409060303112406060d0e0102030901020415080f07121d06010f090b0d1b09020f090907020c030705101b060e01061203090b0a0c02030604210c020604 73
    0x4005651240d0802d50710303500990300002035481c80c110b0000f0401d60041c038007071007191142081da1a41030f1442e040e405569045908015035422920000d6454544070307000b0040b20100d010f000464109854920b803c80e0002c41c1d411100d0380d8002000c0c80329421641c01c020303000103079282960031803420f40040303c007015024000c0c1041c885101a81d24183e89a6040741105c10b0100c41d0745801d0800d00c084090f44c1d00d1080c0306401030174880e6480400d0300300f50384c01117030b019003000f601044c1d4000550b0f4a140b40b214072400000c0c2109042c0b0400b09061916000412000320020760072600c8941c2c0030100400050050180419548540042802c40c1c0300030402c2c1c41283c10498502006043c800c400b40c68980e0310340b02101658200700340801c20040720b5800410b00d0603a0764002c0007410741f19a4180d500d90180007010300442c19851082000d00b640c540181642d000e03525107003001204560102e03203041015030381194500100010300c44a0310030b0f1414070400303003c0c5240000d24404c85401082480c4203a000e8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 708896699 1250 708895449 708895483
    0xf1d040609080307030504170a020c060309070302180103020901090603110907020c030f0f010e150c07240905010b03060c1b0f07061106010f03080f0a09050a080703061b02 75
    0x20140125603006007000e603000102c4a0340d03880d10380e900a009001c229000c440c01f4106851021150341d480082c4c85803404242c0082100c10f03080c108014080d00010714100c0030b841a100003000580302c001120002c8494800c142c2c1c101e504620412006907016004100240d152140070804a40342c1e141c07013680d000c03058600c0c000d1611410390172810f20700850b2009030036100d80004080300882c005221030442c01355000030800041081040c50300c1e119241e40d900e17058072000021070302400020009007021031041003201080e81c0000101c84a610312600c00014982d40c030303440c101c1070110a00400c04103210840c0038183c01c0c903240200c22131900a0016500c1d00c40420b04107010200410018018a4030349031045038030b1665200750090896218080048a40c0500000021f80300c0808000c80c0503070f035100bd449801c04007100e4407101c0e941c200401c07020400c06860b00014481c1c588940140180c07019030083c1c90354905508103201507540e0a244110032400c1c0c00c114690705075011418642c0c3c030850b094 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 708897949 1250 708896699 708896701
    0x7080a02070f080d1415030c030607080601181e05010219020915040b0a030503031603061401050f09041b030c0e0d1b0b12060f030a051e03040906030f03090f1d 70
    0xa82280180242c3e40c40c17804031052401400140c0da010350400b4130211080f403c4422444ca082c0600d034403600700f03840d00c00c0450010808a0745540c0180090412001401090001580c1e90480014001c3e822500c0c41c2995074405814459540d0600c00302201002282c607954500b001503000c04d40102000b0544c42482d02148000011580ca54000038070085000300061002d03a22818290b440341e0041d14107108024011164020032030003406601e00f1581c0747c0c503101c5091300c9441d0040d0303495805001041401a000c0000c0710880c1e8032441103400881007506000d517031107025540138046511014059040c0000b14060180c156109a2a50b200035440010618003851224a501055030107030043da0280c0e03c0840d800f070700c103000c00c9016445100d00300c0c0e041c1e082c0e4291200340f50b1128035100010740182c205552003104210302c5581004200113601c1220700d016542d400744003ca8949400889200d5480001041495032241d1900c000d4910034000c400780f0780c80c00f181e5840341450503050001c1d03014840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 708899199 1250 708897949 708897967
    0x308150904051b121b1801060207051e040504110a0b04141c0506070507150c08060f0f060c060a060504020c0a11040204051f091509060809120a0807080a02070f08 71
    0x4408044c041580b10480c0c140f403c4910480850b011007000c240e005166031040743d04c0101e4900801c3d412a44079401904000b4104800c1c03003007599440b03498580c00540c0744c0d6040c3c0c8a0f196845203038411070244c611070100005820400c01121025880161001c2042c07106005030f8240a41c003400c10002110001c080c5508111183c8105101c0c2101030150b0107043e040003a03068004000f4508503100e0102c00805007200c52000d4111007002c40075000080e003d50000304641000300301681c011000400410004140c40006080c0d50300c0110305080d20342001040c401540303420700a50340038003000c65041d4180098440c0030303660b270f8900000c040c01c00c8042c00948030300c50311071b94110b801824024024a180740c14901c001c5d1080c140180481000481300c0e94002110243c00c003c0d03000740a00e96450410b043e00c1c1640841e000304018125501c0d03401695207140d10402480002e049c007e4981d1501d50407450300d08005000d00c20b001b00781003980d60041104d540058401d1001d00f1040d44d03c00c8101f81c85800300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 708900449 1250 708899199 708899209
    0x6040f121a01060f031512080706090503031302011d090718180e1c05041512020703090305120309070e091c031e02090604030624030308150904051b 65
    0x4881903031042021000089080341c0c2c4244ca50020303da0300e45084c4030200f0600000c03090319903503100d040b0030b03c40a45078550025643d80b00400511340230780800f21715511591140c0e400d660041d1100700d48210500010000c55030020140b0b01c890741d0350340c802080140004003003100070200501d20750402c15045d84440403a075449403000064688645280110000d1100c0580200f0032425034500718800d520032404840100c0d1003800f0440159503555081510b042e01c6e1959254454002d10f0503c4012140003500d481d01d031014203140c90290f0344014545295050590420000c1c500a4101900030001c0000c0d0060000c0d20130201d03818412003000c0b40d07450a070903506000c5a5050810403083e20417142c01c585606030000720000135030f031400640e90481403801004038400d4181c90303904000b00340000c102103144c580c80403036110b2904108941e012182c3c00d0702c0100032100c2c1c204401041c440014003000d1075031491007014155081e600391006052a84820f507031140b40b480d01d0144c400302e201c0d1084640d211 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 708901699 1250 708900449 708900473
    0x8120a05071401090308100902032e0b030a1d0304080619060e071d0625241a330f0a0302040e07090302180c0f0c0d0e06040f12 56
    0xba007002080440410f2030010a22a02034414180340704030754902180d408842d100700d0707014025000d848444032060002040304c41804800030b070352243d003030341c400140c8010000096200d644211f00000701c00f10454200103000c1e00031103907282c2581c81480180003d030000603405410121601000c101340740002c1d00030015000c1904550410518081401902c40d044040c11a4442c6900c003041400c050315000c3c420740b03001d0310b162109600c1c0341056aa51400d40004004101070107050031440e2200c0148a0501c02c003074000000b111540d469152191200880380e074040042da0841d411650420003405101461b0121511608844090f10a0805215a0804547e46402540c036500d49900140d0005030003500203200f40e00c1581ca00900040c0c80502c86c0c110340d402d884d8010b12456841d15070591101d190321004181034101c0104010b04004090140301900400c1c4007000100031641c58428010443c0c00203180c040c0c01760005010500526000360300d60740c240d803c00c0600f0903026009003401d44886d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 708902949 1250 708901699 708901733
    0xf14100e09011d010504030201050109051b1c061205011514042c0f0616021c0203040914090d030501030b1501050f040f03051e0c1e0a0602030d0608120a0507 69
    0x20143e01682c480352040d00050f1041d07000303400821050780e840a8103401d1b110b08603440710800000c5040401c1c0d0344641c80240580d8602da90b02c0b000c0d04140d1620079000c41e10b0980040341d03007108880340007003003010901030310420011018480d00b6191030300c40d00140729080c016095200d1031302c4251204000c8200441e00014540300710f0008140d01001400a8407803441101041d4a80514400240020f490500c02c4d450500f82d64001c010303405804007004030038804012441c04600041000250b010228095040850303c004803020450400c072861a15040c0307840d580000b410704103030042001ca01c0741150345601004d9854100b0000d400740004032410b00c80c40041c03c0100c0404180411b81c104601c0c00301040e207114000b16581c106402441d844401241c0b10185080d6000d4450040d003820300e2801c05440b200415507401d80d20240100050718584142c1151005920214010740d0003020340c0a81c1e40102888005040040f440403031001a6101e4a6225018000001007080401c4548090308180390 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 708904199 1250 708902949 708902981
    0x304020d080c10021803070e0403030c210606090905090a0809030c060d0b091f050411070210031a01090302060409050411030609010204060f08090a0311120d0f14100e0901 75
    0x2044009064002e400081c171400143d8041e403080101e50400203003d8040c1c0b07070301d800d80c0400350340d40b503070304401525880010f08204104e125508400022410400c02903550507403010a055040c203000514209442c1d00112455040c002030103000200403035040091074101319802e0781d8902002c00b10b8688a1055811600700000042c625500100e55100210003202150b0140464440c8080e400140d02c40958001c030f200704921080040303261a41c800d40001c014608160300b045260340028054903941800c503808640c4600b0b43c0d000d00c0022316500440541d09003400c000c40c0e8250340200741e1030b0056000d070108160740c8001240c10320580e0300a03d011039800408803401d524091070707d41d000c1d421a10403080400c40f00c0a48180c0180140e41c03c40c45811094014151403140c1e0f00c0495110f07001e41a150428064845d0240c400341d5881e008108221413403c1c042003081001010700100d400d2040b00016a1904030144880e0684018911007201c03140034045004c0e8031707081d00090050080ad0300101981c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 708905449 1250 708904199 708904213
    0xc0f0d02040806090d05030c09010306030f0f020420070b0c0412051b15120a1506111c0e0d0303020d15030b06030a03020c060c0106030c1d100b0304020d080c 69
    0x280800c0c0c0090003690b24260654840ea210110b910340d484d58034403c04800708105100043d10307c641c5d2800750461084c145400710b6540d90320f0f151403200d19556001035900c2c0003602d0700c900549c1001d004882c0d84801e100d02901007036085003449515409451002000040c4000124007049142000c0c0d80c00351102d10b003a008110390602d0460f6403218001c45041d004071078155814043d10340780402d0b82c4100c410b0030540d803a01c04459104a00c403000101a41c0c01141d0b140d440e107401c144089401d0000e00007d445603023600c0040c03143e107171401d42560260b8001510707801000350b46991001c007400c0591003d68102140034561b25003500603001e4040c001c40018640560342650750a101c0800b000c0300d0154114017119155038040c540c4030310300d9902c084d0141c1d101c000041400d00b050301c000c00b841960340c00000b483c41c0d200d5480301d03c601c02d40d07801001c000c0f990031440c22210964220440e006000085600304052030007000c0d6515020040000c1c0c454008141e0130024040c40c0801c40b0aa5141030082d118a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 708906699 1250 708905449 708905467
    0x30030c03010608010f1404110d060314120711010c02030304080a11040f0c14130b0f0304050c0303130311010302040816170d0c020904080c06152e03050c0f 68
    0x6800c00d10620001803000f000005021201d4030240e42900c00d2003403400121481c000903c0040e00729098202a090000c204100c4400101c1c85900081c41c4107400c1d0508207070340e2021581c5880c1894034010300b01c54042001200080c0c0c1c002c4030303040c0c400080c20504440369060002900394000c0340d2201110340141d4905004004102d42e10b112004000c49041000307240c040c110314101c6000101c0b01c0040388040003114100381b4a100031f440c14040703c0303054000c2a612444036012a03084056041e240a5011082c042040300c10305c000422120b050f00114240312482c28403098000c2248400f6020034803100c0012080e9100380c0469018050140c01c4403051000b1503020111a6141d2190004c40b805080c070201c0034000c081008410303040582e5030844803e806408016071068007070402c8404040400106c0103d05051000340e21402c4440800100e50801c0400c0c40003145243d41c11202041001004002589502c0320b940450703007551900180326076400d0100c03045841000584003414002241d80c0764 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 708907949 1250 708906699 708906721
    0x6131e020706051e040b0a0609090308010503150402031509010b06030403021507050f221d0103060605100801030f0218011712031005061c02030403110c123003 70
    0x7003094460324041046030744060031a1600403200144890300c0740020046004070f14000d20454002c0c000c0f45002841a655410000440d00950f0085001c00c0c02d6900400c4285414450601003c0250b0741000d007500d000d0340000d844030100151b9201e1226080b02103000c0c50800d41c02240c040344080c00165813400c040c02c001e903481030b12040708042c0030711400001d031500e0700c500f054130b0b420441c1075001401d00c0e003011200c0c44c01800d9171001000d045a00382c00055100040c2035200c05005074610348000d65419403d10740c05450300d94000c00e01851428444562540d0f020f1003050440750040c4881819078510320004010442e541c043c40c0c560f010000010034a0f0b070155620325140c07803d00b41100c40345c42c0c0c075542c0c8005a0004841c0d0390344034550a0300411003418007400901000b0342004c4041000c04810008078102c0c0c00645050b800031707a6114103c1c061400400240b40c13010022182a03100d01201840c81b65520a4a8114461422020340c0f41c0070103007041c2d03081000650703084907140d103070724107500c03050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 708909199 1250 708907949 708907957
    0x10b0a09050a050601031a04111e0a11010209010203040303120b030109030e041401030b0112170c0127050d03021b070e060a0e090307080f2712010b060306131e02 71
    0x140c02d00d1a0501050076580a07126581c024944408002c046960703582c2084000c1881c04407403100310701c0c10408000a142c52001d0351404a1001e01865222061048010128011152502c1403a0710400c00c01c02e0682c2c0000981e400c13a81d0503d007049003c4c5503802c07408094030105082980640c01d2010040030160000ea413030828140641d82040412000701014038110030070304c40605040702d802d006000c01c410116980300d1540c0602c41c2c0d401079081030b005141090340010451101c6940d61a800190580c054010000081000901404454160311040e03200c010560b0343c1c03030a0583c0040c80309003100481c103100303803046408401d42e03d03420750311500d641c99084101c2c1e1041c8101040d503404a80c0482c1c90032554000d19101e0011030801802d9981c040080c1d11070b0400724050941803050042c403c42d80203444038101b6800000c1160b944030034041c003080d41c854552141c8240d05000e040c1c0d545445171416a91f228800b201c0142c0002c01415107600185000f1010180c99520050604080703000c5400030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 708910449 1250 708909199 708909211
    0x150c06010e1f090b01050c0303010905043e0102071a070b010801050f070e01021011070b0a02090d1b030b1f080304030803191d0d0207080703080a0c05010b0a0905 71
    0x314065952024010100c0010b0541d14108240100c0611000c2950b0b4001d240a100604007246031140448100740b954000340d200c204500e498408000070402c1071007604ca81e1451502050b001001c062800a0100e2030b251400900c059003140c040c8250783c420040d0f10020b00d07080061b02c920324000300380c040d5198030901c41560001c008400006007100c051203440d10404000070700440306c2d1150201101d031045421510360452140c80c800c0c240040b0684102030408070303404842070b680c40c86490143e101c050700400e40b407000d610600550381552100c2c86490802a4070400c2009080d61340030014541580350b401c090000c03060362003007142000746c1c150f400004002060852000b103544481c1607039680b24a010007401c02e0014008141d000c000d25a40925046002e1070100d0981a0001c0000d444010700d403610702c1030b80c41501060304040d01400008098114100a41070540c1076444003d990300c0340192050030007a03442000c1082c45029070140c61000ac00600d040c4006543d100151301802095800c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 708911699 1250 708910449 708910469
    0x60117010803250804031509080316030f0510060c08040e0f011d0907030f05010902030a03050901030c0809190311030304030905040b09100b0d2403050d0503040c0311150c0601 77
    0x40f200410340d081d4000c4860780c1e4000b400c0c614107800d669510840c101c1100100c1c92180c2c40c2c0500e0b1000800d4070000d10b200c0d0080015a0b8050030550700c0003815125402101c07000140f40c0000d000c940c400c2d500c1c114090303800c1410720a13504551f038500b012061245e60f104044800a980c03d00030150909000ca0b4120340350721082a011050304910400c0c0c00704151026552580000000c00014079049855140c0d40d0107000000b038a60308540200307041c220441821000100002040c042c69078052049144c05c100c20310b060740940c03520382d15450742e803030302c00ca900f51340c19040c144a441010310414209207140402026aa100e050918002c1e11040d0a4001c05124a00788840c0422038207242a405209100d40c0b14200c880c2407401640c0a00c0b81d000046000c182900d032103031110b01d004140e400f00156020621040511407450070820700703004842010504019081051001151882c901c2ea402d40b070301710004001e0710040301c0005244400781d1480c4000c150001c030380c2d100303400004591507040f50120300b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 708912949 1250 708911699 708911737
    0x7050a0e0915220609021306030305040e090a050d080604050109020a08070c11180f01080c13052d041a09100e12040b0705070503011a0108060117010803 67
    0x80140100403044441c21002d0344910001000c1080700c4a480e9004240c196180151018404003c0c041501204055442607200c0d80c0742411414403400352107006500000400c0340d9811079400520b00d00c80d81c40b582032182c107400d010510300c80050120200741940002101c942006440c0301030402d14045445c00d2141c2c5c6048000a010a0a03008407407120340b50b55a56409540c5091382070740c00780b50300502607503141e40941006980351101c40c03000880344601c4d01d9214013407038244141650260140c01c0129030307070800c000c0ca00c11529030820302c1d41421850790307002c109a5102510640140d100e40c00d40001454460820114084030290780c41c00b99020708403036040440850588042e0780c4041ea041840c1c0c2d0b002d000b6480c601050f66003d5100340040d00c1c00c0c0c0301c0c4010544040d8106810a400003580d5440c0051a1f404004003006100d00821041c0e009000c8040b40c40343c3c140c0b00e030407401c08540c140400580012084d81c86108400580c1980e25503000e05544c45041107a0342e034000050304291018000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 708914199 1250 708912949 708912959
    0x60c021306061d0f01091e090c0203070606051f39050c180703111b010e0d02010603200607020d0503190504030203061513180308130c05010f140c07050a 67
    0x50904c9500312042e120004554070f452042d80d1940c0c1445a4180b481c1d52202c4c0101d004401401078a0f1012413580c011070300c803105405c0c02000c07211984e000900c030f110030b940e6404512040300a0a181c540ca03609214407005001101441742c0b141c84070000c41c2d94102880224420000c051001d0011402081214080c208900a00c0741002007002a117901d29a4a800078610a11940100d41d4103141c505030309080038800c1c01e10010300e410554000026075100c0810891203c2c0030412800e403104244000c1c042030740f95840d10b01c5000700f280d5003240c850b10301840c2c01c0751b5138032080d045801c80d0768003030420040d104e0981496516504458042026019812040d1032058810400e840950b5001400313440962202e5040744802c201c802040740e00580b01031038007041402244201d4030f1003001c2405510b200c4d941da02d4001c084100060030380100486141c2d040003c41e806080c940c1c00e4407020f003400f1040300c1115001340d07022654440c0002ca1240700040c134400c078000c080343c64000c89109443c02c108050300ca03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 708915449 1250 708914199 708914209
    0x13090e0a03170702010f0905030403030f091a07021516050d0207060e040c0c0212010507020c010503010b0901080604111611010f02060f06150c0d1215060c021306061d 73
    0x11980075001a100c442c8180040c1025000c05802c042203000000700f58803005440001d03035802d0141500d00e90000702e402c105154104413446131406030362600c1d0f01e0150401317103140e80019445c14454030f8810080b52100454484100459a9211028640d9259605091580c0c82d1540201c0d04a8813402422483c0c00c80301e0000481c1000d403040307900d5422100490034107000041189400c08020011444c10541c05a112180e0100c00034404030700228030303407a001c10003a240085400c6210304000301007004004600803c0103403026004246031071821034075001300280103060115a44484c04900180c4e010707982d0007522403800294411020319285950160043d81c4001481c031030030004d41c0005c400103858080000d0703000c1d84000e00a00c0390381c242081c25280011074110b5a90003201e0750140f0760680f08181c0000002d2907140201e0018003003210f00b681c0420500c940d600c0b8002c01e001c050380c1810f045540e01d40b10310107440b1800a08200261761280000c00011405812980260f9002e1504a860400b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 708916699 1250 708915449 708915463
    0xc070f140d0306090204060c060b060706020309030a0e0d080318011413051002030402060909130b0c041d0c19031e090213110301120201050904060e092e020309030f13090e 75
    0x140c0c03240d0490b0f160300c0d100e000c02b0b001c2c2800143c0d4811010046140010032510155005024010007140c807202d0640c005030441d0f800e043d105103d184a502910f00080c00903040300c4c1e100a403404850f0b60068184107040c050141c441c801c01130345822008000240c0640520080310500440c2251940860480814100d120950340070350403a20820840c82513080c0f8070f0b4025002890000780c141941840d031117600b020402554012501180098200b000e04980d41800315400040c08031410f19051100c04089184202c00324006111074410a40d03030168020340c00600030b031520341011031405407201102130081074031560132841000841d10305240800b503072040320800c0008c80041e40c83c2da400c2c0f40e010040740500140403410000100f150140c540c0b11405818020b0001c4200000d00b400c0c070240c0d0342d09140340d0b03001c0c00c000020f00160300d0002004100030340f91811401c85c00141e498580f180c042e4203502c600703914154001d4002070b440c003001c0b4040c0d25890890f1088a030400100c50008483ca8403111 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 708917949 1250 708916699 708916709
    0x7031b14090c0c1606030b1e0d02011218230604051504060b060d150801112203020a03210c12080612070b27090c070f140d0306090204 59
    0x7040e00000c040c0c80c0c40340020151180e81070200d5505080000c040120b0380329540142c40002d8681d0042911030400000040280b040d641061f045800f1040c041007111101180c01b0781045480404405910816801107152008003500900c001c0d0b030302d06040b001c0d561041d0440904140105402c0400c4902151041c040c640c450080c09003d159500c80e010020405041940d0065031000301526943c6c0720350041c00d2001440038040b842555280301a409600d290384050031a9040c41d00103085456800c044600918220448003800104542581c80100c400d40000390440480040881403152020389e1050801c5213051405060003203020454240100d0400103000d000300b001d0350f681d114040c0c0002684020050000001011441e400318a03183c00395020780b1a02d000040c4102401c1c6443c0d22a040988807208003100c1ca51620010401c90b1800405410300c50402003002c50400c00080c407100740841c0c006600b0440d05203015030b8180c5403804800501c001c24609203002414031114000d0303900b128 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 708919199 1250 708917949 708917959
    0xc03060f07050a05042607050f1819150312050a08070e011112270a0512031c061809051b01020304050d0804050111060105151b07031b14 60
    0x10701c0d50101030701c1d107801c800c0101c404d00000380004502d0403244210110340e03544c2c90303024400c01362040c3c10503424071413182c1021b400341240701c3c2383d040c0c40d4503000f040f5955242c41c2e00040100396078143c0030090758081580382000b414102200386500d01803108107401501e01070266400340404801f0151113900c540d8031070741d0201c0c15071000201c2d51406440748200012041c1050000181098082c505003d10f01041c02c44e0316001069001407070a041c4044d118201c2d0300303551a224007800800041603241d0303510603244110582c54507004184014025039891400d00d90310208241d0080207510054a49402280b000240740c02184028805500078540c1c0290060040c102c295a0100482480c10200c0c50b83c44c1548030400c0001517a8903031107402c81c2000c2c051080c0035141c2d81410001840d601084e0725459240d071200740148015501c02c80950307280100f10142c82d03a9181c0d491044452007c1c0541650b05a0040040c00024000d16000558902115540914900d9140c080360003144024502442d00170b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 708920449 1250 708919199 708919201
    0xc1902030c0a0f0f0f030f1101060506040b0a0203040f08010203041401140a0b190315150b041206061203020105010e0c18091021020114030705070b1005041d0c03060f 73
    0x40703603500f40d04a20b141c1c05141c0c10321845809488002c443c03100c03401e04a0000b000d075510307071100a034020001400000d101009100d440d140c840001c0541c0103030300400f0011400020001c203c175000300b0885008162840000040a95905080d8000e4000f00d034191000c480c2440d40c800400c1c410b1260702000d039908066001a5100c030380a0f20b0045c00b088035025001903142180c024a52603950001d0021885080e03a81c4619903440da41d03405540d40c80f00452508114901c00b845240404025101680d000b4905c660321074495041c07240c05088035030f1140e220710060610107028150b0640005050702c1450320103802c95164004001818401d400c03014015604c034003010740c1c445c680b440c4060b400c520460000d000d07280d02c1c1c40c0044c01d03000a4403090410301c40d05401d00e00455811510007511410b00c0c4820303600350316054001600700e114944008001c0c4012000180030940e0134031805003e0710001d0b008225241000440300c43c14000100001c3c01841126107290a07441c0c002403c0c0e103d001c1c4401e840c006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 708921699 1250 708920449 708920453
    0x10082d0a08280c1716050601080d020d02100e07120809011404180f0b1017091617120a05071106040b09130f1505120d02030406260c1902030c0a 63
    0x1141c81000a01255224204010000062003410030701e1703024007400240446503d00080c5c149403070000e84c600b8040d5044100c0b10320344d898001c507042c2c90b400802c01c408120b00c03040c0303900c060a00c0e05e00d41282c0304c0140301803501c10520000001030100d003002a05e0f540031243c0b1300440c2c4206801580f0401c840860340201005130303032019070004807501042e10b5001c42c5031098030700018901100d40030101f00150408034005441d640c1080300c284c01501d224080c00c91114030903400851116540540c1e40031000c150882030b0001420020a480054007001070394944420490090031136220300820743e000804c0c20200350182c035011007210308451482010600e80b41c1a0810700070500c1e00c1c2e040410813075640d09078148409900c0d00824580300500e6844150b003034101001c000c604203200010803260b50240054155035500001100c080c2c4445040c10307080d1284a85801c0c8039042c400880e000a40480c10501c1141c845070000303410325041400440040542c540ca00703c0e601e01540c0030004081e8420090200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 708922949 1250 708921699 708921713
    0x3060c030c0e0307051905040e0127120807020a06060e0109060501050906030f13050f01061a0901020a14010f0f0c0201200d1104051c0b10082d0a08280c 67
    0x43e450440000b401b908030b41e0b40c000541180ca0415180d07032165118280c0c041c0040d012021080445140c10061000c880207490714250000d10190317410a022005000c034800500030882503104c42d41c002000e002040c0c403600c1c0065045d801307104481a082c20101c0c0803540d50f0189083d41c862403c060021411555130311810403071602c0203000c100c8113010490300280442c0040c08a07220000c3d90400100d5030314070f00b40d01080d025150560b2a513070018144580742c05132b80e0210b01c02d1a0079810151100740d00598922071401054048003d903101c0d0725000c1c140d082c80c0c0c4180c2108080e01d580d40c0080104442c11011207c25400c00f02c036000965400304041c80f10030010f5401040e004550071056400d003a1101f000c2040c58000c00340060105244000b0401001401582c442e030080c101c007080400d00307180400031356a410052152500c00d100c1ca041240710181070840c41250b006d2050704992184259080800d0785074056110100d800811100100541c03c5c2501d90300b0306c5030302070396402803014030a481c0c82e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 708924199 1250 708922949 708922969
    0x5150d020307200c180108030304021311040e0114040c091505040905090c12010b030a0602030a020909011d1e0408071104060b13080c1c0f02060403060c030c0e030705 73
    0x107018008201100160520f420002031600c031109001401200c6030340741081046540449075081403070152005012007100401500e401c994103544801d1200c3c001840303003000d001c003600d4440b41614013250005148954a02d039a040714003500035140c952084a05002c01d5a5101112001061110008001c81030304100b06446d40815480c060b0f04040e00d803120b200540d441a6843c2c1000e1b404048601c490b49001e0344070b000000c05400007007007aa01000302098440071210006008030340d0100c005041851071f074041b50903401000f0183e2900e0341e107400c20244507504244090081d9981100020680d00c02020942c01c02503d0815982060b0707951f41e40d00c0c1944e4041401160310140031045080e00e0380700d074002c50f00602860003405440d0300030ba03d9040c000490031b5001d41101c1d80049801c9405489441200b2012816a080750301d116143d0b0a00b02c50344d1020700d200a410a100003000424032a442e881419041005d54050201d148001c00486e80540601042589a048020b00b0451450b10303510203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 708925449 1250 708924199 708924211
    0x1407031502090f0d080d0213060f020c1f0513031208090c0d0f030201020705120a110601030c0e1b040909020a15020c2107080c0109050d0305070f030e1c0b0105150d0203 74
    0xc64071b880014005031003a07070040042034180c0e1001d4401404903540040c0205007842c001e100600040750b1000c001248020700714881e2010740d00c8081790010451040080380d400b5140701e02c5000c1015038a14050881003000142c413030008a482011441c8c2c0900030030442c0c684c0400512070000d000c034980b02d40c007079404000d00c21425503600300f1110740002c006104844c200e0410440d940e884400c0d100d40a8428140341c4040e5a075134004a0042c400107012211480c11354400410303440c1c0a03901d4944c2c003000c180410410900c81030001c200000c4001042e08442c850a10aa49034a911a5a07461084d10340c00c508080401503002469134034224205040000c00001d20300d8034000d00608501c250074109410380d0005201070b00b00e01016182960000c6034030004050644201628842d1524020084d002c2c0b550300812441711500b001c07003890b22030007600d034445000600b040000170800c01c88080c0021511012681040e0f44000040d4500d045600c0e440d0a8004d411071910b0031403105440f1009500040203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 708926699 1250 708925449 708925463
    0x30103120f031424010201020f250c030c050a0504052203090527090715050702010504050603130b0a05060d080c010e0f071701020906251407031502090f0d 68
    0x1510b100300b103803085030900907548550700c0c900d040f0000c44454a14101d04c40d00c1d606583c01086140004601182241d1140ca421512443c0070403250000c1d5805036104407019100c0c648000002c0305000c0321a08a00454808a8900e4025507690062009540c0211650140440c1e001020703a0001801c19690400381c0c400d141500c90f8540350000141480312007020361012854002e400c2152a0348408041e802450060060000d140f5100020303850280000d00c401c100000880c245007164015016079015200040c04d540e241c0c50401ca0b0b0381ca040050300c10980d00c0c88082c1d000724500d00b580d131041c1405050050110400d0001a4884984650012080d410355650301d010b40045110240004290b07112141e0103000f9035071400101c02100c40e90303103c0941060f4170411009040d40c6d200d108503110074600448500d10110390301005800c2d0072800130090800d0034030800015800001040311002d980c4920340e5280304030703c480b0015080380a2000140d8000b440342d22041401d142c000c601d129010f04c5640 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 708927949 1250 708926699 708926711
    0x30906091f0b0d0c060504081002120711161205010c0e01120b03100207030f180b03160516060e0d022404020d050d09050a0506031003080c070305161505030103120f03 73
    0xc4e4224020308190302c00000a2030216003070048240078400c8100481d080c0c18150304040d8011050a004075001d4401c6040c4030f1110101000c0280500c468035081e40200c1d01c4100072917039010b0141443d0203c81d0708403041d51070308051002090284042545071030060b50350019032945910b0305402031802170303441d135418420219004a2001240001d00495200340d036201c0348840300b59009006101e032400341c0d1203100c00001d002d000903510031041e280d00044d544105207000702c0b0b000f01510b1500c904400c1d00071618200005001303102940e00040c44c8042d29104880544020b80340803615070802401504008050b602c0b9815641940418203030130034002803014402092540c0d9840ca0720000e03c45807404512012810026490401242001004103859291443c03506d04030003540810b02e4000105495004501c9080200041080c0c2c4061a44102200c0e2804200301c2500c160281034465003c200c1d03040801c10100610440669048950050804c001450b40714030946078162450081000c155482d1707 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 708929199 1250 708927949 708927953
    0x102007200616060b04181e060e1606020601060203090d1b051012050a1103070309050c0a0b030103060b0d02010210111e03040506071d0405060d1205030906091f0b0d 72
    0xd4644a20a03110f50400030380e845285080c88281c1d02464003a002a80c01c1c5e0b4000c4001c125555031402c0c545017215009200300d9100c0c030307040000b40480c0008411f80d1041c1d000304a41469900700340d50075262690200c4403107030f03039602080365203110f01084641c0007040d18500a000030803041c40d00c0c0c0400044a0b055440a0326a000300c0e20140c0507a0540e00050000884511241c45611829812210100c8140603c40c906200d000d45484081c000004040d41d0750b00300d0040c03110a0240e50a5441c008017488074407aa1031010034059002800306803000d42c60035028500c0c0c0c1c81d0503c2548011503060f0003a00c903501d86510307481e000704424200342d07840c01800c001480101d035504600d003140c00100e0060540724109420007600d0280000c1c440310078001c0e0f810b0002422500e01c00d480342e005108580114031682d44070082014540b0010005000461561703000d0034680d0080c0c0a14807070b00300c510403544265212a01540d8840340540d500401d464500071a02c0150701076040022180e030702800c2c4038407890141d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 708930449 1250 708929199 708929227
    0x90e06060f0f040609060503010627030c0b0d05180a120e030a06020a030f061a0708090301050405030c1b060d0f0b0a0305010203011802030c030a0902121020072006 72
    0x280381d0901c10b1800050a01035140c102c8074203005000c3c5c07850302506540c1000710217091040003013200410980b17000c204522104603081d440e800b80d07620400c08521079a90360b8880b1180d801000303075102d000e401d1600080f0f0000803c02c88a4044690380000c20781c4121a88610015641d101d28a004000031080314500341d490401a1444aa104050050740e03071881c2e080c02000c9032251002c92802030705103101005912071407480714440c03a48201c030441c0c3c1c034585840c001903544034106e1203903055420041080b00307103c00803001d003010790b0052094139882c1485051000003111880f1041313a00c107000f0f1001040b42c00302c5034040081c489020100281d42140c003800603060100c41d901c12140c81e9000401440031502c102d8a07282d440084900640c00e5080c0746814200720702000341078440c810390311940b400c15540d4115103070903080180ea080c0e515180c06091100e02400c2e0201c19140109100b05850600810910440f40015081404a040110041c107000180a00000304561018040c40132881c2d801e65 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 708931699 1250 708930449 708930457
    0x141e0f03031605060a06090c230c0a060515010c0b0708270616020c0a030803040804051503250e0405060307081e0c0d050d0311070f0311100b01090e06060f 68
    0x1c40080c038075480c0842c0c5c10700070340310389412200c101da081221140350385801030192089200211041a690301c00c01301c50b002507000350702c400612841450014001d20456a00a5000e28280d81d028456410340100645904a80307034001815203a620002440c00762103140c3d265000b182e100b001e16000400c1c06c1000300000f03520403034031900d500007005100c43c10060381807040000d80180060300310a02e42400241102066203c050701c48400000010100000e0034101d6024040050524071142030000d000d024640084075070510b000d48602c5001100501440d507104144002e0b80d6100e540c0d102c020a00001d044081c0000c0c1d0180325400303012500c3c89041c0446c3c540c1c4c5074060720384480320321043c3c00c00786805c0c03c9901b00c5018901d184441d101240c1301081940c0c0d484010300700810724100c0c0a510b003115215004018024110b4840880101984040c1085800d1012012150680002415602110b040313a401c01d001c91405041088a0024084163717849640185186e04001440703120b01d0850f80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 708932949 1250 708931699 708931703
    0x20c07030804060513050a21060b03061008070b090a170a140307060605090609013c090f050907050d0303090b07030509070905160302180a030804141e0f030316 70
    0x10380420209090300c40104420001c010807501c210f47ca40c50113500013040c0481c1d008035510350013a00e503040c003440400d40041481140140840b402c3d480c2a20180c10040c08601966070f00b40220000004c0690801c000d513000e80c8401030000e080303503184c688441400e81d03541500f0400350051244040c00f141c0d090643d941480c03d9980996034411451a0600445102d0b81005100d00380030300502c2100e40722060b015055803031800c050300102044031007a0303040c0b8085040b14400315400314150103101010b00b03001d000f100c0c038a10301800404003c1c007130001030f944103c0c0c0c08140c41e40641c00c1013200f49402086030504a0007401c0020303801394540c4840081c01c4040719a280400d03140c2c802e0025001042081000510391160200420700b0146080c6031108625021801055004139a007200300c0504505644407290040070521020b5587c90000525001407044000400d0400c28603800c4e41880c0b00f8903a0010540c00c42908165204400c005100514000b03240c5c1611003400240e446103018032008210764 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 708934199 1250 708932949 708932957
    0x40903120510090b180a0506010c05070801021b01020304020d02061e03130b010e070203030621010207150c0c03050405100e1e0405060103090b16020f01060e06100216030303020c0703080406 83
    0x43c0c20300501006a56180945038060402c2c0b2140002075034000701403135000324006c0e5010400342c030f8080040301c48545585024000e8082d8140002d0600c03c150b009140307c070380a0440c3c4081e0412a1026800c034081220080c4d040200c4600755001031030914000c00c00c52240d08411a04c071460343c030790341c01190422948030244045411241c81484a01e80c2041e00604401c1003c109918201e40025182d00010f03004601540c085203035030000608507140740e000e6900c0540219203490b00c90070161216034450150702d440d80c2c40c100315004924800c0c41c03c001d4841d05500ca80d447d080c075003001d0081c40c03030402050317500f000a0101145240c0d50303030f2002c00310b039501c40d01c020702d5061600d501000101e80028142c54181480c00d43c240000441035010298401001d100003c1c10602e074000503400c0001031020700388254680b180c0070076100c030100d6416020b00816104140348070800c000590740e0f007100038031200090480d06400c1000910a070002d07c0010008010340301156a02d550784070f5980c005800078004a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 708935449 1250 708934199 708934231
    0xb06030c0726073908060603060105150304020301020915030a0515100e040608030a02060a0f0204180507120e0703150515090910020a080406180201211d0c0a060207050f0409031205 79
    0xa2071700700700151f04074104801501955160400040800400c0344035a2185e9501000140541d0390030741c1507032120071000d044842c480b100500304a9070366104030b501140080c40c1401050741c40c81560115058400b0103428110a54400ea4051b900c0e00d6014503404e81c0180c440a000c03500752000d1000c1e06100fa0700c2d800801603800c04280201c01ea400c24001c100c5150710500080080c0380004501103805405004000340715128010101c40306544564040172203810304c1a802c85209001600004403409004031045020003c0e03001c80c2540c2c4140c50f4035040c3d4101421740d42c0341d840c2c000010341d00308404ca400c98034411901206070042c1d0704212540404108490200070500005000721917400d810b081c0c1008081166a0000e0f00c2e2401c21b003001140400c1c0500c201d043c00c100c1d94425100582809085040031607442c5000e030351002d41200440c09010303040400180c803400050244142c0380001c004246203508501440010003058006604001000b00035004100440c0310703450141030740c0a4603e0724 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 708936699 1250 708935449 708935459
    0x1309030801060e1f02030909160f02030306030604021912200102031c0c09030510060602010c0801060f0e010926011d0a080304060b06030c07260739 65
    0x440314140e0002c0107000700c42d032101201d50384611602c412036082070306842841c80754504c00c9186000701401070b45c11085203001d02c407402d6010f070301c01c000318106556030942241107d00c0c01c1ba100d00040d1981038250344403501003801403608006c100c007226800100906031a40d40d480e52504140b2130f140036509114a130141d6400e828001d081c012940d0401e000443c0b5040d41c030031503071104141304400212800d503940344a0006030700c9001041c00440d00141150180142c2800d4000209031512440c805076203000d1128440728060610309040b2103103501d800301100906403050781da440000300383c40d04104005c0004240c0142401e520003140d5075072078596031410034841c051802c4503040f41260b4405c01007041c0b512600140004c0310324210750300008207902c9484e146011005000a41c42095000801000700310081903260054030003c1d01542070000c5202c10100015016511080301c078032240803c11008001c20703e801c559a0029a40303072a8100e52086642441071129408441002600349003c01000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 708937949 1250 708936699 708936707
    0x503060306011520030d1e0c080f0c07030318030206061302130506071704080607080c0f03060d0f320c010f0f0909051e0a1407180302130903 62
    0x1c09030040c40302980ba6803880c0c1901a201d46070403900c02c004c5a4100200320b04160b000d1041c1c800ca02c1814a05020300c0d45000040b689a402401e0702c10205807801360105c400c60700c201c041c3c50007103841c01c42100c42601c031403489900550103030a09a0906485004031003000407002207195955000343d02400b10740c28050100328600380702c10404c0082d240148119200601c1d483e400b03030f0849108481403541c8100ca40340c880c1250400030000e108400c0041030000d1032200109240c0e01c544220f9481e0b030725540d101003400c5054080c045284611403070500c001001c606128441e0f40321540201c00ea844025607658400e00d50740a03040d4841412501e44e80c5c940300e507020b04030503010b85140a50141502d80e0100000910860104290004112a225010304c1a500a801d0b15000c8e0032100018070a924040790b28091016046001c05842e195440010b200f0140b13a201c0d681c8100240000c01d20162101042100e6241c100f440c60321710b44a02180c000010380d1440780c80d1007100c0c01e5801c0403840c0401414050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 708939199 1250 708937949 708937951
    0xf0c031a04031209020a05040e0304080f0d080703021b01051009180f020108041b060e0f0103020705060105150c0f1b0102061003020d06060506030a0e01050a02041a0f190503060306 79
    0xd8210394501091100003a0044204a60081c2015000801e8140741c00010161506548050f8220b881e0800d00d40401d0700200c010004d4039030782c1c0c04a07a59400c45650f09551202d501140034002040c00d800710344d400c3c1c4603400501d5150140300c407040d164812200301c1402c40d901941c40c0f8440aa4100c1c00f08603a80c0340740124911000980e407001080340c160749031068051402072000341000f4419000504000850b0005030050060801e2030042d036840f1000500440780000015200d41042440303264a58441e00880f180194042c1c05420183d190000703101000403407440c40300081505010405203084100400c1e030300141c1c0c40700146111114461013000001c0e9904080781103400040c108880007503030400d09411241e0503524120501d0503810520300904494000302e502c00e100005004c000710158000003081d0300b8503402001581c590080b040121312980c402d05481c005110b14009002204102400382c090280300c80c98503042400400c4000304641d80319035004582c1c04802c1c0240e5050801000e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 708940449 1250 708939199 708939233
    0x24031113090b0a12020d0305070b0f060a09090809120c1c0b010e0609042004050c03040203010c1b15020919030b010609121b1707082104061b0f0c03 65
    0x1283c3c0e003400d0028180d070000b40e44101038061001c1141072010944107008480307520740c014440030840d041204d04030281141c180d483c2d030300c81c2045100109409160b40718003007000b076000840a00d414412820300c5500503800c120150745d8020312220708003d85410906007103078a010000328100b22000d1400c091b42c2e14040c0c004201c5c0c0a01d4004004064030b844c0810794110350040d001c03440032480240b134910500d0090f0f05041d0014182020701c0300301100c02c00614040d52084000388859008a80206d440d90602e0366055414110f4001020100303840c100b84e034100c2d0b00258005850a40f0040103d401c112418420301e15002d0065000c2060004000b14507000d4240c070f01e450080145003882810300c111017a24090204050700084003d0b00d201c1e00301c03d80082102c82c0d10514160000034040f9110310b01c622940ca083e0042c440680041a40c074035080444092030041a8141410036404494405480d5850348018100d0a6403e000c00c010031882d8000603c19072050740e9240c00c6140903e40c88030b41c050700c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 708941699 1250 708940449 708940459
    0x60801020c0c21010212041e0c0b1308011107050d140301051c050d03150905100605030915010803070201140702010e040213030f060606170124031113090b 68
    0x1102803040070109403002c00391030403a4820b5440200e240712900d02900341c0b80340842036100140b400d0b0007030100303c03005100702d004020007640068030120101c0d00c0e08000d0001404d00d103451a05204004411001c3d02e01400590300850040b9201e294107821500e41207594020b10300302082190070881d0070008014a0b102d07502d08085402c0741e0811510702404103001e032600c22022034102c1d00c941410036a0b0741d10017a070054101c409016400c00040d00030103030700c2041c5d41440418180403075041e4042c05002d008440400c0ca0511152a09008031034640014003000007500918010004000307030140c0e0280609441c901179582c1324407620014180c2d521131980c441c504a400c0c000e0001507a0040e41c440c07002c910a440c0980d5450300c001d0031048140380e85c0c20003043c0300e010386180828801075600c08d2058407039135201d035000c2400b00114444060424411098035240e040d844d661803e00e05000f501b002d10700c078140810507820b6080c0507041900b00060034541d0094003070080021080c1c3d4003a150b20740303000f654 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 708942949 1250 708941699 708941707
    0x8072613080c0f0f0f072102030d08040b01050a0b04090203060a0e01030308010609150e040905031c0f050c1606151d1509070246060b03063c01090f06080102 69
    0x5e49546550f6540704008540004032050348401681c1003400d100c1c59801401d0303c904003460200500814020740341603501000c10302c004105400c10642c1c43c002d595010080c6030800b0b1801800c40d0196100400050708160b81c2c0000040300080720084501a501c02d8850620740e60500000500b41c036025404006c40d41c02103070300d60520541001100010960503140413400c0721050a00a195200380c0d4002c0e1440e01c018805c03540d40ca50b45034084107458880356801c1c40544c0390b0200c2c644283c000c6400c0c11002c0413819140c2c0000461681c8090802541e0903003107500306558280038500c4006846036224004910b00800070440c05202d0300c2e0410007000c55400c51a401c0000c0d000b580c51242c04201000c007108826186a0070320300315881d515141c481004001107601c40c4039243d40d403a4138a90100e1302903040442020b11441d002c515544181a1017108809160010710540c9900e003903d005409c201c2c8a8809008442911403501c5000e0800705102049203100002460100c40c030b554054102a4030501c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 708944199 1250 708942949 708942973
    0x607170615070c0305060907090b030105090c12010902060d050a0b03070605270303130e090c0612070309060c091a03010b040e0c040b0c010c08072613080c0f0f 70
    0x44545004141d00400c54072900c8524207825506455040a026840740008121049030001035034000c0d5070262500344402981c2000b81401c1c0c81c41601c1d038031020340000c0e0506c4940d09113101d90303008080f07054001290f400032503000f180385030348507004456415481e4070401c41d2220480c0160300e21400160010300710f0324900302c002001c602a4001d14118192030240e552148103140b01c01c0c44a2a10050170b5030ba45240ca00041060140c8612801c3c04801c10311001400346a4045003d80c2c0020000c0c00c10380c600400141108100d0718010b240740c06159540301991701180083c03065402e10149502d610701c1c1181480c04185184030308081c00d8807041000c20050102d881c003103050300c00310380d800030202005889841081000c2d020b6500000c40d590400300390382d6000b0a05405c8001b81070640d40303602125440d0840c0480303602c00c14010106141520ba0a2100840d06141c0c02070361064048520740703040003250350303000f4040e4443c40c044070300303903002810303c4100400c18840c1c003564032140c000504450a4030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 708945449 1250 708944199 708944209
    0x30603060612010f180605100e0a02090a261009210e03060c0301030c0b09010e010c1b0b04050405010909020a030b07200d0305011e0e1803070506071706 67
    0x1008180901040c03540b1000d188002d4004103007180c1d03075070828002541c5200003200303d1a401c2c9403d840003030803d00810220340403101030700203507480001842101c0e91600c2000c0b0296008410880c2c1000311144000344060705020521a1341c04e41c07420345252045c50704011850083c580810104d0a40b60080f60000903200c8008808109240300d01210091680041a100105c02270203180d01802144104824046444000d5050303907c6501d0184041c0d8551003034880900800102c1404111002c540c001c02d50300441a194000d8401c1c20301d40c25104014207910740301161580944818500801c042c0130701c0c60180103140c0500402d0204000d22845500000e215019900c030103042c9a41400210f906584a4000000710104980c560034030922140e192030341d0380c00e07007803500c81c00285044004603121500c020b99603c0c481d5800d080380080790400680c00e00e64000a00070342c15688444440000c0740c1010720151542500410140445103040728010301901c23104400d0346403403484002040896074030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 708946699 1250 708945449 708945451
    0x20a030e2205060a0b070b2508040807060605032a031b2713030215012319080a052407110102090a090501050f010804120807180810050c03060306 64
    0x7025401040a40320503020075480768803500041c4e20000d000842009029103d9441405042c82c00150001c101c02118007a130b0a0b4102065100010010004103001c1801c01c0050306c6124060000050300c42c4e918400a0700e40000c412003503078000710020301d10f10301e415030035150b0500d1170060b0054029110816903898007170400039172503407084041102a03850310220b5140030150904140c090740f0300b414420401c5074144452b9100b1001440f8010740058004401340c029412a61186034030700c4802140d1150340001d9050b2852180c010901405044001d01160f5480c802011a400540342c440c025041c11810281004c0b4100226001f5244c242d003503441c00700b5955400f40035803902040008010b52080c0c068481e8a0315540d0005060070b0120b94503869070b100c01e040352002c80d035070000030f1190001594100b0301218040c050400c219265100e890086030140d078440a50301e08482c02040071691480070662a420a6190780e000f469005000006407040380d0300007901d99555419840e040c000266a080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 708947949 1250 708946699 708946759
    0x1e0e190b0706020a1b0f02040605040c1713020a0e0901050106020a12050a17040b06040e1506100c051606201b061b1b09220201090e07020a030e 63
    0xf0340001c150000510030000b003290a8803080c5451071490403801d109402440b204401d07031150703291180014052600740318241c60304409485031844054a044486200c80d4002c00308983c180100440b900141d41e1441048007501010b82c5814880c01c051080354211030b0142c0004040d94064511400400d44803010a010202c4500d41103543d801d100c1c00031990b0030040b808034004920700301d0030300007003101d2403681a1060710213035003c105500e034a426403590f1315864492089070000c8640400c00c68204240e0558005e016824010440c000070354aa51a0080c056074141d4210781c04017050101a40c088249d540d011804082c0a04100f0201440d40d101d2541e034003030030f01030f40d61000c03180103d840c2d83c0241c802c00752140040280200c1c0c82903a40f51601c01c1b0012040c145150410aa1032511348518941d004200a82a81071441c2c3c000d56240700c1d900d100c0b03a080e410b100c003020b40090900486580395218042e10313406024280070364540500001e50940c4254072901c40005034400d4124004141d0030007403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 708949199 1250 708947949 708947951
    0x1211010f18210909020309150a020a0216050120070e0c0a080601090e01060503060310020d0e070e09150c0c0109062c030d0c0e030607080708090304120308071e0e190b0706 75
    0x605c6400c078031491b040340920440d40c0d441c40701e000c2189c08480c80e8041c10900c00207400b66030807124003000181007613006004260201d02e550204000c20034540d440903610064260880c1c01e01c5442d41c00c46403080408942c901503010000a614088952010701c00c1c0d0040005e0074160a100d0130311301800c1414405000752005c00c10040000368a5580c1000038144141e11040115600c8510703002d807001034840c1d0320203c0c06510510388002449500c601356a0b21030320104002c1c0c480754441060b80e03840644050224842c48000740700302e60061038207108104e8218415500020b04001240c44402d0394ac20302d12400304c030400c02540c4140d41b000040201e41104181c2100080d1010380d030501075901c0e820b4642c496030580305131002c1114064001c0704040c000d40c003980720300207680d541e40c03811390741da200c0c40c042c0c040c1c110700403100500005c0c0656180381e000140b50505121203241d5810041e000c84100350b064000609a14002c2d050742080b000e11140007108852401000e4105981c00502d4450100000e01c030b0303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 708950449 1250 708949199 708949201
    0x120307020d060c031b090927060506191d060103090209010303181208030106031b0203090d1a09060411100815010c08030702010605010212071211010f182109090203 72
    0x114805e0780a0a00060010580b8802d903105900041245002d8000c1032046481e01101d0f0300071031714096020651448617101291000000da031110042c1c0006004070380c110740d200d00d03005070f001120417074003024120908007600b409400c0c2c0c107441000540503014a0601d40b8024192002da1124144281520b8140c03d0a0950714544402c40d00d84100907444195464030708030300e440c02c000c2040001d50403180c85030760500a41560300e062210074002c82c404100941d104100b882c4860038a40d5106580c64081c0c00344041c0c20210725558a20300c04202c40e45103440c3c101e20b08100c20010540d004a038079000a46040c210404810001f8084c00009801529800301001c00b0401c0f032382c4100c03660729800f98030400143d1a401c05103030283c080c0141d802a0740c0540503a22003070304c83c0300c401303000c0d00c01c0c0581140c1c80c0790340a4121001038810042030040400750b552540040d0b20303104054000c000c1503110f401060315018511b81058030050582c00754165511000c006d91948495100c1c03840c40c10380e1410000140d030b03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 708951699 1250 708950449 708950471
    0xb030622140f01020c010212010e0903122511120309070905091002070c03120c03170415021620090c181005040303180b031303121505120307020d06 65
    0x75040c1e0090152040f58000980d4480300300c2c064001d841c03102c0c031400d180f003400d1341c8606010300442411243c03140e0340c0d8401c0c0644556400d0b0410042d170403400d227546126200e104c022600d1031011308140f00101041c6c101049460f40f44041001d04206144e080145041d82404c059941d15035110744184041281c6590215040c190240300c009104002614110b548131031a14050f83c2c04001d074441507074045c0c0014100501140034806003881240c0c15030301d00140754000b080f401e10034030000c0c1059460203058142524800741903c001c156940030722140b070000c103a807840c1c101c0846884000441048042a02ca008152039150b02550092150180b060701d0b0001b45001c60f4600c1c6c0c0c92000150f0210010a80b4401c90b80c00c00010030030381c3e00076922085010b06600c42092040443d102e018800007040000903a1801c1c00182100030a11924100140300140301c44002590101c12004e144c0e504490b40400040c64a2501916412490300182d4102640c58000501112050f0720203041c0316201e01e50b00c44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 708952949 1250 708951699 708951703
    0x80619180f140f09030a09091d01050103030201020c16031505061302030705030a0c0512072601080309012309010c081b0c040f0b06030a020705070b0309010b03062214 73
    0x842007001c0c440400c5403590151036506151000d030380c12424510101c0210306503050110491b0340018079034a8403102c1a1420303000c0c0c0d00600042d031080c400c404203160340745030000c400c1c09014000c0d07000c1d41c000740e202c0b542d00100c0c0381011191265418050008001080051070020000c507079020360300000145641d03202d000c19030f49600010051060341c030000401c0041d07600300340a03600803030010400308100103503000305541ca071140c51204c0412803489000035100d58803030340540304005480c0709122a0881030150040c10408280c01142d01c1d40c0002c00e03c0089540e00018856280c05803c010082d851150040c4528038807900103160304000c0101c02c1a01072081140455120412240b84009030405610000c0e80b01d154a008291045040a080354485001070140f0000c00b403004060324616110000030702c00030340c01140700704c609028000c80000c0d10082d0b000958441c905420001c500440c0150415050003001042d41e0402010400e2800040c04a08001c00070640e0110012080100d04c081c40c80c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 708954199 1250 708952949 708952961
    0x72003070503030a090305011406091b0c0a0507033c05010b12010b01030516020c04090c09140703110f090d240e070b041401080403030e060705070308061918 69
    0x190580f000013020f110a581c400720080c00c4a00980081103000c0c00201070081c9030307034191881e541c00341200011440120300050302120001c0f500c4846c614103003224203102d04050180d0001d031107036004500e0400138012640c0c2504c4a01c8401d06050074842c210415840341d5a00391500c0307442c0c002240014200f0000258044140400020102c141c00c0400310707805c81c060048049100c1c000781c04c12011900200111040d01c1d48034404d5006040c8903d000800d110040c0528038094800c85001c56000900b5041c81c071915400c40d098140303004c0d407454210030203000d442403661080c071110070421540382a0030b02001920716a03801101d0740900030003141032018541c0042d040d01d03403c000b06c041c0050b507100400e9115040c02814641942c20040d51181e001009000d40c0c0315000d80e540f00416510003c0d0320401d481341d4071a1190a0014403900c0b0704015901e05a41101c035600032a5002904805140e00030a40d940e002000320b03030444010310401d8001107504118071645080042014202c101e07161240c0200d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 708955449 1250 708954199 708954209
    0x3121803030a0507020d090b0306011b290702070609030828030506030f060f070507052103040b0a0921020102121003020405060102030a080c0a03060321021207200307 73
    0x203a8607401c1c40b141d80c030003c0809441e508054890305590200c12401418101c0c00c0380c11240c502800c65072400015190b0040b1011105540031211081c0400542c1260f0148400322140800c1c0300058690400300600301d602400c0c03041990302951080013141d80c0502d28006481d44111050b41b954400032a8811081c0d91321014008018010351081d440c6a265208078401c0c0400c03011200040840c4507955111042074a00e0000440100009a42d00d03014000400d02c0c5489081203d12421310502003049121200c2e29440340c0060000500042c88619400c040d0451860001045415615508c01d079603800e403402c00c0404920405050a0494000e5043c2d5401d1202290b1203c4d40f0320301107150703026081881c0400c0744118a440c0100305154800402d0b503840402c141c681403500c0d00c0721380000d051a00801e0084040507280c00f008800140384008411040c2209150222040c0c64040064241102d100500b58462420320a582c045680d011100c0e032200c2e49096001c101800020109060210903000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 708956699 1250 708955449 708955453
    0x60911040e0a03120207030e0906060f0406021011042904120809090c0408070303050702030c060a08060a151d0a0b19080105010c031d03010917120f0603031218 70
    0x512007040e004205901000d02ca41d544c00e40400903c120001207014050018001a15201008085042c9416501d402c514010001410100c0a001c1c07910a9401504400c0061f04191200d030341c024194001d00c1c2c140340000015500b030909096415426041d0b098000a1843d42e031111440c00d075841c40100c502500c81c1c1704102c007089665081c0905183e2002680070b01881d2104009034078100707980d0a0302c05803003024019000345803075910125119001503a040c3d03814010011074040c0390303840b640101105001c1d6164944146018820044840c0e0b06900604606980360802004581c0c400312000c480c601c4004041026460600480c41c2e82d00b41e60004000d0032400140c1444030b4044807404104043c0599030307445182e80780d000455807044400801000f040041200e09003810f00002c00c1521610040d000003660340050b1240c8808190241c2d401708a401300080b0f10504031140315850794090042c1e1404003050801c1c401003a40c030701c11100c52044042c0444040f4441743d5411440501030a40402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 708957949 1250 708956699 708956711
    0x6120b011206060c050f0f19140313090e0f280624060f05030c030a0b090103110a0b07200d050d18080a0210080a0e1006031101081306091104 62
    0x54042c0140640f0b80041d51184114000001c403040000b4000c0041c413407c1c0b01801c4403400504402400b4081403100b21410001e05050502c0e80e00300f00301404048240d52410250300d4584040c1400700c0755012009040f9811850340d1203412200002e08140e0403003207a00c019a00c1c1c40080f070180c6000e5940c0c40090005080165910710460540e2217000030050f080180719401347d44c0c41042d114517802452440c0450024000501c1da4801100610380c403041031103010070b01400080004500b10401d070800c913108080061444000c1c01c4c0790902002501d00060000d00e00042521015a210b0702044000c03c0521101010b50705501c4a82d00d203448181d2100840b000462401c0014000e420104020040003005000001e00300b540083d40c81c800e940c000d45800d00c143d60903103003201c80f001f0050040502944134061614061802c2091044010b04480c00191072811843d00c5a00d10b1034500e451410002c440c800d00035440b25520345840030650001d000194140c151801e0b042142084d11403070341c46071400c0307 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 708959199 1250 708957949 708957959
    0x1b12121401031505010e07080705160b0702060106022401050609040605092404060e19111c1b02100906150806060907031a12030d05041a0702010606120b011206 70
    0x10002010940301d0014085680c075407003600941b001c02c4407008005201d400205a600740200010680f0180980401120352401d848003074010209840c55801a8001c10041000da0381c18850800c1c88402c00c480c400d141403405000c000c240c00c041c05014810075000070040e0f02d690f55076000200070200504040f0141c0342281c0c004210042002c5d00c5176100c4242150f41d4480e2a00303200b00c4050343d0604c074116040d0303216130b903403513040d51000301515418a0352130680b0203892403078201402d0f51941c1100351900004185c40840143c40d6200704a5483d460341c40100c0c05445d030045000ea031050f040c1480001c4181030b0b418200b01406007407a204d004260b1425002c110170038007051561041c5070640d02038090b511011800c40c211984861040008640180c007e215468140344102c85400780f0003c40341841c0140d00f140c81296004c0d01c003202c0c811160151404c890100030752450380040d050000f0000c0320304c0c2c07280241010444084514120350381d403072070100b546c0c0900382d49845a6a504801c004440d211 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 708960449 1250 708959199 708959213
    0x705130f05091c0822060b030708030903070509060a030305071b0902090108101a070819020a03110f030406050c0109060f0b040b0402070819050d0f0b011b1212140103 73
    0x311080c08120718400c90001402a02e02c0e80c000d4020b000d0245c1002c0e003210782d60b9113000e20307404104ca00d280c0b103000c0c403080e5a82c1000b400014081c950082d6030340d058280201403038111607503c40350080c0e41300410012141e8800c0ca25078122038150822a03552807031031507c0b9502e0000d003140d072840d08100c803c000c2024a51903019241c1c0301c800781c0b650b088585070701c02d1400160600d0320500d070780d070070f20200d02003d1012254003030315440d8410541c01e8103003400c0742400b1a6000701c24030715000503404444c03a401810303031201130f4025920454000e84552900088516140d210314010300342482000168030b5105d500944c0410380741500310808000342284650041c3c060202c1400251042d82400c0480b00315140510031100010380c1f11030f02d1843c0c102c205007240d804246409945d803e000b0700344004420440ca900800c03002910700440003840348520300c00945601d00018414090b00f04800181d00000d00e552081c010501c018141a0364017550303208110040d00c1000c112401c00b60356040000100584 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 708961699 1250 708960449 708960463
    0x3110d02130615091d040219030506010b210705091011060424061413061809060c0314130804050d060e0c0f0a09150f1203030b0307080705130f0509 65
    0x650381300042c03980d580228070810407440c14103440000e4140d0100b0018038041907201d2182d8122101c0300c0055039607454680c10a50240d01504042c04005072440030050708205a40c401d0114000122031401c0008000b4058090000894081d14881088004070b40c080c20be100c030f4000382101150900d1400f850302254540020603032040e6003410751000d003180c1060303008100c05e4948800740e801806040804200140c480302c0d800c10b51070360b91641e002c075609640724411400c200070291302050103501403038100121000b003071402080610b048030341814000d2196405400c2a00f5800030580c41c002c60130181d01c00e00c2142e100c190301c00030744100745040101e2078025803644a0240706469000e40c9a200344208001c1e0518038a41c0180700d0b01c0c1c18031107007091745e0261414600306103900d414142c0702c02d103c2800102c260040e05014200480250405034140102d0398620800d03000340182038940980ca60707442c070050159a00c1920544d01349a5041c2c2e413540300a4040f004039009210700d04140982c1c94231034003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 708962949 1250 708961699 708961739
    0x1030809031e031c05011401030f20041a120432070614040e041b0803040611061003110d0305070501020d060314030319020309031b070f0e0103110d021306 68
    0x42881074100c04d404043c81594101da000307011070442103030030100440c0100154051443c0300e0b95a082c0900d541003000a9180031000400c225559460501c2000c0c43d59072207802200c40740c031400300301144050440e00150ba0300a87d02c49944030030111030b03038500380c00f0203c107145c00e200c0c0d195a1410002c82c07060014451044480c581c80b000341011116038a002c0707030322036405050039107042c10740490001910017001040c04d0b164150040344468689585030b045601560040001950b0640050f103c95024000250004130803568000c03640d1a40c2c1e100722290a8200d00c442c4030b0304085070410149800f5000311020b8690007802155a40e0001401e900144254001a01c1d90351066481c0210900e00200b00ca0045c07900b0050310014107607e080c84000307548021300320342c9540400e001c00031080c0d5003464015120100c02c00503117825030a00500e016492415803180444110903030041020480000c68440003031000c2d600000c4408503400420403650503082003442d075616200002504003180f00030310308048 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 708964199 1250 708962949 708962977
    0x30604150e0a050a0209072001060e0708041a060d0204021204050f0d0503040f021323091f051305060708160527150a021e070e01030809031e03 63
    0x48811501290707105180302c0000c055510402c104405840c0c900c107940e81c0b042c400d02e018009280240c0c4000948040c141c500340c400e80d150841800030808080045600040382d01d0240002d242c01d40350400840074121804034408903123004a038146c0c4584000040454002d4011356403400704080c20912801c0488080c1e846001d12200d903c61000f020400300010b04032a6502415500d0b65114003801200c1410300700d80c040c605991300d040002e46c5000d6218500b003801c600e400300b0030b241452200c8002005240922030303000343c40b04049590900c80c02050204c40d23108002050384d51120f4410400d00c0546000d0000d05c104000c0000d640d85c0060000c1c0b0031100c48a0080018440c00c1f001e0341d542c0240d802c0080c00d00c2c61000240545085814a543d01e044002c2408020305c20006805496901000b032540050300035012000e112009490780c007141d00b00b00001000111b240c0545401c15036010f000081c03a54000007808100c9550400c4182005030b03286082d859103003400e410082e40c07076001d0b0306170019407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 708965449 1250 708964199 708964211
    0xf0a05190306051f020705120303160f2106082b03090f150b06130f05030708031e0d050c042423070b010f0303090e060f100e03060415 59
    0xd44240200320480d44050f001411a20070400c0b45000315800020314000c6202c0c42c4000200340e55564810800848800c01640c3e0340d00b4141e17003c070400008410000c0601a5140000ca1000d0f48043c4000b40c10f01003c014401842c464071101c4d000d400c0f15404041c0d54400c84070300380c21094070b0a4080a00a0814003800700c0b5104030b08007502961000c0c0300c00307000d203520f00d030300f003008142c9a104164102012040004269203154001100781d0403881034101c03101c045050502c01621000c3c5104042d1504034002c0c0035917031070f150104da42e912a0f840d2410301d503000001046242d0342c0020690302130150248003441245004600c25146d90454842c40140303e004ea03400360038445001242c07424420043e61a01e0910f0070704004c000c0c1c0740a00040368040403600b08500404104c3c12030a4501801e082c01d01c101c032162440c00c1c0105850411b8100d41c6001d40702e03009202c0d25540b40044171106081c03da03440c60251100541c2610a10081400f158050051908200410080d0386000c89908000c0b003040140d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 708966699 1250 708965449 708965497
    0x3050f0a060503030a030507030222210f02040b0a0f0602030310051207060305100b03010902030a0c0203040f030f1401050f040c0902090a290a0c0c0905040503090d080f0a05 76
    0x54901c1e502c541d40d015007041000d562058401d800030fa92165050501519000d10f0602e483d2109121044540501c0f101e15000d114448140c19190300481150341100246035103501c802c42c2a5400c2d00d002413099654104445180d1988113010300100200385540109581d00c00b00a503ca5208036801070082d41c10300703c00f24007480d081400c0d00c9070115000c010078049080c20000d8005080c060f002142c1030202600009402c1c00710700045010f042d00380070168a0342003d01c1440269581480f410007550024003092101c00242c050b050101c17a0006105007030010745091407000c000d152915100b02d54205010030030400c6003005c41c24082c1e4411403180011503074840c10f481c22800340d20f0751550f0140b0004810040700b243c0c40b44903210100130101d00d203440840115242c640e07510000c081004108555982418800322860110080405440502041c03509507650394491094041152140824901650030f202c0070401392040341d2411218a550307400e40000c003902c1d58000b0701920076085515a41c00d10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 708967949 1250 708966699 708966701
    0xb100309030f260703020f1c05060d081c0b120109120f020d030e12070b180106050a1205070f1d091c0507030e030a0b09160e18071503050f0a 62
    0x50f400c2d48400c00080c41980040c04915100c001401c0340381010303001d00c0b482a12565440041c80c0c0f84680c03000c2140d42900e1120709074152600201054401c400100e840790110750608122140308864203070f072050702e02d0303450f8800000380315880409070018400400c0386800903056001c10041c9000382c00802e11800000c0c0100d4920800f4001c40d40160810304e0450383e00c074060b030040d1103002d0310001610080240448007a5058002803421303145401c164003400940401c0c0d4034090220703420600240142c0e807c00010800200c0780d0b10a5041054100543e075041c07003c1448100c2c0a41079850040c881c2664070801180c2102c01004400400c044c00c00100329407400010b8001181741340442e0320007407103c0480c000d0311039802040041d028400d030301901003450f5800b4401641c80c14420708804c021410182c40c0c003882d00c1134484200324121032003141880512000c6850b00d52003e050103400440340c07a1140e18909203982c80c0d20040d540c010b40b04155140c00d030035401c8140b1404104110582d1aa075412000c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 708969199 1250 708967949 708967967
    0x7031710051e060a1b0b0c0a0801090612080d02070213020415031503030e0a08070f0f080a0c0e09010b09040803070f02071a0703110a0f110a0f0e06040b100309030f 72
    0x594400b00420514000c0c0b802880b01d0350345c1c4216010320b005201501e03150b01d40d58420031030700d64911800020b01c0d110100c1c0c100c4c50050241c03c42c0700c1c0070010b035814505203001d01c1400b5070000d4036146021942a1000d42990102c5039812fa0250180c5005040c180018001c0d422900600855644405034281d00314480d00ca0700c000c84091202c082c44851954070142c030703a19882c03000240c00c040c0008010a103400200680310040401c030500008041c94040164031100d06034012480c660000007840002c1074400e624a800e41c0c040f65420055600c1e030800490052808808842e0041065001c220620a03518090b51103806517803108940b0f8004a00100d840c1e403202d019119414483e20150308004e00c21401034070130544242040340480d03074500c410b24900005140c0459000e4140b0301ea5108000801c0e41c2c2030600802960440c3d0b8040c00c0010aa002d20035601030a00d6070122400029140e60b50b1b50071004112a000c0d0400d14001c800070401400b8106440c800d9001c5031071000c1100142e0300c588806 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 708970449 1250 708969199 708969259
    0x2c150a090b0114041811090a0c0e04052e0f050907080406020c1618060b09031002090f0d08040905091c0c0201030e030c010225030e060703171005 64
    0x7003850340e003020802c2c0014038042114503046070342c4106450b0484007035105002410300a0740444000402d66080281b9000700074680d103c0b5a04000d0103801f103940119a580c04500215000300b190382e14480202402c14400c1a941d5000d80500400c64003281158081c0082d2450182a0794034107480c0c80a0203a6418180c2d146000121030400007004202e165010f80f00900d44030099031090464a41901401c81003500200c0714124256a8000d090059100c3c0400800303242c0002400c00000800080d10303080764520030084590001841c402550320101c0c8920401e00042c003400c12545076003040030060304640110034441c0c8c58500401c20040001845080604200c040c1c41d200c0c46452004031800d0090110481c1810341310705d60f01030403101c1030015100c05c401c05000142c0350340c01f90740c40d048400b56030030005601882d550313030f4580420741c08400c00c058600d091302c40c80c1c0d842800d45011a0124074584c0c80c0d18488a11206200c43c0d0340d803030b400920449200702c03001003014448403440303452940c0700f04a07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 708971699 1250 708970449 708970463
    0x15040608012a050708070606050906030d0905010f050c0715200d030905030c151e150402030c0c030304080714150a0513020d0803010801050f010807092c150a09 70
    0x2040100700d0050b0004540e000d1894480e05007606641c1315482908034003070407101745440342d01c180941c0c18a100d419030b0020303003100100b140c2210314202070801d10890007158100b003008010303032001034052000c450480c1c0984084404031a550444010b58000030364000d000a0810360440301c01c101c0f1003481c4901c2c1055007000e000d603500d6440c401d8006080310001100d50b80800c1c03085084910090001d08003144030049190454509280c1c10211050581d20300d003554010306040c0b110b90320b11090b9804104909450050340d9868080c036514003401040405290341c400001040b041080c01e8000d0904584a030810003d6220032220b0243c680d17a0300203c2c515081c3c804000610380510540103d900101a2440682c0001c07550300803504ac081c00314020740302608004010080920248926a409022380b0382c04070003541042c500507102e080034400c08203400d8440501000c0d4981c100302c000c6031700c4401602203600c03111030000710b500c8200f2a40b04804007841c8a000480680642c00b130301c0103680e40415 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 708972949 1250 708971699 708971741
    0x30c030706090b030604060b1306120c050d150e07171602100f0b0612041202011e1a090a09030e0301051009110f0c030c062401080403171504060801 65
    0x5003c1c00c1c3d600002c00c2680e00940360040003512041000c001d100c2000340e1044502c4083c10080040d00380d0100c2240200d11500d404601c4000c03550000a4440034020072401007400c0341440d4840c41c441071582c0280c0f81801c0d40700117208045411613214246080b0815400300380760b4030411841c40300b5419103800c5000d40c01c0713030960012041c180d81c0042c29888811100007030b900f40100124100d80c0100150741000c0d10a03c09010900c00b102200d09148001c61000f8420011810315406058201701d203030030714040d03c0d000c422230211a895020004514041c1c06070509140503141000034041500c81580410300414203014241818050584500280d10109407098a0840720b00700811352001c031400d100c081400645040d011600042c000300301450001c580310100c00b030126040040182007003d521101340c103034002d41514101040150720007428010461358071410b054400705040380390b0840d00780c804002c12503c1c80032550b0784c0c02020340a803401c1124139168200c042c200c0740d90b800c1d03c1c00c003610061 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 708974199 1250 708972949 708972959
    0x30f0103020d0c0f06030e0c12031b030702130c0315050f010f1202210a05100329070503090118020306040b0601110f0601050108071d0f12060a0902030c03070609 71
    0x5566948118411185003e1981d41d506005100780301c1d58000100283c1c40340c405020105003001f00c01d8004c24112140070040e00750b20141c40e034038810084061320b10b00e00d501e0464074851040c800d840c0340326000390501108100061194008059400190b00800e103004894540b00035007255010a444000e0027040b00101703128010f507480781404242401304840190b44503a840010b00142c8030000c2d082e14401c05031080c102c165a2801001452a842a031521040181e20381a01800108481c4c018039401c4c1e1040740340a482e0a02801100f02940c0b8080d00d40511800c10340c094011803103542290b000b002200026407a006000c5840d000183d4180c1c09030001c64041070500c416280c0001c0141496029580e82039030142c20035845004031051500008010046940c020543d103a0016543c600420381091901c1036081d0702103482041402000d0510305078070a502c03201038103907a038103045007160b01600d04009480c2c050a10703643c0884c0a40640c02e1101c2c1c40f4113001401c41305a07295511182d07a0380b4240 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 708975449 1250 708974199 708974209
    0x60e090c040209030c121e16030f02150313050c01020c010203032409010603020301080d05031e041722140109031415071d27060d02040c110111030f010302 68
    0x919040f0b54540200c10b00301c0703115610020f040341c15031081000b03051a01508600350002c0704a0414241c0b0f16007008005514401c00664054140c81d03101e42e0060304c011690020070154100d0b41c121003000304000040c0400c1480c00f01e0307450b00d02403140e0102c440c40c21604004a0325440215441d0740503034010300c00b02d2010481d88160244c0c440b4062075003800105800c0003d10b0710142a0700000202e03a00000500005000b03000568040c10b0604010b46181400812002c2c01540c003c0c02c45426041d0901040030050000910759800da80c48180e59100d0151404a0302101890011800d9031040e0000c0020804a4001001d54580c016181c1c03900d141e00c0c40c0c640504010745640000018045ca0880d410050443d1a07001d002d6080da9440490001e140c0c00d80005541c2c04011007445281c0240301d0810304a02c0c1b00d09003c04060b40349136010300303481d0303c404980d0781c64170414001d40c490b0420190101856100096010000c5d10340c0090000c0f0507101255801884160740034000911b6401c010b01c094148 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 708976699 1250 708975449 708975457
    0x20a060e2d150604090c030317060409020609130b030f0d1d01090506030a0e160501020d0c170a0210020d0203160c0f03030c020c040501170705090108031e04080303070504030204060e090c0402 84
    0xf40c0041210180c0d5926030b01c03114443d03001207001c1072041c1012703030b01c00e0004000079510040a030790400002245400140d000c0c02031003080d500c111481d411808007010f0303581000d5800003010b400c0303e43c907868948606407075030551016640080c9050009108a095202030a26a0401a143d10700d11904100a00003564802820825400d8503171040c60b002c410100b0008026840000a030120a03062000090138906243c0380c01c000c0120342960000855003421182c051080d031440ac25503150f000d10030a9062082d00108031403207510100e80900396480d2038004520405000c0011401e00c0700800003aa94108a01009000c4542000100340003d0181d80015091000e500403158114038448c002800d40718241c100b64503400323185814550b1500c041146401400c03044030040c02a6050940c40c0d9035038060751807202408000c0c1410255003000b0f14040350068030304101030301c0c0d0340e181c580340c05403040d03115120880c0114076021002490500c001d01c468080d03030446001d41001c0b40704104120103504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 708977949 1250 708976699 708976711
    0x90614090901171207110406081c030e1908040e06030d09050f0a0504020c070806010b0702060d051012060203150a08030d1109030d0206041209051f020a060e2d15 71
    0x1240d204002c3e000f030384480107002010320400135061b040c208441440169141a400300e1565031001410961036964052400071002c00c074600001d03e0f40300c92102c01c3c03070611070500d04050012040385180c14804c03208001e05c1541ca94103103806698a800c000d1560b1022410500c00000756050f8042c0b22070314004c0c407a51007075900140002030003501c5200040c12a0710000900c8210780c01000c08218402d014003030140103180303400901741001e00a40128032a48035030001600300302d68032400107442c0c03141081042c001c2e01c11110138a800c4001483d042c1d00a50081d10303054044103880410b940b0500d000c0140f1000d0341c4020340998140150a28130201074680101000740e0386d0400d00c6020003d03241082707002012551a0b0045c1000e060030305001c0c01882e040010780d010080c10748024001c40d240c00c2580843c100007841c50040f40d1500381d80c2281800a20280100550b041114403c402c50b4000303040643d000d080110001315031400b0000c600c40b0b00c080c020305030043c1c018040804210a42040c00c641c051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 708979199 1250 708977949 708977953
    0xd1a09040b0f09070b1603090501050301050604030609020a1505070c0e1311120d0e010e060f161406041a07032a020f030705060121051b030a0501090309061409090117 73
    0x103403541c017040c400e608103180c001311003074500e41c4070780905601c492402d00074502070074203514650401340460590722540c0009800b5a84850451085445010800740103040170200c011101460306001041c940c80510705031401c40c2201c0010440c00050113034540201d0202244c3c100302725881e5034000300041d2181c44a90303c6003039142170940c4050300f84000748100c03c03199170f103102d04403c01e03001401182101c0b0207c0c0c00b030b20050201c0c8095844e00d00444004003c0a200e484908242c2d1800240400c004001036202d400340200b4041007180d0464550701d850259003801c40a50f90f8418110103c981c981409205003605d01a000e403203030b0202184d4052804207105071003c00749012452450740e844600202e500d07034041001041072a42d40c0210101c00c1c003102d03443e148444400d4403116952221032002500c41461003440da0030780d80c0d04000320303a60554018000d20180d452400e0191800c90584241e401144001c0c1c00b003150b40564000b01d400d4070100803c1c1c0c1b1a01c0c0d00701201540d898158071503654280c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 708980449 1250 708979199 708979213
    0x1103010b0d05010507030c030b0607022b0b070f26060105041d01050406051e090703020d0e06040312022113080f070c0504020a050a1809020d1a09040b0f09 68
    0x194907294000d000c9107000790004070b40d50401d440d00804403082c08510030100f40c0f0b410000f00c90b598400003203481440c0c0440745074940c000c0c822800c0d0150400c16000055100030440e4440403c681c0d4000103100707185c00d8544e40c80d104921401610216615032021104102221468405c045001700303d0f42c00c01c07410f2500c1c5d0b00f4a616100c1d1403000e0040c840c070000c2c1110302c00004104903e03041c0941400344c0000c0e10b800d409001e81c8841d1000c0101c2041001d44a02c0d08880002c440038400c1d0706440340c468100d00180040302c01100d540e80c5820050b0b500350000b9071247c00c8125140e280340221501b8031020301403e05a041108229003400c24090000c0500180e401500404a030712a800317020150101e0030029a81c1d4081e01d0910300320203040d1710090050340103200400311942c021003500c61100c0c2c00d0802c41305880c2c40303141c40500a1081d4124080c040d10102c1d41110380711407948141702816944c0414442c5000070300410244081c102d40040900f441c40b03000440510507840c043c0d40006e00c800071600d00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 708981699 1250 708980449 708980471
    0x70f120311070503040302090c0a05030708060d021804050607030e03040306180501091a06030a08030105010305060d0c060e04060801020403021018080601060c0218060303041a0f0a1809020301050607110301 90
    0x703980c0c00500300707441c1c943c13000c2002c1c41503107801c0d04004d4000020b1580149000300020000c4c2640c00300401000c10b00000f003001555585800c514410420307402000006580b58070544025041410380d0103642612422002070051800307849010003104a4078000e508080c0f441c0d48840240109543d114084410f9046040c0018424050041414400e0520303004d40000b0480400e501034006243e64402e41c03041c91540045805841100e054440070b203404986a610580031401e860309042e0002d00c003049241c3c00013880c0d58810070304440080304642c02e115241d6645451403e0740124003000e5809211407130780a0007030340503224a00540396284030f4281c04513030f01c240c21803d0001c00d9022201203a02d03400305204500c0e2010021000c40c3c0742e450804a5424070102195070390040d4001c903a6603032418416105144052004d60741c070b401c420040b01e50784c0c00c80031400802a1800e081ca214040300701110210702c05070a402a02d05031400945100e08000460303e032400031045070341041d60955601d03612004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 708982949 1250 708981699 708981731
    0x6050d0c140f0105161b0f0303021203060904020907200c0112110a030902130921081b0a021e0f1504030206040303090c0b0d0b011107051305090c0a12020f06070f1203 73
    0x40100747d484018240240385040180c100342a610f03110a160b9002c000300130b01560740403907050304503030151410085030340c9550045c0c4240880c6460b462072041201151602c0c001e000a109a00c1007080e43e03041d50326080c60030001c05503a0040004c01c00c440040c42102c511074460307444684250b000820501000201d5003520003124a212003e9035103041103040c0324815180415060003854040c40e11076500e1411800034010580d00e080c00d01c17000b0030700203203103400d5030b1080042d0210360306203098400001d4100c1f03001d170766542d6400c09490a03900070740501c100209031188100c0c0c81240c143e0060001e5681e513580890052580100848004282e00408200d01c02c5003000740c1881001c00400056808040c0300152020358000b0003500a644610014080c0361582e000505a2100803e0007090589034602441c1c20300100340c20035030700003100120018066003403110042041e802902c0280340d0361807500c04c1c407216200308100a040d2000898800b0009948400124040c290074500000c000d104030b05804 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 708984199 1250 708982949 708983003
    0x912030c0605100f0e04060c090b090409060b04021317060906150102010f020301080a11190b090609041503060f060501050405011107081f0509060f06090a06050d0c140f010516 77
    0x68000c1740311410001002814403c185485185041000c07404d0310f40080024644281480c041c022500d5030307040c00030440c081c3c01541402c0c0d03006100395201c0040e240500e65502682c4140321805022000d004007080011504c18004c0302040c0c05802e00750765070f41c04074407001e45580c0c0c594115940c0d01400580100a031010314041c10b202d00c090401d03140d090070300c40c0c0c504094080c42441401d0048401c036400480c01c10110454145508040d280e25078200051058002c401c0c956400c41d090490b02d101844001c10403130180c03845210100725415071548400200d41990080e03c0c0418130400060207175602613505c0300000e40050088500554461035042d0a02c00381552071640301c452041002e26424590007550303440307482c1030010840c40c81c0c4250060b41c0b041c405401d941c0a4002c0c2400309100b200d1641210003d010064981040304400c0d1400400100552044040000300807404031520b20b040107000c041590140d55043c28241046007011039501070341d03000c40e0821181c000f542c51624501d2800c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 708985449 1250 708984199 708984209
    0xb0102120c032a120a020d11060a110906031503060901090b0c0c0f0d0201020a0f03110a050f0c0f0c100c050705040e010f0f020c0d170f06010c080c010902010912030c0605100f 77
    0x603e403140031724500680350106510f02d00c01030140a100c0c40d81c11050000b003003a4016400c00001c81c10301c00c0f5541c405084c0c800c01e208150800e1000040122802c800e4003052034949007036049030650758500d01c1d60303400c0300c3c408100100140344d6072001c141d641407000041d00140c80d8480c10380d105607445540300c51500140f00b0b8201c0160750003241c0001c0f6550091a20054040141414420980748445414962140c0c0c0c1c0f4040034005c01140b0703512410112003c1e184180c4100003294501c135100e030800c50352541140002c0f071103011201d0b40781074818454a14000c1059110004094641c05c010800c40502940c1c0c3d549240d640d42c0c1c04461604003000d0160300f076400411540140c1e5070400d000e006092500d54030070b44041c014004c10034003140700190940d40d4002041200034125480e9200105c1e15040034440c080d0542d600811100d081d810194004040300e0b100f62559064540d444001c5103100a1a900140200d60305455030008501d5540000c0d03440310043d46200344068551859141620980e001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 708986699 1250 708985449 708985483
    0x3130b1204111512060a0504060608160302070515150d030203070f021f0e12062703070f03030209040b0906060d020c0a0b04050a030e060906040b070203011e0b0102120c032a 76
    0xc5c40780c0c0c1d003040400440540001e0f07500b0b00c51075040c490041d0004d00c01403e1140c0114039140c00c00c0702544070b036051310840d9511800380d449440401d101795001380c2090701c050710541030b560800311051522103c2e00760b101d07505401650420055844050400d8a05070003039820101004140c80d801170350b400e0400190700182c131030180000042c070610820744002041c409031680075a0a100c5991148800b01d852054400515494888040140760941c05440c0d0002c09400c640ca61278020181c042c0c001e013021880580e001c00090000004210b00c00d0030984500da04050200009009452550000c00b1500c0103081150950000d07075403041a0700ca01150161003d4000d110300e6030825502140c2184500b800725030300b90a200324200041c00c03d1040c1e120705031380341390002040c10441d00c00b07410001202d4000b025041d101d000c9020036401410000c04013038014051007084d0f00754500341000b502c42c03041c82d20005505101d0540100d0000c038644086542a1000300110111140401c00c9410485032a03040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 708987949 1250 708986699 708986701
    0x5060d0615031a091e0a0c0b191404140d14010506031005010305120c0c04050106020f0f01140a020703050705010c0201060f060203280908010e03130b1204111512 71
    0x42a03803c3c4414009007014000e071040c203000c044000014030f99682e001c5a00342c0b205440b00c0311150b030701d4154801c000400219009000007100a150720240c10982240703c80c400c41d15880300d81c100d0704900150441104024144802d0041b0390664104c00c1c90032002409150000742a40c13580030307605c1422184031000c0e07034541b000c01034242801c0c89407401e5036042410038415541103980d02619140d000205014a030300208010034149000c0010340c021100c0648100306650315414001d40780d102c0307014000c500d44143c21004018440c1449501180c5c1c12551040501d600c1da10100740103984580c900b43c0800c842489014003080d000c5c8101e01480c0d90540001543c580f603e164224a4071a6500403420754000384010100d007800600e4407480144440304600c58a125003106a0f80012640c110840c03035803820281c1011584000000d06c40d000780740714403404840c2c0c1c84c00a5070003442000408580550703402c001c5000224140030380d2a0050b8014240ca0060113800c080f20745c140c004004660800203800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 708989199 1250 708987949 708987953
    0x70503030414191d040201030204050d030807031a0d0f0602120c071e080306010e0406080a0813090203010609141828020a1b1b080708070501031b0305060d061503 71
    0x103c02c0705400500c1100c061194900303010501010028100744071801c000c3c0d0009011a8466412100901001045c078007040640b81001000c0c0602101e40002192509a40c2c04c82e10303040d03100c50b00c250400104502100c1049035681d401880101d201210020707024084100040b01030702200e44151100d0380c9003515400ca60405904558452042e4000084a250050f0100c0c0c4030804170380d032102007820710002140022000c9002004254403804c898000c1b0a642003c205503031004102000710500a4805541c4a48030201248400e02c5240e010600141c402c2005110a2106894012009240480080c0040c00104405400b11064850894444d08c40c0c10003039404120406080040d000c00c5041080a950150100d100c8100d102094501180310100704032040c0002d4090750032040300812080e58841d07040e0313920401030146203c03a010310500401c031035100744a0300c00c09070f948441c400c0c00003000e1a403d8008080282201c8d8202c2490f000c41ca000c507007540203444c80200c80d40c14203c2c00a00d54 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 708990449 1250 708989199 708989209
    0x6050f070816030e04051e060a0305070b12090f1906140a0e06090c0a090e0a0807030306080f0f1e0f07080c0103061d0f06060c0d03050f18060117070503030414 70
    0x504104da102d1850708007840341c840a400b0050210245c1540e404482ea143c040008080d80340641c0010b1661180e250003007501100c101c05048050601c4c0c0d201d241d40c0e101c0040443c0c8a07072032204400901c0e40841c624001480c400c881c3d41e01c80f0350142e100011f02501507002d1603a50001100c03900300c0703151120390baa00c200310100103040e4080f000c240074050944090000621001481c82000c40741c51301c41d02d10903521a070501c0071004282d84032040c6642c03111940f5001d07000c1c2c01c0130301c034039142c1d0b01845440068140e00400c10032060310301c40380a404202c0146404809801c0c082462880310300c20060240c0000e0800c21524001d0000e00008100d0384284000040503244aa000f444d0011701e1622580303154a910029941c10001e200d00000e06a074440c00428003e02400c916100e841c4a680004100d0603059440303640a517074034107038074122991882030341c03d0000d010301070003162644500010800000140340e80780a55903514256041c0b983d58a002034074640080c0c00c05030840319501c80e0440c1e20304d41 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 708991699 1250 708990449 708990467
    0x810121b0b12010b0c0f0a0b0907050a06021c0908060f0f06040b0105090603130f080c070e09030a08060f042c160306090204060b030901050402101806050f07081603 72
    0x118006070746403140c1482811100101032044000b10400403904590b5031500748140c0d86060306000880e0031084c00342c148840000c00640c5c80481c83c0c042d03441c0120711420803c20a5042d64465001005201083c0c890084945c90004080c010050783c401c0c0420441000d112150140000e4203001c202400e02c1c0101448522002e000e43e40310f146480902d0030503907001026941e100000721065526956140c00600d6002c041c184004d20103605049402c0c200131a9101900024151004580c81991500c4180085200944100207a68000c0c403020b05100d1140e00b62036803006000d4603d0000e2111440858240e5160800e4140c80100000344110035140d8110020344089100d4000c008070f881841c4145030010582c007002e1300c2070313031500011002e40d12541c0100c4010410f084050740d0300d00e05186410b008040544049201c1d105884c0b00000140c0300e0302c0c0c00c1204900c0d0801080324145050302c04d480b15844210440703e505400d11440d00401e0441001e011400c160910614101c0c1d42803400800200c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 708992805 1106 708991699 708991709
    0x141302031b030c13050f0a03060b13050a020c010e03040e071101020f070b012c070507030e19030210030608060112080903010e1e0a080a0810121b 64
    0x110f40c0c010049081c0390010701c0d58054841c0100640303407041d1071307040c3d9001c110b5660610104045501414a0718002040c0c0d0602c01d4075860107074240e1341d084868000c129404548141c01c06c01c00e0044a41001460000d1864142040c01c12024184013400260400c1051240e140d000c02c000d50490301801d0902c400395480c0e20403441d000540f100c0034064454200d030001c4400080c1004505144d01c0c10402d680090295580d6000454031900081070a60410020300c0300340c81c0c16103e001c01004003203011180c030030090f0309500500030340003c1500c1103010035141c9641040020404200070741036403603c028208803140d040c20710001ca40031b01806142d00d5468100c094880407400a803410b011400e41c4109803202d51026132480c0c482d80362480190482c8020000303962081e2003191000d03401189902850301c0c071500c030b101c1041010f4210500b16080480c0c00d050032151084490400c000342 = true := by decide +kernel

theorem cover : BRFrame.Cov 708812949 708992805 := by
  have h0 := BRFrame.cov_init 708812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 708812949 ≤ n) (h2 : n < 708992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
