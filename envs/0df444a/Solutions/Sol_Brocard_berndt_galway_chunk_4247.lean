-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4247
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:00:07.362124+00:00
-- url     : https://prove2.me/submissions/cccb1508-ccfe-46d8-8695-1ad7a21ee2e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 763669064 ≤ n < 763848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 763670314 1250 763669064 763669073
    0xc0f04020c120c070315020c03072316091b0210020d0f050c04180612030503060d0510020918060a171221011d0408130f0b0c060907030b1f03 62
    0x1030010f6860100034000c000e1642c20800350300c5c02c0b08192802628010401240c03820408011a111241d1001c0d0b1040d02a0b038442002c0404520351140712514420080201110745172030407610b04070740c1000001e2102448a1900d24000032680202d90b0241e03220000000ea2002660042d003031500b81181c00040c0360030210400d4041d41e00648049440d106c001600780011402581440615500b401d014042c5514001480c1c4922100341005420090048003284440c0d690061180f10366400c0400c40d100c103e24054060004c1d031285001c18820b2440e814508514422006024481c680042c4807400f0740f440c2c0358040180840e2100000c3d6903008200030000308544880140c0505020000c9a0366001e030504401d010002e0113810007100354090020845903203103480400e591141d480a682c075284c00941003060030001482e0080d8124024a81005c038401160034007030080c0d00301090850310340d03440b601d5916031280d1071400090400a400d80024090007030200b501d9501544071600314083c6a070f41d031035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 763671564 1250 763670314 763670317
    0x207020409080c0111030115030b01140a030c0801060906210209191802090d1202071a12151c03050405041e1b0c0308040203010b06040303020f010e0c0f04020c12 71
    0x282290010b50100310036440c41024401c10700b0300303171454482d94510350424001b07041c42d80600c182801010345440c0c080f021a4412100005075031082d19071142c45016004016015004030f00c100c0380011090b100006400b8418180401141d4107611a20b0031403051950060400050b4060b103032055800f0040c02c2d1681d01c0d013a81d2030f0241d00c418820314000a06080a0420314010038211202040c0103011891087d42d91180c0c00c0012a400184621030144040050781440103c1d804240720140c1c101e134070060444040c008024070305140c107403403207503030390354410030b0310350304207400e505030410f002d00d14401d50440b070b00600311407844c0a4100756050a90f1480010143c85010350502d080300f1a0100c0b141d004200c074008c0198460201d4054400048600d50003080c106001c2c3c405000c0181020118055440030340c8032620400014104a58030b5442c1c4c1006561000c410302405c030f8035841e0002080100740080340c4000d50f403c0c02031150065807811020040030b50031045100740d0b20300070940301001a03110b140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 763672814 1250 763671564 763671581
    0x9030604080301091b092d0b07020f030102070302060f0c0705030a030b031006140409061103090d0917030a120e0106180608072103090306111213050a060506030102070204 75
    0x140402d03075941c100803152080e42c504030b221895000300c048003a80c0441d00014400141e60308803031004410207000d201822080600d14034002e01400c07010001c0384841504009001741d600948100e440d803041401032608034400c2e11000780c010703000b960103d40303418200400c45401c54022600c490414409445190540d4072040d40c90b4042039a8400d5020181801d10402c01d010721400801c00c80d540c0f411a4008001401c0d0940310301c03ca980c0c0a80703104010080c0c2c0704108a95410880c5a00c3c0e00d0b00e882c00e0395488000c00c0700d410100c1d01c080000a06100305410f1341a1185000f000b5509040f01000c0039100e2002180c07002140c10344030811400c4c3d069003445604001c01400180b80c40c0c80c40b06035545421245550041c01c1e2a03000000184501015a0300c0d880702c1d110703840500b5400350381500701111800c0d1541c03c001e02ca13604250704524412544006804040039040c2c44850320388600c4040b00c001404214010416000f400202000c00c0f1503038000b5510000140004d0725105003a1b00040071a210b44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 763674064 1250 763672814 763672823
    0x807050c01290303180f0103020409020408010c14040f0b03070e120a0b071b111503010303080a06060905010c3203040806070906091e03020d061e05131709030604 71
    0x30b102ea0420042050712002c0040d00076500c0c0a250240007100804210443c600401003010440690f900ca81e044400030550048110345441d02c0700b00c4513029101c1400c030740e0002409100040180340b103980c200d600303d031841d0282d101c101d4a4020f264815402c020111828080310324103031021a15000300150064030f1001c0070b02081d41680c50032200300e440c0a4040010070600d10032240c54044260300743d40140d50000b940e60381c80d042c03050005950040c904400c40c400c0d000400004200340d006a0568040e4031a40d40903c00c0c1c079100e01044840450500c680c41c005420907044002184030056101c0d000111b8038083d125450000392000c0344000400d0062545600000b800c015641d01440340d02c0d0080c141d0700d8155055031030711a004010352124021010b09102000c104548140c5462102c0000c50380034054480070400e07410500003d04c0e0b400340748040091128041800b0400d944295849000550b0010b80e91000540b121402011104240b00980c10208030000880c3d4003000343c1842203100c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 763675314 1250 763674064 763674101
    0x1502130602061e01050a12230d020c06120703050a15060f0905040605061209190f1104050c040b0711040203040b10060806011d041b09091401030c060807050c01 70
    0xc0f81124041c0e401802103010540c900001840f03544d892011440c00c40700e40400310121840141040075001d0040d4140624034000d0a003411202880803030803609559168007a00c0b5080071140910102d03200e151000546481d00a001808d107034000e90145030820030340324000800000d1007106e03c100c00e5040e0031050119042c1401c216440f54402c0e050f81c080c1005903400d210302854100030942901520301201c10503219280081c002410800100d400c41c80d83d0004c1ea001041ca03070070035094924401030240ca1050550200c0da8103820a8060540a01241c8445c9440e06d0f140100b0103200e0782110008030b640ca900d4449030340d5240d0341d0b8000ba44c083d1303004030402141803d0050a03a4540d60856125405000b1080108596030780c10030f0304000c000ca00e0110781d1429211030800680100903003c6074500e4219640d810710610f941c00754000c801c3e0360300104200051038103901101641602407000500010522400b4071603107214a0311580c111410741407490078110342004890949114411403c105500f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 763676564 1250 763675314 763675321
    0xf03020d2003100909122d050a0818070521100203090c121002130315050907080721030512010e060102061e070305151504050f01051303150213060206 66
    0x500420f601c0c010680031104006010a560300d6091510004001c90148400c0044540e40040c802103c900300c2c107030a00f10300c9800405c4040c082c1a5420204038100005e14080004803150900000f0084c03c00143e4001d140c164980300801180706080002158011060704035034007954000c00800341c00b1a002e6901680701d152501d10149040704143c0c88030b00c0303074141c080340d01d032500310105481128807118000581d0780d26800ea0310207101915644004c258034166101c4031481c601a42c4228002c0c00300c1c5007500c00c16541c130300040d60346091602611040c45086600e07021107045031608100343c18460f05120781040049420150a84002d0b809104030034442c60403c0802e680c140246030307019400480940c0c100440c8446080c90503c020103182c1495610b81c082240300044503852400710500400b000c086805d000510403039900523110703040c0152038849100541e5805a0142c54002e064614040c80311891510b80420310a054440b44580c0c40e0300300511080c0d0f0b4044200748000d007078030350000d2a2030700703 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 763677814 1250 763676564 763676581
    0x6040f060c0204150f18140c0d060f0f061110060f060e060a1205101e0509060d050a171c0219031e020c0f030705010b010206010906060f03020d2003 65
    0x4400c00704c40200c18104802c20310040c81e1a9503101c050300c0e8505084000681c2180f2454010014500d4a412000003c420008010066002042c440b850b075002409919515110203204100307600480640c046030410501055215420507c1144004800c40e0460700c0b442d410b41003101ea02e13170400880d00d0b1140c0750130320013150483c404e01e106000c00d688251900c40707000d00c002e000b01d8014441000090315035010804011030824030b8000703000c01e55584c14658014000300111281503204181c01040000c00103026468081c04001160713070810301400034295070350340b00080000c00d01301e0340702102002e002c2c010800180b140507845c0410031520040c0d0782c80c0c24080f0821401c24080502d01018100503903c010304101000c06500c9000174080582c0740e02c03034404c0c0b1909014152106032000c3c840440e039001409415048074801e040c0a809441d512398840683c0402d1311030700e01541d80415118000070400c58400d0740109952010348100080c0c0e604411b4103400305844001104c00d540300040300b8482e416 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 763679064 1250 763677814 763677821
    0x4120803040210110c040b0d020a0611010e0c10030b0117070305180f0c06160609150606081e100e180f19020f0a0e10061701210206040f060c0204 64
    0x81d4010304041001d8113040d003610360b50f49038a5003043c1c011511000e4500e500e483e6508100b401030b9000700300d0614141c072103000802890341022820015070820414811641d4007140c0740d90384843c0544160640742580740f0a0b0003074441e081000d810895048101d02e0741c03030b020b1004c8034003a42003580c020901781450b802032603406610cc6041170315a042403026000720040041e0100440d0002c1c0d07002c54484c56955400078901441120240489003482c541c1e408101d1030038151440f42260050400c22685c440c0011074040c14100c1c3c500700b14081d11011754082d084030400c9503070322900042180980684540c84002c03422005e44146802e54210080d110208409212015095110304000e1050040084c00154083ca22050103800707817041107400c80d0180c0302c55181c10054031130050586514140400e0404d145501031103401c0005001c08519408027140c40803440c1240c1c440448252640c2940c0716040f45d1150003c07040360b0042c01080b00183c845c055400718001060f10740c582d00008c01c031500500098 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 763680314 1250 763679064 763679089
    0x50a320c010207032003071403040b04090b040627050402030c180708011a07031809020a0507030807030b0a0b03130203060106030b01110609070e040515150414010503060a020f041208030402 83
    0x445e20500f981c07a44400300003040e1350000d6000200c041403013510b4081e160641c031980c0c200300c00d070250005000c00c2040381030f08074583c100b8040c0d50411141c1e076101c3c010720742c0c40d200c030700f00441150242006001504050700300b01d80041c002019181e8058174800099005c041186214903810044010440310303a0304074404d14010020034038059503c1c40403000a8045107c4c0580003030074810a103054001811171600e03080050206c10b0011580c604540350701401030b030801d51080b00003c1d658400205182d10038090400117440182074110180d0800e540d450382608010003044098658039201005a601001200e00808207500e0000d50030b10540c000504070408941c000206620201c18040e1400f8002b602d4412034107020801640354440740b4015052031410102ea482201c2c0c1b01080c4072005001c484a04540d400841c0c040180c03c15009845035175403401d00c1140e40c542c01641c0007403a0080250000e085800b0711144003443c3c25100c40220403184c805d00d60075143d03580c012042204504094400b240c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 763681564 1250 763680314 763680347
    0xb0603240d02010e04270f0b01060912080d180c050f031614060f040e06040c170f06010c02031006141c02010c2d030f050a320c01020703 60
    0x2292220350b0000b03042401030f6649140220b0360342008181d00e0240040800d0301c10f009641c00500c0000b2805d0844114401c020305a4580d0620000000c2860060360030b10101c0f04e41c070001e44c50500650300c40b42090340281143c00c005075110360300c1020041b40c0181c05c030311b09840707a100b080300c090401040c88400e40b08215014040d9002907540b80d03960110020703100c1103c695031548424000803002140c003074000c008584001182c045004510034404200300b610400080e1010809a50105070482d84841c1c4c400404502c59801c002251161089504459002c8018100854540a15400f01c0c0c9809201c007a141e003515540c1030309001c01407101c8001040c00108030f84070a80c800103180d030202c0000184c00002c0c140b04580443e2000c01442000f82e042d681c101c40c05c022000610420448a090390b8400704900146000308141000c0ccd0003141176562202c0700d0342c1e0308184829091100d003800d1926002440c1300d0450700d0384084c035040b1440c0041c0700c5103e1250001d600c0b000e252a001d440102410074164 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 763682814 1250 763681564 763681579
    0x509040e0708240a020a2705180129090616051219030507140a260c04230904031706060406080408090d2015090105030412030b060324 59
    0x2c41d041498040c60304104001001a0341c1c481c0700f1007c2d245010f01603d881d04014503840300005050352134080c3d10844a040d41d840502d080f4080408002c8242409844070510501d034890713051003010b8080206070681c40c0d016600c1c1103142800140070381c02131005c4500d40c4000001000420006014500290b00a0b1804504005401903880d64040c408404003081650701c100040500c0d00c60000e0740c9144030700300f80382ca940d002710101c010700c1030283d40b000d402c180c40c0c2c0342e169000d20403610031100d01ca024180714281c1802e041c201c0042c9007002c1d03401410000310271030980185558802c034480e030060344292242510000415200c0303503010790040c645807151000748820080c6540120304258059404008036640e0350504001560601d48000082c03d03460040e4003114003006100c210743c400190032210304151043e00c080e4841d591041090311800503a0a00c00705002400c0b44220403081142424003040c400318100c0810a1900101d0703004489440c02c07400807014804d190011021100160b4841 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 763684064 1250 763682814 763682863
    0x2403050c120d12020706180b070f0504091a03120309070611030403030302030c121618050f0d05240709080105061813050303042d1203020a0509040e0708 67
    0x41d52030b00d240300500c00c284400d9020308514504958126003031a41d100b20108080c030303100c40c84c00d00308035070320350b0221107907007011000c034031762034014216080e91502aa607001d00d0141405e00032005801f000d1041c07140d5801c11514503240781e4061220308105404180c0054492a041603102d2034080c00346e001c91300b0702c00d0a12a10f01101030100868013626018200035030381e0f440d03005c2d4012003486191b0400b08104039440601c0b903404e904240d607083d8075216959030b418141d91014108010030282c030400740d0100c500e0200c0d0030303a81401008560b0700740c001ca0640e030514012b80441c020340704103c401610f000c40010b040200c83c40e0082c3c03100c0d020b803d59038001c0065141a03808100c121403088900140030807001d0005000003013009080c90705540c131405503034490500303183c864840c416203101040340311411884111070501c8540078101e9070f03822072038030100c4501518041e8001e5000c07820351810050200004e054a4843d4080c4594051080c0000d04000b460840b00c07130304003002039032600090303619036809 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 763685314 1250 763684064 763684099
    0x111207030b01110703080a0c05010c03050702060c040f0e090c03060709031b03120309052103010f0e1014060412080d050a020c0705150c1203190b13020705012403050c 73
    0x280c003500d41c001c08541d0f47d1613035110140ca403840c84500040c00342d8201842020340c946d0542005004a5458080710041d450350a4440b03404d008074011041c89103c554030070401d064440000c140c00c81c4220b410354048803100400300e07041070012900c0401003406244100100a000c0c0142c1248030301d500141c1807140d045a40300900e40100000c0301d010140c07680584d10074003c080c01042100c02403604140580520350707404120342d800c240f0039071000010120001500d1101400d115210303e08201c1c103030b03840e9402d200e03a41510070a042e81054014606004c04900582115400f421190003000340540380d090072a205000c0d00d0005060f0100d05006000520600c0b0b000148482620070403a14540c1c2c040d220542d0450310f004492220b181b1348244607420103042601002107018980c1005003c010503000f0460505842440d0101500941590380c01f034480800c41d40079142644c800c8001080707048000300c52100c00e034030340d000f11315100138845010400c100d010003c1c7c0754280300c02d407501070b01c01054804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 763686564 1250 763685314 763685323
    0x7020604171c02010c1e0215010602150c090612070302040305100b0906042703030e060106200a0f020d050a0f05100e060609010905070212161a0f19111207030b0111 72
    0x101c001401046c080004140303802032000c1c000d011209a52600d131036a58040081d5a4402c20b400d803801c012560010070408014041120f03001c80000d001185420340007200621940c0008001a0416509100120006600744807034841c0e20720140001c01c002c00300b002007100710080500180c0c4510b1902d540305851100d503d6060000c24071241f9180c421a200d0f00701640601040201c0000d507016490020030703840d070010b43d0305030584408016000120210380c0c22954442a055000e0300d00c400030004580145020702c2c488030418824030907a00f05080c9603070b460401d9200c1075800c0300c1c030b5002414075202e0713610079100310080c0145a8004190b03a081c5800032548049041c0191403049031140001080e00e402000041e80c6c008560f0b549030750300c02c486555148045e0004000302d414484111041c008003c0c0c500800b03008010802450700c00340c6403603500840034449819480c8506403030300c0d003803080000d2000240c580c000204414802502e402e1200504640d034503c90a81130150f01150b8103840c880014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 763687814 1250 763686564 763686587
    0x1030516080a0f020301081c0903030203030c0310090c020c090a09020901030b1e010305100609050c1b0c0618090106030501080a0809010915030c1e1407020604171c02010c 75
    0x412104035200c440d05074014003403c00c1804025400000001084100082c8060241d14400c4078100c00c4611600200e5280565110140042e031040c400301d45135002c00401103401c0049403800501040c0d81c0c0c0d04900a54110b080003901607000380074464132604110340504d9021035220010002d40d2030960000300522410b02002d0102c1107801d0001d241d45009102031600000d0190400e001c540c1d407407400b0390703646e20b0104108002d00c0c03c00b038002807040203a024881c0101030399104541041a440b044801003080340e20055030522820040a0305038a449000b05020404180700c089210100c03414030090300c4041c1d10074010140340ca401001002c402203410310780c982e0301018541d9140e040c0c03001280c00c1031240d0803441440d044078801240507501030744400d0f40145582c4405004807006201009200030031000c100200d4444003008144044070710040c02c00620080c902810a81c4805a00c2103035841013060801c0781e030202400c200312030401404100c0205007880280240c449052000744080c4654 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 763689064 1250 763687814 763687817
    0x81b010605010f0e06070819020f06060a171507052d430203061f0605070320030c07080606010c060e01020c1605360903300601030516 59
    0x3911404d400d60f07a60001c4a8215030000034654a44502c0b02c00c4464010b025080c0c40d01620888403004150794020542070320403c00141581d0b10a80f80c90203e880818074407550807494010044020725403041007030340302d00070f101c0c1d6540c0c1500c0b070404401150f02084181c01001e011301c0794034004c1c42280070150498204000719018034042600c4601c218040c075106030f020440150941880c086079285a54413803400d035008504454007034540203026408805121070050124800032810b008890041c401414900e00c07030315000401c1e0003d0105014141f00312200b840c1990800250000b0050341002000040c3c40d15002a18090070b0180019108400c617131802400152141007100d0401000e60503034a0100440003611210202500c0010f800051409280d1090030031302512250180e20701c00c4180c3c3c1c81d00100790110101b5902e0416024880010111061071100700002004480d55500c60141908440d031a450700d08040c00d00c1018040000b0700c2e003810075181904100c45001c0c403905d40001001c1e04d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 763690314 1250 763689064 763689077
    0x210606032a041808071220060a0507020c09131703280605030105130606060504060203030a020903120a0302031506070519080d090c0510030e0604140712081b010605010f 74
    0x201e0a81c903e090000c0c103009000e6800c00300d4182d041c801c105070514080c0c3c800750354400741003022210700200e4403401a540c00282e8000c20003e10700320f17100d03403206800080ca401110204000040040c0304d1840403580441c080060f09607010070405039258100501800f6505c650542ca00012480d00006d008040881d0041d6030343c4568244c0401540400d003d0080035000703000c1840c01c1c014003c4030310343c100001c440301454001e000443e1131080c8180c4041e144164051881c54803078560301000ba4001905807541030154060400321591410010104002d41e03490158503441c0c03546003941180701d040c40341406040100039050001e8804522801208103801d980107898203030f0304040b03555009402c001e03800c182c40c1c40440814404901121800c845c0100c0703040c0c020440b40c1c0c0c1c0440071f440502c410310302540e00017004100024003251742400700005030011640c0c0c440c0e076070301ea050781081c10341c0003928003c100140c04d15120140c100e0b00e0481c903903030400a0140701e25007400202808192910f44080000703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 763691564 1250 763690314 763690331
    0x260301061d060d05091b04061412030d0203040b041101020a0206041e080601060302090a0f0506070f030309020618100906050a231216080903031302210606032a04 71
    0x2551002d64622010b1440200880e240441c5c0681c0d40c2c030b120440c41c404000b40800d00d10383d2460f00d800780006580300b041e03241c8800390504c0d0500c00ca00a54a0b20142140424480c0d00c50941451000d14801c1d4040c003001c036000c0c10141051007441030000091811500410481c40160b182e5000300c1e812105942c4001d400d80031440700700c0c0b02041d41d50b000a4450b0140000004680340d0640103880000e00480d411100f260b81c42281c9542c0701054451250040c1c0280b040303c0c04110440e8070420143d01904000c110800154005085513006102040a03030040b2406030125050040070700d813403c0103a00b080300c1a5418000041c1041c001d600d01c82081000b0b68000010080d004060080c03850400201d468850703608140c04183c0741d00840e103204242c03240d04400c1000368840c520481c0102c030250f0284d850b5459030141c40e485601141016604140d01244049204505110a80d0741000000c080c08039400d10204050502c1000c0c21010402c281d13101d420050301207450000c1c040401c0880300000d0342038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 763692814 1250 763691564 763691569
    0x60303070615051207050907230403060626060609070c0f080c010c091503110f0c0a0302010b01050c060a230103111507030c02040c0912260301061d 65
    0x204549006100c0740c1403040b81221a6107140c9407405640d0100c4920f40401418130101c2c0d40e03004184201395112055101056003140510301003154080c41444240c013000132003484a10301d80c0940d00c1240e0b100d640d40e00401c0030900107500204e0b00e298070300801c0f120b0203900c0c481654580e4050903191051510364003280a01d4000c0d01015000c03540705c032203500246698100300905800407101505c081d4244916050401d21400f42882910084c820b140740c2031045840860007007040303101e20032100d24108489103010310710038050a154121007008124014907441d0003420350f001a50040e0601c130040c448400240340c0490034691011103048009800008405941081003500750400c0c001c07101c06c0008814064921320800442c903003a0ba40e9a80c49020b5034026917035103d0b0400141c00941612500301c0145060740250b4480c400034500b1011080c0c40c3c240344c117100c03140000100d800307060111201c1240c003103e040354a07280048102641c1998900040a880c002010400c00e02221900d02c0072400755 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 763694064 1250 763692814 763692817
    0x28090e0f10260105010e07020a20060415090f052b0215030717010608040803100f0b0a0314040c2904060314090d0f121e052418060303 59
    0x1480810305a503060007200c101c0410301041a10080915400c04c0000310b109410702c44024020b4106074000c10a814560b140d0f52240890781c1c009902c094800d02c60300b5201d076541005040680260554142e0350000044040d24000c5103a2010202008c0d11030b00304240c1d611504810308001d14101c125901c03507860300c200300606414041c001d503c10402c061034000b103004400654031800c1c25464070080300700503507071020220200f44550400601804001740c0029800805160403988e440b4124209545900107190112003c1d00070703980f40c82010800c181e869505000d550340786140040d4071003185c2400c1d210001c6580c102e0140340340d4000300c034107102e000e04d00c0f02d40d00e5103500d034109100c0c60f1a280c9500009001d048075000301103104000c03d006c2020140d002c0303143c6034042c005407607041210400d6030f416507080384025030281c00d481d41e40092600c0400702c03901e0104c00103180c0e00001210302d070420f0050a154030080400c8100144003c0070450740c0c4411032905004c410307520101d03081d07540d82c80000740b45 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 763695314 1250 763694064 763694069
    0x39060b0607030801150504030809010c110901030803070201180203030412150e03030f01211101051b07060219080313020f030109030e041805120a020102070828090e0f10 74
    0x8032000400c50300303050b44507101d24166001103012a11403840e44ea41181c15000b24040945900300c10007030a862580125022489140304800009401c11120006803402c10240d00a9528400c0001081000c950a00c244000120040149802d06401d60042952030041c3d020760884120248442c60a0104a00c1d0410005c020b0000074000108a64aa10340300c0c0c000b0f0b1242c00c2c41040700070000c5950701101d100600400e0050183c1d6007041a80c1c0c5514a594011010b07a07814800c0800030382030402da4110903641c1c4255450010010302d8a0729800a142c0794250030445842141213111000103449030b0100c2e5003000c1c2c3d010110304206070a0001039030011601c00b074076a0640c80d00c0340940800d40c003d103900303184840843d020001401c60700748042040c522480d0040c0366030401141e442100c1c1242c0060640e2301c01d144001030400c40c9507a01c0c1c0a055000f0118601e403141c444000c62140c00890749294500300443c0f8204448500d084201c2d61000d001800e40c80c00d00c50041e00003504400b021904900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 763696564 1250 763695314 763695319
    0x91002030f0703030c1202030606070609020a0504150305060705030106081501140c0a031413051215010e090f0307080d0209151303020a141c1a1639060b 67
    0x9030b465551030098010700280c029040131581e220025040d507049407007928802d2102401c883d05d442d80683d2218020006054100d07444900503030302240c151500e100390340790002c1d58121001c2c41030840c104240303040002020001004420030050114540c8000402c1e00a41402a00202102188010385030b04007815002210781c000030511448098000070107095160198461555100101c0c0f88255103120b400c1024052003200d0004000600f80464009680b41080f002d030b0340d00e0481040911602c440a9110031f864042c04818003002da001440068003052910005500d40025650341001500401c818a0301c10b0394080381c0c3c644141c84840d02c3c040c0500304103000d44e5442c41c6a800c0400d1003640c5000503801110758000c0458040d00240c2640e0605034010100c24015540b500141d05001da4107101b20380c0d498841c00c680118501c10941680a90b038010181d50640c080d100c001820100d81400722003505100482544d40ca00d0100646522122601f0011800c01c0050408401501c4030458554 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 763697814 1250 763696564 763696567
    0x310030510051602070803041403010603150504020108010b0313240501240203040b0904050c0c07060504051002014d03010f062c0a030203030a080f1605091002030f 72
    0x400310748035500c407510a1074400203a02c102d0109200c12656202c240c00380301540d80c801c00061029801045080c0b251510040000c502651640c0c0c486207000c1c190b410441c1070a86517001e110441d1b80002445025040240c2c0315411854411401505080301840141400c0c00420118035080d101090706401c2d02d0011788180314030359464003840c00500101203a0a00c6800400001008510100442c0c00700c580b41d04155041c403d5417810800101000b40c102c401001042007090b103000c0041c0004401422940c603807640b2140790030107103c0d03c0e0001c05112400c592500c101d010301106c0c1030304a43c0c0b00c0c40c410324104d2001c0d0400f1840c601010015200c400c0707140610035858020302d01210081d4103031140d00d85400d4900d50341d40415203034002e5118200c0c40c4448840410111240315062844174813600500c2001c020b90b07690003090a40e44034104280c00180076104005124600c0c0d00c000d6007145207903d00c0d600d030a4040d00c0052403070150b215480d2080f40790b00c1518070910b20800a80b0900419102c896 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 763699064 1250 763697814 763697833
    0x50604030f11030906030a02031f150306332a0516031205070f02040c08040b06060c03070201270e19200a031e0e15090307030503100305 60
    0x500024404003101e000116a03118922581c0d4000c07095400080020b000981580c603007003142d9000e90002442c6814202c101342c1125040c0682000c482c3c020210748010321150007602030300900ba40e5840e000102d414954000740001100c170141c12101e084044680c452007000d59071421541600e621034400e00391642d00003243c048001004e05c40a40d10f02c204111110308101950261060019120190500328083c01d60280540640c004154441c4100c40210040c0d4030750740000c0444610300c1041000a550f401040b00b0801c4020380039811450480c0c0e41030500b00614034003590b030712404d1802810001082060010111080054901021600100803100d43c0714560030b01c0c132180031034010041402240d01c6402611007841030100454801e400405181a0322000d41e40f2680109904410155540d0010a071001380751140d107110060031401203001540d1082c003a141100300154610925007020611947c100e000080355801640350400e19126920b9903c0b07031550400c81d40c0064403d000e2840c02c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 763700314 1250 763699064 763699067
    0x30b131d01061e030b04031202030f16182d0801140c040f12020607050d0f0e010206060901140a03080a0c03030608010c0903200415060816080604051305060403 70
    0xc40405103a60000c0042564840c002c0c400e42e580e00d0803081c681c40388468140041404070300c0380d61740700b4042c2c1080065403036910320000403a03100701c513085070750845c800a20084541c00c441d050b08101d2540381403146501c0e40d942040c1146414491251040d0080303604e1005000003403905980f020300e03540c18170a135544d0790f00424081d102c038101425108940c980040c0b064210681514151801402424140c03802c040c1400d403004241d0030180c0c1c3c0540148171080c0019400c0280446000d6030703030303110b0402040c0d100002d48034142c030100c0541550081410050240c9803000480d045821102c282094100d00c100401c24209403504098440040019081000b5400082d0448980d01c2a41e081008030340c0d881c0c1043c202c03840840c02c41c00086a081c010004150746500000c40d982c01800c54103425583c90300007070221035085410700b120303960042c01048000d41001e400c540c071011110001e5151200e035a8000c1112100412540c0304550740c01c0401e41a1580e088242d18240d8810119a07103420b06040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 763701564 1250 763700314 763700351
    0xc0109020616060b0904050604020906060705010c180b07110d02010c33330f030f02030f0303010503030f16080703050c010b040b030a030e0f06040b030709080a030c03030b13 76
    0x2000d4a0a44c1802002920350600071141441150840c001d442d103a100c6501304082640c002d490207500031018042907000c12408e2140202000480d110008016a1800c0307210380083e0307a90040d0755983c030030b002c00c00100d04400d0380304940030310440320100c64085900c0103031009482c0c0c0d180500483c0b0600d050007800e00f1062003840303040e0300c2c0c114100e03000700f1a904072209489511440307010102030002e07003102d0385040b40d00245040000e0746503500060381700c1550301140c8885510541e036051030f0080500960409020546082d5003030f41c0690302d15810b10020940e030f4421104a82c842c1b0100081c000143c05450f85010151640010440c5d611089424024840d402a0759460695480c00e1072420311403400d072140108502001d80a4880510036403000c1d45e0b950300011400307410100550200080760380c1d0400901c00303047c1003c4816124200444018000c80707540d0409000c6034014981031000c6a0403009010711a98185000b0408082100100b1060800d60307510380b8445041440c41c8034000e07044032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 763702814 1250 763701564 763701607
    0x10b0f0121020a0206070905100f080703090803070504090f0c0f050a03110a09080c0307080d2a050a1a01030503030a020c01142a04030f06050903040b030705040f060f140c01090206 79
    0x41d901e04c90340f0b80724810041d00030f04030480c1c1004280ac01440340c541d1801140c141e680254503040000e070504040c0c0751285103034011235610b00000c3c0c1c00541401680c0c40c91140e039001c4a10b28008105d03120300c40c2409440c0306040c03030f07204084c000c1c0441d21501251181d0041e0f01244802031415481d5485a000644000b20030300624506000700b1100c07910504000951078100d400f82001481900c802d0442502c01c3c0340000d2a22000e190301240c0c1c2681c04000a8098a00c203101e0401814641c1050410740c4400601255428100c41c2c000010404104008190307078001c44081030041e038800030301180c81d004005c9100000d016250f000100030b100c41c81c1040c82c0c520629040301d070b016852481400000305101da804010031044114441a010410950001b94019500d108481c034140c0c50b42c01c03403103042d0001c945503400075034002021300080c4c509148090041c44281402c1c10300381344103803001d885a01080e80326580705d0740c00305108814a030250004401c0680250a003035441c0000c402c00440d601040c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 763704064 1250 763702814 763702817
    0xc040e03070f12110d082205071221050d0f0f0c0c030f0905030601140303041a0405040b0f010f0c03020c0a0e04120c02060703080a060b03010e06010908010b0f0121020a020607 77
    0x2204c140c0c80c5a0001c1861003440505940310f01d0f9554820f012500041c0980507000711035810070700d941c0c00085c4201300d01c00c058050b0142c801c910700b09520302404c0c114043d10f1300d5103085030030002c2ca418458005040e44c5281c1408000032451042230140107000f0400e8444481c1410704042e0120066504101680e1703150380281c1e0b503070102d250f80c160140d9030708616106960b0541e100c400100820b120910400070942d100405403842c0a54584000c141c5c512441074200c2d0754140050208954640381c42914440c00060703401214640c08180003902c0d54050462a80521000c1031a141c00c061003403254000f1080e006103503a4541e40c546000407410902100d04580d0f005d8400b55058006008000c00141c00360f00074211860300e60241c3d811220300001030200c00030329840740c5011503145040340c05503020300742011a4403910301e002c9000514081c40d0384d110084907403403c64260010340b10010196080c2c3c10a081c82c0e41e9a0251220729249081300c8503e000d0210b2021400005207507004c00e4031802900c05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 763705314 1250 763704064 763704077
    0x305190207080c06161b0602072f01080112060e0106090203151903020307121a0406090204051e01120305040b0f0c150606041a07120e1c050c040e03070f12 68
    0x2000030000180604444117404100440c0f06d80c0901890b07000100c1403035108610160400440740d44d044000d80038005808003030301081c00f0300c40b07a140c80341d80e200400c02000d1074018103e51401c003d52035440740e03449000d41015250354983c2e1400d88250414002042d5185c0215900d10304181015411036000c48000e1040801e4809000c0560400460780107a98008002c0c000082c90410040074414281e01d00f10741d4030109501c100011035100c488d080c4034900030200070800d0013192040104481004000c1c8803007c104410620055801d102c10314152540302e0200c2044220900302500ca80c00303039501c00445000d00203281e512410a60026010b9201c1e018203c0b240c403803068140341070f0888104da1994100380180030803c61504044001c042e00c8042900c00f43c031301704054503041400c3c034440280d4808900d03d85400320442c24030004002c01c810b81d1814400010040d6665207403100d0411896030300c02c640304c60400301c0240043c4121030100d94002200700802c03141c0c0c6005a540d405071180074010814 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 763706564 1250 763705314 763705321
    0xf0a0f14240322050304050a06022e0f0f060314030a05180f0d0c06081014040c05040f03051c080c0307030525030b090a020909070305190207080c06 65
    0x9214181c88203607004070030007099400407188a0300039500020b002c00e40c3c60801032810001c4210110002c0b40c2036014401940e625401e00c03050009800b802e9010303400715444a405001d0100e0064000c903410348600c440d40c038043c61002140c501610000c20031026840c40c10f00b5200c1c2d104c5845e80400d048034030171035040c1b45024460b140070382c80380100325000c008140104034002da000d000d09800900e03c50300a160301e44240543e80400e83c0038542c10f1003140c00581086023844200d0300004e03501d84c4030b140c0c449054101400d00c4000d00c181c4c0d44000101d405152602c40c81c4000500a40036600540001d01c803136034000b035581c01c0c01c3e41d545048442e00d0342c2c052800d90141c0c0c0380034880c050803407043d5010f400030307851900c0d021021001080d0061140300a0314001d00d01d02e0f8101c5150350a00040c0c442d40d0390114403010080200019010090301e20442c40d881080850415160704505680c00384103030a0000d0680d40300c139030410b012102840c0c481d5240d80700144003402c1142980c09454016407a0044a0071681d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 763707814 1250 763706564 763706569
    0x60411010903020114070602161a0610051e040510021c0903020105090909100e0c19030f080d02090303190806041401090c02030f0a020106050907020607050a030b0f0a0f14 75
    0x4070769000c080d0000f000d81e100c00c101500a48000e10105100e10f000524101c2420100c040b41d01c1950b5049460300c65174000d5101003003050280740e8000c1012501c18015040c0221301504ca440350412900542c26044075190000f4200c03c255402040050302000e581e60131968001d44410188980005840c844504921581d2049400f4400e0300e41c10784510f45803205040801c01c802e0b1000300b001809114101800071250f500d800342e8a00c0a0312400141030144a84c410001c904100803c81502c26a14400410100351141280d02d041e64000c90600d1ba1440d5030300105000e8460f05140d2501480005902c0101c5c000304140f14580c90b0700c642d80d01042c3d450700b0303042009035290b0074528981d00000034010f1000320203a50200d54120340c1d60048030b1500c0303a880c40047c80394001c0e94040000d030759111410046414130740c1c241503000c140d5101802c00c034944103801070518010a0700c4072080503030b00c44010f1500d4031040380c0030f0f08580005107900340c00341e90380c1c40f001224032003400384400c108007000e00e204590 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 763709064 1250 763707814 763707827
    0x21501080309100e060d061710140a0c020f060106080103150902030d0f0e1e1008162a050c03100207080f0d090f05011a0105070b06130e0f06041101 65
    0x400c005041030302d40180f4100454900281c0c078481548258100162910070315240314040050118520070a0884c2a02031814186245e089959040350b04002020341240c0e801d020300ca502c003101d014001444014030b841281341442445042119200e18800420410b801c11201c1e41224812903259014549040b00103003035072a0010001e4069104406441c40c0b103000d48005a10080749240c0703070207010b50300000100310890b803580305400341100341500c50f042c0c01c1c01140c80b01c00d0011418012068144014a42c01c881d840c108240d0030440075404112030085032501c426150f4516a035900f66060b03441c10015128180464600d109100e006100017009003580251010540c20006c11410401502204009544004100c411841d0b0328501c100024104110100300c02d4000d5000191801010441c40525200c1c3c12800d81030001c2409407000181e2152007490340320109591804001d03a031143c0110150903154007040e040e000c0c03c14074280032f0300002101803007940958030360701c150130194005443e01c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 763710314 1250 763709064 763709077
    0x91e0b1b06010512100f020c01061202150304020a120309150315080c0109090209031606050d0b0f0f0d15020a0c020f09150603190908040302041a0a0909110a03030215010803 76
    0x2501704810b03141d0200c041ea8088420031100b50300c050301d001d42014180c0e0840365203400000c2d04c041d103d050074055003072040000280000d869403107451030401e60002903200e03015101d0700240040d030074000b400f054400c00c98480103001852211101c41c00703544028000e040346403049084000c0d811000100300000042c2442c2c4004180c4404031054100b8a41102940c01a00d6154141c400c0111003081c002020146000408107651203d8480d07034584d481005845160321803a1195100c150040300356542c14092181620046980d000e4404aa10b0070710240e809080369454010310100d41011020b4000384c0c003128940c421101c4c014011842c2e0101711260b20103403419444a412180614070a00f00240259000480100380c1c0001d41d013580b0841050711940c0400300c070200d80216003002181018002c0001900822a442003011519004501855050303c95010765a0b2100020740c1481f40b000c0c40c200ca99540900104291074a03800c000e036864407402c07040300c00203074088000118210003105a441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 763711564 1250 763710314 763710349
    0x150302070b101d22051504080a020601080706050a03050a090f060f06080f0715141c0b061206090712050f062707050a12051504060504020a091e0b1b060105 68
    0x701c102c85007120031300340000b58000303c07107038800e1148000c2c003d5400c0851611036071288c0602599410200f500a08041041e80042c0d03090340120018000d040e0000142e0f580080186800986540c8080300d0002425148401400a070200240801844050b4201411031140108140016580d40d0b1001c1d50ba2200c10300214910f4110394000d000b0107500143c10b111600e82c5280c19001a91f113001c1c1070185038040c2c080c809940ca803440001007141600c1c0102c07041c07090103d0f8001d0070194001d03044041014000c2c01c551180a01034006801d1500a503031540e410060040f00700201d1400c18140021200c090320132903c0f40c0382d5250880c042c129000070301401400c40c5200003042e40c840c20300c203a86940065a10005202e540380514005010a1007594440c5039864801040b8a4900c41031108884280c2c01c180d000398010003007004601e40110506080724108010304501c00c0440032040c0e6031080540100d07038040d4000907400d14042c0d503c0b82c04030403001900103a981c06d036038501c100404541c280c071580c3c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 763712814 1250 763711564 763711591
    0xc033103031b1d0f0603070e1c03020a2a08010527100207020607061a18100b0d0905070308120a020702090c0c07090e100f060f150302070b101d 63
    0x50f10b00f1400003140f4201c000500b42c61582101c1d5000500940c204942000c0003422041d04e016582c94000c40840c1c8411450251810302401ca1710003c1d12646c2c681e01c0039040503030302d1168506460010b8490045601d031100e0141c0416140c000c1c19004c0d00041d907000060030060343c0300c8881c82000c0f0301204c1200202c0c030001e0248131a00b250050107500018002d076400082841203402150703450184040000340b0b1681da0604500031010407411140d01c4113503600c2c451425040014a400c44c0b00ca038000d941a101040f80c69201c0c403070071000901b066030790040c10390003598800030412190340d020f086031410403007002045546a04800b0304900a05d000658481c800c103000c00e000c01640001400d44044003400d940c0d0164072100d215040d5541e0482603100c0e0381c0f014034602c014102d280701d400325040b0030083c01d1001c0c6141031170f443d0080070240544403c0224801743d04002c00e0082d07044581243e401030900040d842d00b403072941a11300c0107100d5549244c1c0401d803445000702310f8001d035a10500e02804040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 763714064 1250 763712814 763712837
    0x901150806090c04061d0901090e0d08040b0a0b0d0f030905210705011d10081f262506120b131d0304030813120b0c033103031b 56
    0x1219a0346c04072944081c111025072000300c06442d80b650380c0740603181d8600042003810390617041d179251903239030001e000c10041d6020922000881c08400c45070444e042c00401720b0034007800c2000444003c0290130042c4814000742a84081640180c10801242d504495100b0040c8900c00c83d0143e855800715000807e400a80b414483c031341c01900c1080310150020b403540301030000b02000c151082c1c20242428085007485080241641e00c00c1a01104000b5242080e58240e141c940c100d1603000020001c000014131301c41c00d5080c0008200402502203068428011201d100d045081d418500640285400200c2c240150780b01c001003401099001807001d00900c0d900721038082580000c0c06002c0711140901c100381d0411000e0740080002d80095030007000c07034076501c116a009a95030b4200035404000c4411903154114003048d10103114990000d00d078601349541c0d50340c2c42910f03060a16803105010070820303410740320801e032202e00e4024060144661020800c0800810700c520340444140140c00000b080220b41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 763715314 1250 763714064 763714067
    0x3092b02070e011d0a110d1e0905031c09051504050c0105030c03060f04020d060801020301180c0f2f03030f0f090a021309080f030906071407020f0f0901150806090c0406 74
    0x103e45c1c80201e40388001040c4d1034461402c032141c0c1c864081c00c1e040b01d07103a0070100041c10380d403950381d9818031869900300844812540c60ba40c89000d0301c5005031401406001d4101209140d4005c07005c510f51041c1605c02c42d44c0c5c032031000360b8901400d0710162401e22581354810a030754004c5003182d0146a043c003d941c1035583d40c404000d00740c090340c9140b0380c00c10380070300c002d80004c08103005000241030044005030303c81d8100004400c145603050940074005060982c1b008407070740c104411000002503490006200b40550ae0304403101c0030200103103500380c0c200003200140c081010010307500410100c896500240c4500c01e165456044c05e0714021040d4020701407000061030901c1d006986007081d00404107040240d900d0301007040d0040d20700308119a0001082100750101488955448421418441805001c400e01d0410718000c89a0003030140c0500040707400d0b580e07220b0580c50443c06005044840940e190300305103940f075401c41e0030039011403440380100d44d2500e00808181d110394802c0c080c90b41460b160810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 763716564 1250 763715314 763715369
    0x509010212130c0504050a020a110102120403080424020405090a09020306150334080a03080f0603010e010504080c0c01031406010804170316120203070c0803092b02070e01 75
    0x70700f20340511862400040e00c2d02e550107418450009844c005840380c0c0e0304507000c0c002c4025138152078031907407042200e68108411910380940043e01890b106105039154900ba4240e1001049400003c0394465020a610500e0750001d00c140c03002a01d070320680b602c890003103500307858096100070740c1034002000080303c0018080034000030003801012600740504082c00f1000200038800d1041e50b185041c41c0050b080300d902482030000386240342c018080e0740710030b0b10000c000c118046c1200b0031607004440410042d1350b09402c51440e0b010498001c0050b800c1034541802941d2141800040500a41030f0035060796009224000d0000301350f4402406680d80ea00c01151a140021700c211610603440c90f401a0740c1c80f404e4041c51181a0428038a03103046400071025041c01565076a03441c00c2401001041400f07075000540412003a84107403800d440381c648040142c241003410422140c80c0050b004410f0584c07400c101b031050080300341d4090304d040b2031300c0b00918100c0d22000d003e00041c17805034131190f0200c0f107074014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 763717814 1250 763716564 763716601
    0x5191b09061b02041107061a0307080303011a0702040605060d0c080c0f07230d0e03070e070c0f030504052e050306150903010b1003020c0714150c0705041e0509010212 73
    0xd00c1718940b8401d6903805080707411038102030a40241041c400803c7d81420000e1300d010b002e1400040d411989071030f0102c0620312021000720860a00826500704640f200d402900242c0802040070743c82c1d009200800c0001c12058001c1d9000881040c08a0548040391040303a106149489440d8a004026203c100c50700420400c1101078549208a14000700400e205207640102940d58030782591520f0001c040c900f9039241c20603451401d400341400409078102d42c5a480c0c080e80185061090200707820305507121b000d982d0150303030064030308240380b0400600d620040f07602c0002c0b01c0400b2810301c0c860404581c070f80000c962058108541c0a000b4030f414000c403000d4007840368010b00100c2c4200b00040032490889902c00c5100c0030907004510800c1c068002d20850b401f42036010f44030102900107400282c10490071540250f105000091110320311841800034170302404000d030041c84107103842d10300812415190282054407915000c0458011a4103001302e0710351511000e80c40880382c4408008815000420 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 763719064 1250 763717814 763717841
    0x110102190303021201060f0c0f140a1203050915040209060d0602040801020a1b03020c010c080915091f05030c13080f03071704050a03060c1709071703030103020a060305191b09061b0204 81
    0x1202000ac03919000c00030151464810841204d421300302c4a8050f054440c0541400c0d440e4006800d06681030002090035a40300c4d804940180640d10303603001140d2000301011001c1c09072400090080360b4046c0540041241c904a9651008551541104110701d01d594140050058100021040c9d03698840c5480d808038900549140d850800004002048280202030581044101154480c65403074100c80c091402e042094800c8128401024001d10900c802403001070b4810703010501d403001c142c0204005004d86003a004072002e0103030b0f00d40b005a40f904112070031149180b089070110a90031003502a1411500c0c041d051113000c030f04642e034820183c004208400200005075041c1c000c50206d505480380a00c006602a02a05041003a4140c050319030400e211000d50080004000680b101c80c1503d040b50194a80010700303407600550118003803194028441581e051014020051044902b001c007e80403a844082807255100d0702a10001d20000412141140303407088a030250138190001008603005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 763720314 1250 763719064 763719083
    0x6030606040b070605010306050108030a0806010305070c050a080d0510060228060c0e0301110a0518120d051804050c0901030b040b120705040f020c0a110102190303021201060f0c0f 79
    0xc82403221202c3e041414203036011501d40d4010428080c0908c141805401c22201035072404029600c0030300300e0000a81464101656800054a110312641034248c03410b40c0042600c040080d1030031304e08031a410080101c1d40580c0340c44013144040c1d184441ea81d0803100e158020b802d20001c5850004000240303020f220340c00c02403a20550f00002d8907841018042402a1100c1da40d9040e8401450300f11280c914507a0008201040f14052940d041402e45c0c54241000f100d1828808003400829040700b500702c06d101061003001598240d07942c110b0003038007812241d01030616480000608002c01e0315820754218803074610400074180203520907000901301c4030000d8804240828000003060010709401e540c06165088880140322a00d0a4003c980d41840d42d40010750522019040058848071a5a40100600d80d25039011506074000d0080e41c201629020f640040300ca81410042c0195000710449035a183c00d050001c80ea460260321203100e82201c1d0303640d0685441c41d0744d0b1201c12148111405803a5400b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 763721564 1250 763720314 763720319
    0x30424060e18062401140a0804030e150706021b031c0f06120803091c02010608060a0b010806061e031003060b010c0c06030b03120406090501081509040f110907020d020c040908090603060604 83
    0x1b46071006010040e016a031303c081620b0076080080180ca8469401d91242d207004541d03090790609002a83d55090300244010b0799510307c0c1c900c01001146070705040c54240408101d80c12040c1c0c1c244103941081588100600405040e0302e04101152140d018181c00a110511b088003ca41d14070040c6030f10600000c201e131058628400300031008000001a400144e44400c414040e000c01448640c2e007200d840c0500b482480d074288006008004020b145500441001c0f4031818103601c0003128141c5210544031050342d07402c1445115810340740a0005940180c02d000c451101c9510680f070711140030b504000c09481650400e0002c402410800c0940360b4140705044007051154000f170010300080010382c541d80c003003074900400544000e1004080a05030350b00e82d4203503038440d11041c0200d0f91060340240c0f4089010528a046403d94018000c45a04031002000b000b000b26000510301e038030b0f0140c1d86c0888051079000d0080000f96000b280780100305d4107051207405030506219000c1e43d00030500801d490304041c2c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 763722814 1250 763721564 763721597
    0x150c030c0605090c1003050621071802090418032109080d06241707171e06040c020c15120907140114030424060e18062401 54
    0x2201aa0b840c005900452244c49543c07621860403d00c0c50b240d402e0034031180c43c01c0c0703000420107681a4404980d0280340801e05160000070310011001c1c080d209035500300d240e406041c610084d00082507480c005c3e4a0002082246140c130481e1f2180140e043ea1007036140c80750441c1b01d0508862031b04180c0700300ba4443c0740500008a020000d0300000361010302c0055450f142c034011500c0f0019140c41211908103c014142c1c60660010006e000208104042080c0f03480d002c0c02150381c1c41500b1400040c8884080c2800014a101102030304420310002c2c03140e101d5280e0004100481715000a400003583c0100a60340789400c0c080803080c14509200c0d00c0300d0404503e40d0303503002c00c1c41007280c604e103083d00305103800d2000101c2e4070701d006110300c420720f454030002134030b6091002c947c8805807000d002c11000e074000f01d4070006140d00c00c850010300301e001441082e41d00c2c40c642da40e43d01c068403080307140100c410301c2c8400460b00054051007050180f45c00741a034802003010000654040741154108140b1441100002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 763724064 1250 763722814 763722821
    0x15150c060e0a050109053003150418020916050412020d02030109030809210301170a02060a0507030207090b090423070e060108060a030302030a1d0901121b150c030c06 73
    0x3034000c10011500328103900d03155007000114642c005003203411f920782d078040e281d0b14140031401410003141e10340d40740c485c40000400c5c0615509060340c400c2c102290044050915568086014429100444541c4482182211124031000144006082800100a4411800404111540050080142284242c02090035104007090a5006c6480d210030f004400500b00218015400c0340e54a01c0c3e02d1111800f001c2034184818411440300c8124aa046e4520b00c8062140700c00e5968000d01140d80d5004801002d801d6800c20041a005070050510028a0820900540041d00c0e0004d064988503075940d900c1201c04040409100d0301031040740c4001075240c004110707100c00f4069440721583c032172410b40001418002c0c01040a0300629801c0c2e002c000182e000801ea46800c940e50408040000078100c0d412010310340003001300d9012250100006180700c12400c0e2103469070286101c4c0401c0e03c0d1010240d19050712920070003c004a03800814240d05108540d22080325100f45050014240340e0b455441c2503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 763725314 1250 763724064 763724083
    0x290103061e150809061303260907060c050a030305040c1e0911090a1a0c0307140105130c120201030209041a040e0a170f0c0d0203090415150c060e 64
    0x1051070181040c8500c02142c02120784410340e43c5046a03481c580f00700c569465010240609031910282c1440d04105405907142807118112000e403422502440005940400c85c10b0b208541c0314010071328040b0ba558416420b02c8101c1350007000500003043c06603021401840d000304181c0f00c040c46c28802080b084076001036181d528040200212901307003000012421600480e840382d81d40d80301080480c0d403d84504500004039203103000c064408a86020050009109020228030030b8000013585a042200700f008048000729003900800c41a6244254049030201140010380030340022001001314880204c4070b84040c0d88103240140c10600d0f0200410140c696000f4001e010000c0980980501e042a210744030310510001c0083c915400d19460790b92a100303956040000c41d2500103076083c0e80c40711500444005400c150211038098011020081d02c80c1c0194002c10f214908015442420081407a0900150350b600840010308030342d40181134404d100100803c548107a00d030044032907499405d02c2007155 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 763726564 1250 763725314 763725359
    0x21c18060504090b0a061e0e0d05060f070944060403080708130b06040212010e0103140303010b12090106030602040f030c0510050901121413030f0329010306 69
    0xc03a81c3c244080c0d14240c0d0003410b480d0f40102d540c0201040290b9200504c410707049116030842500301540103084402415032601e15400c100300c0a814020000c1c0007640c0ca101d90714101c00c001c80d80d11040f50840711100d00b4803a0381148900c1e2010140b1481084244501c0c0c01e0344680c5941e0040c00465803500d400c00010311400d910b8000d1010031040c960440b0103141d21031142d140a20b910f01c0d2039140401c1d00c4120700e00191074a43c0e6840020920b0300c60741d046170350714810070b0880c040e01d680d914107160950702e0900048400315001100700c24003100010503241030b00d85845d0000d080c6003144c402c03460300c1d04004024000540d290807000001c01e0b007502c0100081e016512810010746d045091550701034550f0751160740a007515000c8070140faa8498152240410700b460020b000d90b07010b407a01800343c4004040000c041d20071500b40140b08000b04652501588640c0794504a42c01205040d030480703c810690b03180e2004480100e800640c498a142d002e220340505002404a454591414030b44800b12032005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 763727814 1250 763726564 763726567
    0x1080916060314070c0c14060d1401031e0f0311030714010b0f03070e010306090f0c0807030b090a0201020705010809031b010b0f150a0509040905060a1a10021c180605 73
    0x40c1007281e1100f4680c8a00b83c2d04200811020700c6c0e945080d6034000f4441c0c0d0495000030061088241e80c0d2000702c503010a0702a0007803054140d000100109480284000c0301c0c6000c180b069008107103100468210040d0700070718201036801c841d403815110481018440400c41c00100311075000192000030540400100000000b050300c6040709010b80000c000d54010710076170000c2d00802001c0d4001340b501781920350204011030451014503102034541e0030344800400c54034903000c01240130700002954204481c040e00406090303071104000161510001c120107030068020070014403055004610300f03604454180d045902c0d0551039544003610210118541d46140d440c1d44041c5240c0c80c102106005940d81141c1412141c402c1d4130102e8898418444c12400340305010400003c0c641d5154412401150080c05642107440c0400341c50000302100c500c00c100502500300e440205041410380b5030208402a001070842c03078506402c81581d40c1039040e420f0108042440d111441c0c0300e020214400404480d2681c6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 763729064 1250 763727814 763727831
    0x6070f060e010b0f03032803020f0d1407050301050d060c200114090f190201020c152a100510030c270c05030c0c0a0b100513020414010809160603 64
    0xf0b43c240210800038421b610511403100c55500a44011030207a40341220900c6603890f48600354040d0088110312084440e0109031181c14503031682140c81404040c6101ca0b1a07952098029101c40c0001e00407903400c8025101100000385850b48200701c0b071040344c02e2100802030440140c0140c000210117a00382651100d80d4680030310b0411900c0b139004a41e580103400147d0007100300d03503a41c010462542c150064200f07100029a4000d03c052400740c100581441c060404030105614940e0140c40c82e8192502c800c6203846458916030059242844a0307009485040c10b03a200d00000381c0343c05020320000741000100000050400142900100031070386421100504280f00b1010350940c1002c0002000c1c1072804031a811035000e41125441003640341e900b501c9042c8141c03024500306450350020b002038811400d000048010309401c5080b00d0046800300d210b1901003941e00c00382d01035072044805030b030300c1240c03103103115800780c43c400d648000ca00d4210b4000c01e02d002d2008183ca84240e0005000c0303941c85001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 763730314 1250 763729064 763729069
    0x4060509131514030606030a0318030f061a0a0308030105040911100f1106060a151701091a060906032805280b0a1a0d150603060f0b030606070f060e010b 67
    0x3c0c0396070b0400c1100a80403c0c41c04801198a824560f1802020400c1c0c00440e881d080300346418000c007640e000404000250114606007000740840611407200c107580206004092070001c40b0030095903442420039003540d281c00203200190110440482d000c10180075482402d868140e00240200321560754001c4035100b05c0b0021f0030030208003030411a15080342080013619150f8140e100304075880e03020f003907441c150400f0045400000507104200815000000000d0242c00350304010865401d000070298000008420042c0d41c0c0f25840b07c1c0c60300b1210520010780042104100c01510b401c00e0076400c0030040183c04401c0403101c04032041c203080384103600350068030f40c0c4010281002c4000400100010b201010000310424880d104401e5046c8103034181003100780c13545081d18a41c1e10407a00034400d10b0710420780320204603041d004a00c00645004000a0b80010f0002d00d80202c8905200c05855a190923050010fa030740035000640b00c8920341c08a190014640384146804103500500025002815108 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 763731564 1250 763730314 763730339
    0x60103110d020a2a03051e07050a02010e011d10020a0804030308150406050d12020c031b040c090f03060207020a05270708151c08030c0a09050102070b040605091315 72
    0x400f9241d06130f40702001c0410109929032401a01420455100c00c000740d81e651041150300c01d4501c1010003c509481003000015105c1c03003440c0f003620340c1c211a0b00c2e4a401194005801c21600a40701c0345c0d1072084440b400c001c20140d0003080c40344181d1700d445030305864500540c0c1c00b5602c00c038001410f18007009441c2d0001c00110686220840d000c1c03040d0303854003001035100340100201403d415210040344441c14020040b5131110baa000d4242c44000001100030405440781502640c008e6090021001070944604251403c2c3d40c041250030008038210f8541d80020f400c002012a0001040d000201706991249005003a000342c482c4090354000c541e20f0f01500800015002205020480040c4405001c0c0343e40c0184c6020010340c2d880604103000c0c0229904421400302c058070f680d000005003c42c4010080042c0080140d03501d6038208123a4840049a599105120b80b040c1c0d54010302c4140812031083c4000c1110840040c2000c07050301d03401c1c00312070172503085000c62080100c401804000502c880355 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 763732814 1250 763731564 763731587
    0x3090601060224190516080a0e060117010618050106120506031f0603060903030203180a080a0807050903010e0c0a060203091c050a150b15071505060103110d020a 71
    0x7001d840350725011038030fa508070200054501240342910002480340710382d01c0340610b44030300100014843d034140750002c254507408140c40e40e00002c1181001403036510315070240405035080300005111aa19006203500b60008008020526549600340002c00c00c0c200d05400742c41c0307a40c100c000200d030351400401520788810401c1010143c0c2c20601046503554002c20800380e0b104030100040c0e00b00300c0b240c207a00014050343d00001c0a081c07401c0b03480b900345581640654840c1780440c03509c0142100d9542c03102e40d41c048007540100320002c00c2183e0000c0500c03501c180354002009003841d504002000001909543d4100030940d502d078003d10200d00c8928002c05110300400f11400910302e0130003100701242004003200f04e1445145c00a144d4402000400c004100e1140e402082440001c0c01e40070549014000d051150340c030580300d01d04001c2c44440c001c0c1c100c43d425079110035101416000c0401060103840014141c6040c55036a171840c488507a6841d004100352901310310700598640d800d000c0074086441c0c5e507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 763734064 1250 763732814 763732817
    0x141c050601261c05070524091207030f0509040507111e060c1b060c03160305010509180118080705070f0602070e0a090c03050c01030606051804090804030206030106050309060106 78
    0x856040b51034100c0451243e1004142c0c260107007090035815000c1e1010701c14000010828480d045c82086141504c000341d06201d04500e94000d5940c0387e0160503179032035251041a240c4900c04010080000c0c2c01100d039540c80c044141049410503d01c000014110303942114540302003881c0c00c010224850040c40103150301c07a6032101012284100030280b581d01c0034020b0220340d515000103142500440007941c1704141d20042d100301c0d111352520380002c401035081900c1a140c0500804043c0001034024003a44c1d041e030b140076201c001c0301e42d10702c520700c1d4441c01e680c640340d0040d55a600b000000c0b03c4050703000b11095401482c410340d981d5010300c0d1180c42e0412591000c9a82c040010003805410b6011800350125401904060800d03203aa4a1450003040107107402046072800040000802c4000b1581c001030010988081140e2a40c401054a40b441500500100300303181d803107e54044d1a0550026000d03a008081c101d041039220742c040b500650003038002d0302c04984040100490140100043d40c00b40c9000d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 763735314 1250 763734064 763734119
    0x230405010e0c0319030c082503110c0d0602220801090b130507060f0e0a06030e0f0a08031605160c0503070b040e2715091005010f141c050601 62
    0x83e013072248003a9510720002401c0210380d0880070700348036003403096400c0c410030000d03821082c45040c00744403d2050381d00401c401080e0950390008041401080e000058540079080621290030f80c4e480030000d500606984018000c2c403019006a20000b1402d0000f40001000000d1060000d04100c00005030040822030784100b880000d400041020032900300321a000d05041c1c1000302c3d610300945600d400c0700c00264100c43c0e14140000c0c40c030780c541c001807403003020172040e540e40303d0700950299202e80d00c00102070070314102000030510020964082905003000792501e40d04060150080c45002a048001641d4200100105102603d0300b445a030006054035480c0074a458540b200b00704a00c40010120008203850011100900518100b54101c0e020302d24207450480124090722080c0200543c0c204080b072007a4640c082c3d05085601c2014141c582a0301140c1c4500d141028a844080c000c100385900703c44900c4821804072210080095000c3c4604082d00866040032500000c620244400042d071004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 763736564 1250 763735314 763735333
    0x506010b0f070506010f060e0f0a0510051b0a060501080c09220b0a060f0b03040f030507020d05160602010b10050d1a090c0a02011a0d030c051c0302090307080c010f03230405010e0c03 80
    0x95440845044940a68044400c000c4c0000700383c0301d900814000082c0024153b40701c07548804086071030030f441c41c840c0c0c10170816a603d480403640c7d5509076500d0190881c40a0300410001c02a18210300015180c0080e8280c0721740e9207507100c4085140a030b5000b00d45c5a103500c1c080c0040d10f82c00d60443d010303006169205046240c26141d40002c41c3e094200179041c0700001418900350340324101c10b4008103401008440300ca2000040150400a00348500c00c010b5203442e54060152801045410128680303940d01410140f81314200310007007002c03440241740d0165502031a00c05807180b03030350030b4804e01c90072a101d511910030120180c00d564000e0480d80c04040f6001200829a0304c0aa4154155800d850541c1000c82c09190080c60a4044210650092005080300a10316419001404180c4041d015114800c4e03450342c09541e161403240c905404100884150180e65101e0740c40003190300c05403420b0f030503140101d030103ea0000b48203a800b030729281d45541400c010b050040090300c03c0500160300518601a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 763737814 1250 763736564 763736569
    0x20a0b0403050304020d0b15032a0909100c092d0e2a0c0114010305070e090c060d0e1e0d0507020d0507090b0312070506010b0f070506010f060e0f 64
    0x400040c0001c1c00c0c0321011021400355195060742c4111280d01c450a2034450a00e400401310031450f4032042d030310912500b241c0420b00fa6200f051060503030304c00880e040c110342001d001c00800c200c0c010010f00c440d115005c10100002003c2c0614203407101e098603103411071270818401c0509940803800f003c92840c038190700c0c0c2e403a140c62120901c0450750179130501d0007541c03100b91091144d0178800355040390301c01e14400c01e085a141c0100041108052440082195003484448074085040911001e0034175004000d080200c107484040a0303500810280a449450162a0014045030401c5100340710185c0d680c090b85180703000c104654070803040710101d907482c1018946402a550008000320000b0084085211005c64681c403101c403a080343c0c0300c0165081e2580b17503100d820051001041d8280310344200101c4070440301f0038200b101c00742900407000d0320181c1c0c01e01540204551003510b095030040c800b000050302248007804814040c0c0307591105455803a04d881c0700103281241c400030803840750400c200204041d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 763739064 1250 763737814 763737833
    0x2011403090303011703160b0a1404021503180610030c09050910021e04030b07020705010c0302061b07050f010b0910061215030510050717090604141e030316020a 71
    0x60f15070661916120003c9011903055025047d03101c20141e481c2409401007107044114144074050f404010480d55000300301c801941034050728003a4110303030b0440c2944400c0e003600004581c4144034081d54038180443e90a807602e0001c00301c40750340114075030074014404c120240503004014000600180421f003000da0303401d07441d021140491040c0c5540054610b030007891a00c0e40841001c03210b200c0d01d03126a034030300304001d654a08070b907600c005010348280400c09601070100c826400303400d03500402181d541d444000b03c1004c3d11a9540c081701d03406105040005000304104c002c42c0150b40001b14020350b04d40d043c00036011010304031a0381c0e0407106034248105c95010b03500340c0403c03002440129039400700010181c0c020710a90000b414038010141401030032600c1d500454003505aa03680c1e0b0600842c90b8064081248042e248501985c0259001c500807681c1c100000f210000b03c2c4042d0344030a9a02c0102c500301210320181544c090300044208a074a100d5079400d403a440703140380058000e1758055580c0da60740 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 763740314 1250 763739064 763739069
    0x70215072001031109091b0c01090521040905130f14010c0e01141605240f130f0327030b1f0e0406090203120d05060a050a1403030d1104030201140309030301 69
    0x1440301e42d40040c5600a54a02402c2142c00c11502d041d5501c008c180d085001c2c120703080b803c3e5200d03c200d02240401d400101c1090a1100303103c0d1300c99080500745086c0c0c00140c540a811080400c3c44078040c400440c000b130b40f201140512802404425800301000a030030340d01c81803441014061040000d02059801035411121811a90b881d5a0390310340e001c10701d11680e0080c0d140a0024420340d848500a1100240c03c0031281c2647c082040450780c440c0c00050340d40600700c5408950390001410b003800103a8005414609a1013414425900e81c001b10503104011101710802030700345c454140800c14005074400d103e400c003041b07405a004403403004545030f40814107480f0300415114048000b909002555004e946850703070040540d240d50328046170a80d52a0089004801801c3c90400170803580c4c0f85c074680140c1141c0c000b429202c1c42c0b9162002d07500d500c0840a59582d0180000c010b4209000e440b0305c9140043c6101c8480d41d520340b0304500006200b00b0081e001450004000c0003440210200003058070b04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 763741564 1250 763740314 763740319
    0x209040e011a040c1e0c050618030f07060f150f0506070807120912110109050f01090501030b010e0a24090602070e1b130501120b0d0206070215072001031109 69
    0x550b203103000c0040303619041c449200070f0303450360002001a41d80e510400ca41c802a001d00d044423a103449180e60402d400001c1e91000c41c896004200d59120002e891010300001d138050100000c405158088078816144443c1d01101c0b1641e06402c2841010900800240580815251a8209030f1207545c0c08206114100d0f014060b075891400c010407030303171140c5508405009600e1000400140741d01d410701d075520702c040070341e0f02052450030b000c200350924075014914100140e580c80102842c010040d801802c0ca911001c3c1040280306222441e138880c2c01c0700f0b0001341070b1a2204150954103014618807010510501420804002c0d02040961340c0010103409403456100205000c1d182d8400e0784d820300d03000e0301c0c50000540c00800c6a040796003905212008640c002c0e2034021907200600070020459848501140c0c0c0007041c0c0e125440035040c02c0d005490300b03910203002c50810001d544400b8949401c003241c115803c1c00402650054424680300500c000382017800e0601240c5242c03051070b246030046240450 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 763742814 1250 763741564 763741571
    0x923040c03200c010b060a0201060524120c160311010f1503030e0d020d030c0b1006170c040e13030315120308070e04060810112503050409020d0209040e011a04 70
    0x154003e002c1d4400d004620004019a650b0003007181d02a01a05184c46030511400001441c0d05130441c41d224914200d1000c0ea42803850105e406402c0c26a10001508807940400180078400d841d4108400d2401d0480c000c0d21180c00040e00b906540d400d451004400503c3c080c20310b0b451602c4101d1824000b42500d9250a0144010160307034049600c201c10180003035030114074500700000303054000c4c140c4602940100018546951241c42c2e001850000b4880c3c8000264140f0004040810310000150040c914140e000e24165880801d07108805081c1d40c04013282d15481d8404c8209030f0588502141e03101d150075a2119180f41110403040c0d60030300b42c0042c060108101c0040c00c0d41f885005e4860000c00d00420412445440d81c131f8966841342d064480010b101e26200e410f24449080d07405403100c1000c1d80507195201d04058480c2e1154a1030748108400340712003408081003000b41e84c0042c0a00f105501001070f21608101c1c2000150303030b100d030300014003645001707100750b03c0340d1031403d07101d0300100b049d1000f2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 763744064 1250 763742814 763742827
    0xf06140d140a0f20100509040914010608010c020d0c02090109020a030f380d14070305010614011b02031b0f0405010e0414120a030c0923040c0320 64
    0x150b08007412002d00074008682080141c04021440f80d00324240789810041c64240c09000d0306002c0440c0c1008540c802003401808401141c0c40c10ba0051807099208071154054480c80d041c6d51400c0d0351040d001914940d440c0c2981a01c5550304014165105032685020b007074111607a00032030600481802511102500001c0380c0080074043e8002040201c0074007010001d038482c8250703080e2800c03c0000503518800c103403a080004800c00c0e428007060b07900f000b4107000c050406640c44030044202940c0c031a0340c5008440707000003c61000e110b503200400d48108078000e200e0001d40010f14055460700255120340c80c0303141c281e0250320002100c00000500e11001c46110746e84000203514802c0049245a02138200000451142124040d5600440c1300b080f11441e25101c0420790fa0300e80e0946062401c49a00a1121003251882078209035643d80341401c0211200c2c0e110301824003c8400c00c60820821107881c051a0001c0c1018881e003a40340746607140c100809030760002030944642480b00c151200a001013541d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 763745314 1250 763744064 763744103
    0x120703120f180507180e060606090d0f0303061805070206190b15180607020904060203071b0b09070f050105040501050d0b06120405120f09040207030c080c010f06140d 73
    0x1c0300c480c1c00d0702c1d205500301504900d015683e4078030b02e0107615111106280310540940290007118402001035001d03001540d02c6105010710307601314041503540000310a64000101c2d07800d8034a00d64080c000e41c0c010888505000088246010790b00d40c2c201d4282c905020041841e9000c074105811401070544143c4e2001180300401c0070b0300d082006aa40312028800c171184080c4a90010482d084025600428440c1d48604120313813801790402c06508205450005000035110303a0055502000905020074080701e501003174179811407810b0301152050044428090960403c208440040c131400d02150308490034070000811a00640c03083d80e040c09400714481200001c2908007041055000d010a51244000c0d04013030043d010a507015100d5014402d5402c40045074030007240c50440001c0cac6402d180000100c1408001d5010400030b804100d450401701c000580001c1c01000300840c010004108030301e499001030102c90140c0d00c500e8899803541c15400b11920b800f0403403c260340d0804075a0080003030a514 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 763746564 1250 763745314 763745321
    0x30509191202100c0e0102010f020c030f07140303070509130501051014041e051807090501210f152903041403030c1b030313020f03010e150603120703120f 68
    0x3851000d0f0b0742024201d10807036600c0185a02401400d9000380040680f0201c107008903c1403104004d80303600108032825440c1960801081d11511650b80035901c0f00ba4400b0780d50451b0000da07002c41c0090400a0026940d1402c215142d00e40c00344403400b00195451b140c0041e9143c101300415000f07105441d009030850f4003070001500c00501043c0030044100e014034103540c028030190b01070f4a00c92406102c0005068081e07000f01442a60340780c0720064500e040074015105a00c1d000d410040640e01c40300b030b090180a8600901c40080c2c02c200d00410003070b41300392041c0d64520064014901600580070b015044402c072140009924880c09200c96680c4c43c3d40c1048404032803401110f41b110301c000800d00c03940c40207620003040503079110814266140240340e0f007140c9901c000d0700c05007a0111040301110240c82d010602031a280b40003000020010440c0d40104d04080e141d6420102d840c06100412195007010300a40340003071588060246006407694000c0c002d1261103090b0346101d0783d1035100e10b44185c2c01d42e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 763747814 1250 763746564 763746583
    0x70528021504120f020601210c05180f1308120408090a080703020307091b03111306170a020702090c031003020a0308030a0c0302130b0705010f150303030509191202 72
    0xe400007100c0c0341c541444614448002c0a0500103802d0141c00b1056130b201198850503a400b14085070a0203c410035030144451002d4000e0362042200500042c55035208180b0024000611103002e40742e25160405075000117000300110428280004a00b00242000e801c807844070038000300d081c840307031110b0802c2d2a40d4018129002e4004540c400c2c04902ca50b0001503540c00c5a01c220202c0da04161250304500598400d2110310303520060002e080c15a003030081d00650100b4244296590030700c091000c40d407600e00826401540810341020754182202c40350b905030350348903c0d0000203515201d03a80e4045070403904002e014250088001c40807980c409410f42a0340020354004048004503500d9060100701039100340c802034105494601c800c00c0107402402a03c40544801134420441c0e880d110b0003260aa1183d84103ca8079540e03504080704084640c413a00320805c140013000d13030301c6600710315015080b62405410a501503010007240c5881099107904031102d550311060842c08080500426450480d506 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 763749064 1250 763747814 763747843
    0x2190816050102070305030f0a0204060f0c0f050d0302071509030507030815100f020f0c0609041112040f0201022a100516080c0717060403030b03031606050f07052802 73
    0x140c040117065018024502030603030111207081e151144101d41c002ca2249100d0800070402c0761000b000c1d564000d0411120560141e407201120702520ba03586420000600c04000c0400d60204410042c03068030b584440c610a41c0311010851403245440141050091070300090400c005940054100d40904111410f8031030060000c4100003075820002c0d0071482c2044640b0011300c56041010301c41e038000940600310310809070a81d440d0800340c005000142c445082c0404070b000342080f5866400411980c80780c4141d002d0884480141d0b1184002420400001c420345580804800151144601040109403d0030302320b0300102c55030309580b415a0140142d52914140345c0180c3c2e206001e00419000514242090310300b51070f8003e80383c48113601e8844109580c03010a91202c0700040019003c0c5d80306007030204008007180d05052100000da404482e152200711001a144c030103000c10102211805a0489500d080041c1465401c104c2102084151200f007840c010304400c00404d4203001380400c44c2e0841c1c02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 763750314 1250 763749064 763749067
    0x1020307020303180303190c02010b091815010e0106030c1103030a06150f021b0a0e070c110402030601121e1118010503041e0203071d0a0b0102190816050102 69
    0x1500c0030351203400c2100c00071250072550100c4403581d403010003182d00c1200c0000382425446a20703104030700100b21001e480c409665852111680560752614110320500612a2000308003000c0504c140c10f0030340307019829414a201500600c914410244688c1c15a12140783c0025038030382000f012125450300e11034804c603a000000510030801c0c07140d04000c0996110100300c4101681172107040300c00014900d24280143c00c100303045c0d40080741d031040b40c400b101801054454959190254100d2500b41650303403c004c1880301c50034808004001081544401c003c5504504600e0242c00181c80e00401403040e07040603568000010b00b100907224142100e40020104100126084403003420a0f0320064419180d664203061000d4150310841c110303031145500c000301c008690204a044a102c0e0305100c0200d80c03500071001c020820050112050b40d140310400440221420110950402c8a60304c0040e01e0454200c104105052540c4c04621100b00750312145143d40c2e4002c071038625120b503a5004004026500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 763751564 1250 763750314 763750321
    0x90d0b0108010e1203100b031b0406050c06130c1214061914070c0803070903020306040b150909030316021c09150c0f110414010305070f091a060a090305010203 70
    0x815400303034030030300e06200842d4513000c001c2d03038074040d14041181d104682d008250414020910060050f5070070000305203400000a0080d520500150040d4209030001007004c250028004030400003550046400222010340312141d45500c002c2c206107004030342e11400c250310150200911500b44008940c03419013916054100480c0441340040100f941074482414910000d1032004030100040c050980ca803030310b50000f04c0c10741e2141940c1c1c000400710414064a8807001001d41c40a1005d24401c1d44100c0484c074848c54407400d1003143c0310132001481d001d281070b00100880c9240001c01c8a42103411010740341c60b28460380a08030f00e01060321074a14880c044030740c40420344541000d035400070399260010100c030001207818200e408a4404801524010069010340040b5241000a02c0c454501501c040303840d140c0d1070300d04030701c07418281c1c01100d030707a400404208601d601700e40204018041614090251265078070a01c3c1e03049441d9200c4a01c1000000b40d4410f07090f02840c84040219800f40084d516850f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 763752814 1250 763751564 763751579
    0x4020306033a0e090703110c01150f080c0108041506170f01050105010f0c0602031e0f0f070201020c0705040e0c19050102061008031c061809020f0a05010c08090d0b01 73
    0x220000c040b9004008404888426003d5891501e9849001d40040c0c00741e40d03660805c4014000c0314881014801c0100480e0380a95000c1c05a0300b900040140000050f40c540100441c40c200e01d070740184925000400e0004203030780c1c8000399175003041e000304000e10361805030b0000ca801000954450861200440c41a50743c021001c50b0400310302141c2ca00070040c1e41e0ba00c400645400480181e10740001d861038518000095213503002d150041855120481098801030f01c80980c04d406070780045440d0001340c01c202030f6005281e0a80c1c0d20402510003581040440300c83c1e1070b95013441d4082c2c94810381e00e4840c003044a610070401801407240003002a008921100e01d40300c107804250080381d00501805c0000f4043e001400780b4003003250f2401000b940342010052202c00c104003420071001030b0741d45500c1c0009000c0c03107011440507140d21283c400900420b483c410045240e418a8025014820f036100070040e40e070300500c1c4400b07600d41261200e0364507242600091901400388070010302e00d032001c200204022 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 763754064 1250 763752814 763752883
    0x1b011d03010b3f070611031b0a0c060f0e1201020f1306030c0e090c0c0109080a030c030609050c040e0414060106170603120d020901020304030204060b0901090f030309050402030603 79
    0x20b1858258050b1500c03072110900f0310703d0002d944020380d984c890241000707828403807640b19046241c1d072001d82c2d00b84007139440041c0a05428011003844d542c005100c00c000d114004042400802d514180b80640c1c1c401400d0141c440d4034910040d51003600d0140c07010b84190f200390102c4469034a00501940c1c3c03039158405041030300304940143d00c00645003403404402036008501d92140f401c00144010300656070b006e507407260342d0b118000042030355484611510000d43c10321701030300d01e04c0940d84001c141c0070032455008084990030b03408111590300b881c09200b01010040200c4003070f20301190300d00700c07950781d00c2c20100c0e1011000900c4084511135640000307440365010400c1414802910b1074841d071619100c007051740d180394528284201c51002c00405c0d210f4445903004040c141d0301070060340d05180c0c2d280c00003001c44040358800b29000c14000764006030740d0b0340b00c0042c001410070400484c5106003152001043c3c020750b40182405540e000010a100f80d40810415103809101070014804074842c4419450305c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 763755314 1250 763754064 763754119
    0x306020c1908030609060f03060103030210181e0309180506010f0e030706080912040810060f0e150402040905180c01030c080c070c0803030f01081b011d03010b 70
    0x40c040c00c9520000081c07119260541240c01c00002d40c1580c0b0340a04000c11150050b24503540591400c100070380d0f90324140700c498000c50007034014240304181c2d00304946c1607031200c01c05200c02c0d40a03030220304000f82d003941023a4219610305c024100c0c500040d04d03055401901580000d010901d4109101c20100c002d50081841040203981e4500c241c1e03c58442510b41158403c04150f241d000f254083c010540319440580e07100d0360500c01c4511195a19140c07c04640c4541c010f01700f42e40241011003000101ca002d00002030114805100c1312518000c007800c1031200103441c0c0b0100c11194029202c00d90f4558042d9000f4015044041040c0d003071032203582e44020300045030b090841c00380e111400307038030b60092003481d4620645480e014925902c854002c1410381c0400c100b25403a8416002c04510f82c4070800c05180b00306039113800c181407941024000c500d8a1002103411421040c0d845005245036032040c0800c0c0300c000414181c846203124400028050100c0c401615084664a009851890f03110040d1018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 763756564 1250 763755314 763755337
    0x306020a02070f050d0f021f0504080d0503040201080a11090a0603050f010b031003060216060204080f100204030804090504050c030f0d03050604050f041502210601020607030b090a1d010204030602 86
    0x1c01a80d4544402d1000300500c54182d10035176000c1c00700c020584031003079024030310b2008048110700400d8401031070078141910818400070b1030201c0d051104060401000000c0c10450800c0c909501d0b1650008000307920040c0440b2402d5102d00301c550b000f001110a50313410a00c024410b9403d00d4980d00001c001340000c0f10304482100d680400014a0408a01141e0003070080d440118160760464441402a6000c074020b20142104941208003040c2188054005014000003031321503c0c20600c0030718903010110b0b00d00004588100010030009000004503000c840c0442400302d040c1c0d03a5410503070704011840840c59014000c03518001c0e01d4034404241d40011000b0354408206a450744001d2004640040303c1c1c0711f4a012a010205020400461524a444059100151904d42000d01c103091020701a02070707480f64414041801903541c1c0501100b9400384c034600d03040000c18200d200064403070710301801441c425039550b00002122040502034072250341194000759502c66507481d00800035480380e400b40d030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 763757814 1250 763756564 763756573
    0xc0c0b0a080a1401050105090411040306020d020405010f1403180c1810060314130c03141e06100326040b091009080a1b1206140612120307090f0306020a02 68
    0x11008001141c00f0781a540180d480300e04041103034060000801100700300c5002c0703480c11300c80000011440c0c001001035a400340c40150300c8600e8000054030204030501c490f414000e030b018030700944001d05000e8a40c01899103021103d0749079002c40c542e0a1241140c49e036078014a142c905500d21400711030006000304801004d1200e501d42e6460110200d0f0a0b0b4400a064800910702255288041c01207012100d802035035140c2c0829526503c0d8041b20740300b44c411076090341005841031940d15580b441e103495211130307002501083c6840f110720a00785e100c4d07002c0200480358080d0042980d0111041061202e018070000c80d03940d94071145841007035084624150700c80c1043c102c0152242e4420803040e4110b885010041c804000d007135179141080558002d0182c40c542100a000a403004800c8240c0c1d00b0038011b410004000450010801d210300000740040e0050744920a00c021889001903200d00c1d203e0315442c0e0301d03181e480b26401101c082c2040c0d40802040b010341c04000c402c1c440554003d143d68840e030b40888 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 763759064 1250 763757814 763757831
    0x130209040903180f03050703062a020106030b0a06030809040e030d0612021c15051924150e0609130e030d0509063102030304060c060b030c09070c0c0b0a080a 69
    0x1c0c514030313610303001c0100250810942080094402d80080044000409820204240340301410341e81034889141000141e4544100b00b05115114000903003100e80080280100c9045440341b2a02d403040b110841e0142e550350f584010606414410b882c0031002c10b050912185507202107008000800500c207038425085d103002d214800c1050040320319443c0c1d014805a132002c601e10344100051a00609501800f0142c0344001c220148600c03800c60410f407900100a60300b0040030140ca42e112098000b0a44003030540c8040e045541c0004551400d46402c603001c1d665903c03c440030500308100c0d0b00301144d05508084018081c81c0c0040050b05103000610800c00a039a0303107a4005641d080e05440b0107500a143d03892506000b0301061a80442d00c0c40e10000506c14035a076070100b0701e1684154810760000d660341c000a0104481402a00300c0c505085008003a10748038100002c00c208405403500701407025038000f00b401c01248201ea200104143c240c000e49490100303001900000b821511107250380e280070706a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 763760314 1250 763759064 763759079
    0x921021503042a08010203041a2a0702011b060501030212070f060f02030c06180f060c0322210801060816050c030c07290a080613020904090318 63
    0x40d41e2255070009800c45a45030b500812814080c0800360307420340ea0050f46008201014240003c40c041ca02c00d1101d0306600c0ca083d183c5a00e5800d010700480c0b460404205036410044d1001541c2014901e1080d001c2c0c0d030b9102c50b00c0103903510500e00008c3c280d030501031034016052040d29440a4120384c001e0700e440c2e1004601c002140d80310000d070300951030aa01c5020040c41014802c00c2d01c00d95101a07401200e24014821282d94074018040b240744d110280905c8001070360420621004c074403558481c1c0245801e0410100e01348443c00700034401c084a15449040034201c01c0c0e4035012800c41c54000c460243c04c030751110401480c850101da5898040b403154400003c10520a1001d1441a00075816058071030203078101c201c4031948000c03085c500034482804190f0103028180700b40c0004002054030103107062102c0130b441c00ea00480900031824001c0034044410341c180c103c1030043d0b20800071120001080c3c07580b14900001d0003070800040d003091503d5502400c043d0000c80f500c4041e0250581641660f03030310b110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 763761564 1250 763760314 763760317
    0x71106041503020703030b040203041b0b040602030904050c07080301080a02040506090103030206132a2d03120c080a030b030c060c0316110d051510050a03110109210215 74
    0x40d6404640c000480305581c203200c0c0d80a440c12510a00e400314a1042410015007a0b07001a9415a002510017039040c00d50b441041d001001040b002d02c2c03840c201480c00b0000382d1240a040600d41c0901d4880c3c1c00a401d0003000c008480189031710980480c0c880d6110707034605a0f11410450202c3c0101c0c07400e00031800c0c0d860304001d07a90489074503900400072035846c40b107004801c0644d2541280c03040c05130652120406a54200d02c054501204a0207869901e000c0d04042e840d800d85d000d0500c00c90100c540d031001c10316050380030415642c100c1408503501c0a5144125541f081048025144000c0414801c0000340e1582149030703500411811140c120409000300615031007030711018006a402084940d110441c6480030030300c0709002d0142d00404505032404500640c04131042150a500201261104007424034407035a04090703a098030020b01820b010100f4450301e06c03070001070b00c80312204840704d032181e119144c200042e02c40800305240c20405402039891010050008074030990159000000d140320410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 763762814 1250 763761564 763761569
    0x70f020c1e012607020f010f0b010e15040306020a03020306010e040501081b030106030602031e130c181e0b040c020a0b04020d02030f0d050d230c2d07110604 69
    0x20001c420049a800c0103540f02c0001250180035001c600182e240c2d48a03071100f0b014892402c0d90050321500325128151821200c0301720000c1c2c0d4061030440f41036801e90340f088824140c48019149401400142c1c04426018000c81d480105403038000030b86c00e40043c0d81a009103003e07400070307261900f0103202c90b801c00068402c2402610400d62014600f80241c4440d40300c808411000036000284560b203944411081e41c2c41101c0301500d4490000103000d070154a4504158001c8443d100c0b400301c51844c0c0c1e0b0798008100b0078440c8004180c03001a42c00c501d040790381d01809501c510082d003101020031405028020f01610003180e8803a07450800c1120103c0d002042c500d01131940030031800078558503075007088041d8241c208240c0c2c145c450040ca400c8080001c0011044004503030b11029100e12444103900d040d00c25000c1c04010340b82d41c0c42400c1036541101c4c04400c2c0c01000550350a6150081d0491485030304164040c046901c800d01c60100c03070340690120052618600820402240c84452014880e0300d2084c0d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 763764064 1250 763762814 763762849
    0x705030703020106150f080a0f060302090406091e0b07030b040e0d110609070f0b071a0c19051812010b1302120c0a1d033d0510030f05030909070f020c 66
    0x110001803542000c0d42c049e08502101d003000241140c0c50707802040052500300e030b00f01d0b151540c0d20f12080c217106410030020404000d82c0000d0b900d03648540d41d140c000110240c03508061540b904645007041d6120380001da603200242c012521423003030703c0d10028030300d2220100500c4030380242008105a200c01254038801da0300000c0d11a072000307140241380c94640d0320480060700ca240210a1002480f001000d03814000c001e100c50040e250007a001801c808411480d0903213080c401c2c00c0250000e01e062480c0e410151050840d50619402c103000703001c5000d05000c5c030507a03a00044001c2d04c0010061160b010f495030300050b451800e603a1b643d030344068081b0701c500003811000c01c081c0c003070303210fa40c40410307101010003280030381910200010052888010300c2c0c81d948200031a4440b00304818010840b0710341200040d400c0307a0501c41c2d41000189200400001c0c0030181405a885a1a00600c002041120010070010b08903140c2407030401c070000e0007850751592402c0103000350340301c3e40900e00c0c021a444403001040c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 763765314 1250 763764064 763764077
    0x9031416080706020c01050718080309220603060606021e0604030c0210180b04030b150109090b1512040b100b0301260a03030b030c010815040209060705030703020106150f 75
    0x319100c40ca4241c214400442d0229000c002100000c1028000e1328098095911030301d00e50a0354641d21840b490072030300086a03540c23050141c1101a1380e4051203513840c071401041e08030b08088025131400a0301d01f5070000361546081180010340e0326400500d4180e4444900c40008081c0e050702070b0710781c560344259005030000320a4003902000d464000700c9110b594070542440000305c01020f0151401c030303003030754850150160040f80400038402c55440d807603407081502c40e101c042040c0d6600003a0102e49503028a04500ea0307183d070002e070280c9a40340c1342118048a001c20070b407204071002e003440058201b00c13400c4a5039240c400102c0d040400206011055444001c40242160300f4494040b2250b242108001240312214083d2841c0580620400d43d07018003990300414105411130038503107410b06202c81d1a04000c296420405281500880d2000001c0100c0d00960f40e0128100003a5440c09500806041400700141183c20590154000400c880500000038442419124241c2da950085c2d03140b41c001c500c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 763766564 1250 763765314 763765357
    0x9061406160c06080105040e150c1c090809040e0a0807080306011704140d020c0312030406090804090603050601061403040b19020a021f0b03071806051201090314 71
    0x24204003901c4405180d07100440c01d070509444010b41207800b648541d02142d4143c0060040381024050001c151120b540101004443e9070707072421034010002d01008084801040303051a6080f0710841012004440d5000d2016100505000724075500c104581c0d8416454803842c10411000400e9603d01503401503059800c2100a46401d01d8952000300a80e0401c00b800d0f00742034289250440d4940224011280c80c02114911a842c9151503200384981c410355019000c3d806603540c0c0000c865074120001d542d155103c1d1107a07c0c5c244041d18070084020708041c00842c0200383c1d050107910a200302c900039402c594160340d0b1014184d400d5000c6c8144414040000c00009020400442140780c0013141101c065003140c0d0818408001ca070030801b003000c01608604124200c1c081131a064450541c200d180801002203040000b030b9844483b4800c1c1d031591031065804071002c40003a48014001d18001d8032040e2a5000c10030418020300b02c004040300400c0050440d03a61451220099170b480e200420b0301440d283c403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 763767814 1250 763766564 763766569
    0x209030304050a08010c02070f12080c010b060a0224040b13020a0b0a0e09090601291c06030326011a0c0d02010b03060a020f1b0c030f07050109090614 66
    0x14000410250144020000007803207490380c1090400600110300002040c0b49640802820040e142d88068181e507001d06003804050061040d64107104d82c40747c64165210031940c54907000d424814001035120f1008070b00100d45035008202c1d200c1409044501d1a29900d103224044460b40050320060016001a0009151044042100d0031500c0c002420401e859540d0305101c81154005420342001460580c150b80143c01e1910b4200c0d000350000000d01895030500817490480341540c05400103901c12400c807491200700302c200705c551006180d4684840c11800c0055013000e80014030048001408840f4a00d080d00342d03840a20062400d101d4064103d6440e010ac03407003032180d090805140b104010045412400b10800040440c0442900040740c5e241d549020982051001022140082e004000c00c80c105030341d1008039900341800e40070350003004985801081c90030342007100c0c46415200c3e8200035400710318000b4400080310b409076203000109889401900aa0701e031442480112404071515204030f1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 763769064 1250 763767814 763767817
    0x2c06061513032d06020d0e0102090d0204021308060f07140a14030912071103070b1603230d050105121515012303010626072f01020309011d03030a02 65
    0xc1d111400d40c180070040f104080443c00d50390070000c5441560024031243c02810034024100d100368403000841c02e002004000c42c2e4007246042000b8440c50b0b001500300c2181215911404c040c0c2484021039659207000031441d881031505441803008207101d80d0308004841446011140300403151754a01e00036403a19200304003e500041c040c00c0050044405169a51040c0c0c0e0182000710b014424045a241c9910207140c2801c081e500a0302218070200100010b0252110b03400c5039440d410302d070a01d0003001200480703040030941d8a8070440c0b00700c002098140d000c1c903500928141c400031500142210100342800741d4510f0782945500603001c1c44000101c3e644031200121140c1c02060404144e1b01001c07249045140c01c0c90100580444400310040c041e02d603100b0307050075035035454440c4245066a511446441e9000080c040c00c100f141001c20055035104244d811200e800030b40000030089400024064041e40045410f010190701c0d103100c0c814000c1c800c06014441000d81009189035465004001020b0f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 763770314 1250 763769064 763769093
    0x1b05070b04050705190f0503010c140a0e0d030c1b2d0b070b04031803020f1201090c080d3e070b070b06091f092c0606151303 55
    0xc3c0a01e4034001880d4480b16015020034485d041c80e100b034a814141044807540c00b541110f03000ba03251800c490305568001c1c800c40400c440451352591183c40480044943d40c801040c1507401c82e1201910404064210044601240c40303000d15041d070104c0500585d031000704074420030a8140781051a0b485003800c83d1303c40c4030420110b40300314004540f1210300080662250b40100c07034060a110412080c994012402206107000342c000c01c40d4146540c00043e04080c2c1c6c40505032007030310380900180450800354400b251569005003200c4885690715180394031840071172500c8003c1000c02c41d0000200070025440c00401125205500002c40341c95540340c04201c800e0558130940c49010f401240d49030000014003007541c8a081038010078540135052100d40392028011001840030000304990020800701d038030013521044400015400c14080e202d000322400030004101030740c110400c11030404c0012075054842c80066a00c1104c118081842e03010038483d030301d55040c1142d40c2c0702003403000440c181c80407100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 763771564 1250 763770314 763770323
    0xa0f090203060702030a02250b03270d031d06040b0705070b010e010f060f0f0807051e0a0311040321140d1a0a08060402062109010903031b05070b04 65
    0x200450180d01003031400320300352200009a4804074944a5440d410070503043c603e06240d500034100e4204a410070000306250054405400c070100005035002c3c500382100c5541e44070111100004041100069110800220b055000905000204010f5014000b511814000390700041865544a44840d0034556000e0b11f400c0400a0812008010038500e103143d0780070300001e12010825525068500104601640c0040244101d80781e6041019403c140d02201042480c203114403603507200a011100b40c42544050301d500108103610f00840314000c40034101d0035010b51410400c0101034030104140f80113600c07005200c0c0d60884824914512280841c2c005150310781041301d000340003405450210380181100c0d039041a59080c0c3e0050b6040341000031800f00c0802d17101b00c09440c2c2840116034035180011300c00b038022900010308016405016801600403030100a00b01064101104c060b400b07800d40141c10f400082c1845041e11100001025100c10320384161075040c502400b40e564145078150040c81a074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 763772814 1250 763771564 763771571
    0x2040503060408090109060c02100f1103070302010906140903030c0d0f0c0305151014130503060403020607030f050f070807121a01031d0309130b1c14150a0f 69
    0x542038804221241c09070380b20b11451600e55045800040c0350b104c0355070294040016030740c0100b0260300c41309000c1540c0349081c6410700e0081220724050301c58101c1801d074401d0911001920070281541980040c01c170703a100e03503000d01010320000b021840100e015201c10020760020008600d104580c04024148000138072808114442d020302041e040329042250b02000c08c0c0c036242040440c120100d962241d10004456406207080c80f107900506403003411006050b11500002c1d4102c2c56280808903100501000b002c9030f0961606213402500d0703010584140001c03030704180008043c000c2034001d003803141c00c626170551107a6540c036008071000f00001d0054024000c000c4105130721001d1a000b0983c1600601d4011a01c100d080d07400141255441e120894001100e01d032000710030700c800310460345410812502c000d07040d220139204c0c50050040c00315540d80140301050100284000c0480012000d004002d50807907800d0700440e40d5150b02160b20a142d1101c403041c00642c22606550151000366404038000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 763774064 1250 763772814 763772819
    0x6092401050f100e13090b060415090b01020c0d120207080a0503090d02010c1202030414090609010b0304150e06011a070302071e031713051c0b15041d0d0318080304060204 75
    0x9000c450405402907000350700e1b1600340d01481511008142c00c14000d0310100400700e002102c40b4181c000c0ca01a00c268951105180c210b140c3c0b007003084080106e001481035105201c1854500303408a007005950b409801070920005a10001181200706182c11001075450038004108010074900700d15403c0741449000d1072083c0104d11414a0900d014025400031595181041a403100003221207224900c0f5809000070003810780c4540100314111600b00c41d2a640322b848034900100100b42d8a140c01c3d04003490b09a1503100880c001600504036800381c0440420460301d08001e08140c403c1e4900030f0096401030508010b03117220f4541a10300e2558103030301044410784980c0c40108000280100c20081c40d00464150381c24050407091400030310040324600000b00c41780c6180305138502040001340c071680038100001c641007064280c004280030b000380308000c401d01c2c0c44600425030410140d4160181b0a8212044589011f4485c1d95210307030a55a00109c0260243d4a442e6a40e00080044410a80a1000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 763775314 1250 763774064 763774069
    0x2062806090c0f201005061c030816080f060108270307060b030f0a06090309030b0f09150c1b01090204060609031a010b0f09040b0306092401050f100e 66
    0x600c160038403543e41e02601c03000400002450144000543d1080d071124001c00402c0c400d00050130b0286840b042000310b8540d59044c001000b40071042100d03075040d0003d440d1a810103030310510191040f2610000590071407010003003250542c0d001c407054200050450301003603c0d5802020305990207070b0301541c075018101c640340c0d107070080c95045002c91206600115400c3d04001e1a8051030041006c15402040390420341c5a4241d135601858001401e1155122441402d2501c141180800b6541140c900107890400b000e0100030090100c8503031080e40a610030392144d024031a155117014a64500c46103007403400d40490221016294011101ca940d6185043c4005072200e0050000505c143e480d503a04080c42c0d03050080001807400d28010810b45d084005104000303021054800460004c100e03141c54040030170206005002011002d6403501c986801c014100700e0021b100c00d03d07400e00c0031244201c07210000600d80e8000702030080f0741c1e00c40e0102d445035072241802801911501c0c1c1e1450014002e0004001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 763776564 1250 763775314 763775321
    0x6061c05100c0e040f0207030e01050d0f060f0501081303021209190602010504031101020f030a0b12070e060301061e05190909030f0f0203090904021302070228060206280609 76
    0x180b8002089900e6400c000f00c0c6040e109102c00b08065401c10741ca02000795400826a40352085030300d040c85401315844401003410f92040540d800c120508002a030340719240740c06800c984e8403406000405010010b070901c141c0446203002190705800034400765507900c1503d1115040603003100e07041403107209004400b0104803010b02c0200200d80000a150409050042c0036080015404690781e00402590100c0da52681c00c0720b910041e081000030b0300488080004195002c3c8298038035442c45003140c0801c0c616500140c040c0161000c0700200481d86e640c0c594100b40000c0803604108440e000c101c10811820301010402c0144d81c20003000b0142c0d07450704440030480d0b010b2041500061001055820440e1300704d0810704443c1601c0c00150f0030040a0800201c040748020802401380015480c0e200f064070580d01036a000d258018040900200c50700c422191000003511180c0c00002ea02e10002401b6001241c0c590148401c0044041d40b0360180c820380c0088034103028218111640d40740c0c0000c0c50701c1d4521 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 763777814 1250 763776564 763776581
    0x6210f02221b0917060a020307030e010207030806011d060403020d0c03050a05030304020112020f1836100819110a03080c0706031505040f0207170a020f06061c0510 72
    0x382c40b03101d26820140040c0800819000078510581c1100c3c004030340c984c0044d0080c0c0c0103500d03400c090380d01d9641c100204d0140c1015282c0c48050741c00840d03000201504219594410788080c3d0358449041d0000d0300d4011114004021160480c2040105001605160341e500d0307507450141c5090311403e40c0c0c0c0ea07241c1e4641141440700355220741021090204540c0e0110004c0c40803451041c095003005080c0e000451540702e42c0040903640c1e40301e100d00d0003054846604641c224150704801c0d254800c10881280001ca070740280000076103203108000703080340300010407a806440d0200d00a0448800c0201060f1b96080000b00030340b60034200d85c00482041d90380104d64405144103000740c2da01c0b10b4050850a180c0b0145800034010f040c20301d0103d00c9403406c000120030844004490101d100490080010003c1c818440701400f803840d03640e440c640700c807140001401615020345c00c4070544004194019190042039850b160321500b41c0b010a2106c0c55143c490f030544900030800e80740300302a90b0050f10308550401d0f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 763779064 1250 763777814 763777841
    0xd11060f13031101030911010c03031e090c090908120411030628050624090a0602030901080708070c0807080c0a110f0f0607082b06210f0222 62
    0x34024400c0007021a05142c5600f401c1c20148684180b070394540b0011500b000e40c0364104001c0002c000241441b0740c200150b0890940060043d840c007052210340940914401950b6560902c0710000d1003070001c1c0325106c58070350803c580d40d060190300010640e02e50340c082c2056420342140502d820b566501030021900400000a01080440011440c00c00d4600d40c40401c4240925003000c00a441d11202900e00300521001f002030540400c1401142d840e02545288641040b000e85010820035000401009111000d8803141102e40d01d40c50b040b00d0045007202c03440006010851000d0006180e6405011500c0c800c1708428107140422026030b1405002460903a000b0403851400036807400c1804c40d111030310790256543d90000d240d00c008103507140315540e8010300050740040d83e000541d0420119103034101c481c4500140d80c502c0c420031603000d05028000d8001d0b981c2082041264803142454041d80e01d41e104a4850803501c5507020070080628a840356180300000500300d40300454181b10b6030320848030700d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 763780314 1250 763779064 763779097
    0x10e190902090a08030f031e04030e1908011e141005010507060e01091505160e060d0b03100f0c09062304120c14060733290f0d11060f 59
    0xd82c140c1000482303c5010b08401001000034440802d92010b10710000c1c4c6015110801d000038200f825802d0180c0c5d6510034050707940b0b000342c40108950030500f441c5454005480500103259802112351203c441034035454684640d00208110341c1d4001d002502c0e040f4004c02000071008000000242524140902111400c0c002141c00348040e5040c49901c1d00312150392180e140b2584212805401d034180c1c01c58081c860140411801744584854114951018010b82078808812280c40c80101401c64aa40303007448504150030008443c5c800c46000045540c243d81e5803101c01501048800003100710341417020401e03820400480d051000e41c1c0c3c12081d89101c1d8910004443c54040c00c80c82c1700b05c24181940c03251208105402c04200c8244d66062044201c8a43d10460300503c480851107200c10380c134000c0302c41d05290038910000c021a221005c110002c00400075091500d1040104a4040407503043c2c1c4116402d8100002c034404030000c02e0304000140c0014030340000000b42201d541c0103480c04002c1680c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 763781564 1250 763780314 763780321
    0x52508070b070f020f03041805042303070b0105010e0a17150c18030303010b070b0711011b030b03070e150604032024180f0405010311010e190902090a08030f03 70
    0x741002000303202d910f030001840c141410042044200081211f407800c44640b0342c0003007400e200c81440c4020340310100e10002d0bc0c20006c0080d8440d240e4200417001c2c1e4050a002c400000d60354014218404500d4000b041c48800d2030400719150a004400980c81201d8031911121002e200d00c0105d00500510305030031600d88400030040150301c2440e030740140c0307070080d04203000400c9080100c2d8141d807813096101800c2c05099944010446180340c0a45004140d9030030305d40a014000c403a2a02c04045013815981440841e40b508140f60b903590b420310580d01c94406e06030020301d40c803004048a608582c80105118945550703511180600d03880c440c120315001d07410940c0364205240411b00e00f9010080740c2d4090085001104a980c014008c00710a240c0c94403155070642c11035034402400180203003004000f04103550712401c040c40304580000000f1301180d40c41c80034811034540032081202c80c4152405042c912070400703031044060340122031142d40288a5403400702d03544400703202610070401c000000039213914 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 763782814 1250 763781564 763781567
    0xb04050411041401140c03040e04060b03011e0f091b2904032009100e010801090c03022b0302011406040b1804020a05130608060601052508070b070f 65
    0x100221807110854004010801251241007900d440300305003402c1098a04807422940b0440c0e106840308211030b4040020080307980c2008801050085015110400042652005060886040c1d03140c51443c050b000c00d2503c00d10009411801c01d036400700d2030200302108a030342c0b22071101d51084c100580d000010b00c0c3c1441070700304802d809a070581c0707424031206261070008135003070a6200d1800042c1986040c45140c40b54a90300d940c011a510601070402034440c94150480106100782e409a40040d104e84400010700c0302050082c600d19a4100f804684070314516420042e41009441441070b118400c040301701160ba0441070341c03408944c0070303400214113070808402c5841402d2006180d5032080f89070a40103141d9498850030008080404185005142c48a00001c0d034003c006905c080c0e40441d03109401d804e00003e582001040360010411115581c0b180e0005540600801c01211881c080700d20004058035030031144941558041e10704549026541e4803131170b0220104903145000300701c860703079a1903006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 763784064 1250 763782814 763782821
    0x50304060f0b1c0b150d14190807020907090f050d050c0d050312010506030f0f090a0804080f0712050d0c0f0209041101080f0f011203050903010501030303090201110109021521010b040504 82
    0x125100580359204400c510004031b080040036000f030000c4100048081125004000c2d0040e98581c010114000c2c211031310702003502e6400400228001c40803803000c41c1c81c0d2070080b41d907031040d40ca000c10080440360614092091590140300b040c0c0300c1c2d11928031030306aa5204d09440ca03d03454000c070702440e42c40f90043c1c0712540c1d0041c185c0c880c50064034200200880c02d0b0002c20100c0d005804903c01c403105840d104a640d00d09a46600042c00c0203600150001d42d090300002e40c41182c210001c103507403d0359030351404070100041504015002c4d0708800980c501003071154040441d0640314400341254034040c1d401003605e1100841d0111a00900429001e640750b802c400d40a501c011051803084907481c181200344013801061007100240c401042131041050b004100307a450460001e070003003025603945d003401000781020080580c0411418100b6000f464010f000b40103429401070018108150306400c80c0b0350607031100c0010603c4030444801d50800801c042807081c000e040319500c0d00d482c0c1d81090200303c01c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 763785314 1250 763784064 763784071
    0x6111b150f0c030601180b19050301051e211b030a12030c0c0803040804090608070308030c03070c21080c04080703020630150402030601050304060f0b1c0b 68
    0x1100d40c824100110701071503a1069074494050308500d0345a4940c000140d842c12640050420803482c540d102046021008019203422000f502a038440d00c07468540a59062000f070041c15005400e85400302e10703080400d01070030355401d0043c140e20311402000c4604100d060140315107000399004422040c2e0700004142141c510800d048010300424001c69881c220b1408003068145c0c28180c643c6140300245005d00c0c81e82c00020340144626549141078505100554068001e02803601c1c40d20070040382ca60400101384e0b050700d512006043c5540c0360b102581241d80c10052160080100b10421940042c2400b201054400d038003007040e2002e06201c040203010500c00500200c1c00030820b000801c40c80d00e00242d0101220b0b01654413699414040d5100c005d402c582c3d2601014800308502000010740b42d0340101c0d440350690704c48142c20306600d641000140c0c481610443d0000d0b0090012030007107466a807150342e486090450003d080c80c80000842c00087c0e03014069a0031440e10305d80141071004c5800d02d250b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 763786564 1250 763785314 763785343
    0x18091523010f03060b190207120b01030501060806070203030c0c1011030a2715020c010212010e0601090e0a0e010f0e0a29040f030203070b010f1d070f0c06111b 70
    0x1000d800c00c12811440d00412141b81e0b101c03d040001d00d000c0b40e00902502c1c02a2001070700c05005251582004108c1c04000c0c40700303c0f1150702e000400140345c800030881d039004a43c141e000d54616220144203500d980c00681000c8030500602c040742c1ea5000740c902c90040c1e0320040750726123a00d0b0301c2c00f440d05100720b4403548403072000301e6018000d83e80c3c6504007251407190706521002001403c10307440d500000a014408811099610014003650a108202c402604849039000c0250090791240011a0f040215104103055050020f010948180040d080048800045030000608603044500c1030160303000482c401d01d0355004a20040188207500145140d01d00d00c802002401380b20007608004001300061004c2c101c100b24a0504080510038001c498105402464007001c03541c50b032221001950491060740400c1c9411242c0c596001c1c460018580304e4506616413107002d01001c0340907210160814402c450160380d8140c9401c480d906900501960700350300d24010014050790007000e14040c880314400f130 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 763787814 1250 763786564 763786571
    0x9073f03020d0c11130209030f030a200a050106171b0a0e060604030602040f1d0610080a1e0b100203030c090d06090b0403020f0c0118091523010f03 65
    0x202180d000201001d8a10342440c10b07200301411130034420201c3c080c4c800f960350700601c001041010100941c01800900c20100e041c0d695a51103501125624440c100400700458206031034007a0000d994a28003122110f804243e80d40140640d030741c1070071107160390030240d0006683c8601581644041215200003904014007505c08445100042d034184154458000d03407421400014407103495981c05c0e41c00a59211001b5500e943c0c45014944242d1014042c01c48080b48006201760745410b000382c070301c1c001c10f4068000464a00b46860458080d04001e04402000e83c55400c9061140c407815004142d00c416014001481c038885c2007000504203040203c1c108640c81401404181083e80c01110340b40c0c0011541c9000c00030b81c520701803000e81188a409460716080c0e00c204824150003107075403400c10104206030b90000c80c0c10401035401050103501c90702203400e034403000c0c800c1040a61207030700c0300200100c0b44441c0729070f21044540e020003099607403415114001c60220035543c002c10001d1100c1210706050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 763789064 1250 763787814 763787939
    0x3060b060c121b0a0b0108010b1818030c0709050105031e0d050304110d110405010503060709060c11030601181a0d030c02190f0302090a1407080907 65
    0x156500c4020103882c0a00c0c0100180003079411040e041c060002d1402c55056403100c50309401e0500c5010024801c05015508003162070525252000c3c0364940103188c9641800703a900d07440c0703400c0c240016000c10341409100811030010480020803011004018041c0701003001d40c1000245418424806c0200580402040b002d55030840d01040003c41803c4c145420b42d00c9658a060540b4030711034480c180b542065544d0180c0d014080c01500c501080c2e0001e82d801d0120713076601c1d0180750766860100e691200040d00d00200384480c510807041000e655024002d94420039114100284c00c00000382e02002204580e150900350186581c00396880c040c00c83c40d242e010f44411840071070007a045c28034000b0100850400034408564820100080c0c1c80c841815000c8826141c0e0b06080c0340c01c1d0b090000383e1151510b0000940c00c1c0d8103902405a00d01103040046400d5122042c040d41c1010003d1f02e250101e00448401181961a200c4015515070004986803040000703060201104101c184540c8400c02440340d59 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 763790314 1250 763789064 763789087
    0xc150a0903021c08030f090124060f031d0601080d0914010f02340b03060d02010513030515040312140103150b210c06130b030408040306090c03060b06 66
    0xc0001c490b01596030315100500626400c1142d100584000c01118022052051080c801520f45125510390380081081098480003007116480040700b280b205800700340300703122491049136143c07070000c1c9034140403813203030440b40d40c01a640311094a01c0030203610040c01045003032402c105907145e00c072050908100319414002c1c10b041c040100c1c10801d040c002c0c2410301c0c0c0300b0244208419039000464050104a1000e58901d004070600c0160864802d0540e451000c0b50060f0305004480c000c1c400107001b004401070340c0e40195803a420414013210051402d420002c0824003e111034041d1030380c1417600084a00d803134600505079104104a44000c240b03080482c0c0054251a8101c6041d6a001804010612400c402540103440c0da004405d401114940141c45c0c4482d18030020004589013800340c850407861001403106038000c15644a040304606082004185030000055800c80d00610020f0f02e42601e94807860107956440700215095204454100144140c9124061000b801210071038640b0344032520 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 763791564 1250 763790314 763790327
    0x1b15050c04140405280515120c0904020402070803011409010f0b1209030c1902090f0c030408221806090e10150312020706030e06010b0a0c060b04020c0c150a 69
    0x1c9900490303441003c1500801d084030328165080000100701405d80e194104e0401a01c015147d1810f10700e641a01c000c0366142c0092300c0382104c15100c004041c2000414204500500050000c1c2e03089139007000b0310000328451000860103044100709004905102e00184201c5d03850581c00407051f810000002d00c411042030044807440c80d03d0107034070185074803004041800d610a440110b107251080394045501c81d120102c56556882c02112a440310303a03680036642d05c40d03000445003418031900c1000080c0015039650b01400d65030441c2d64505608548035404080799a0081d08005222001055188a840030038003546001e050205018011002100340143e038494543c03c00c606c19a4030351a00c00100b06022080c00011500b25504001d00074400ca8069240c1ea00c5016010000c0d082004009001e03100085090490b00342c100d10a261014a10301101c07408000041180c080703446080391106035803140082c0542c00d403098080c0c8459103442c403c0003151202e42050f40a9040c081c03241021040c1c1059 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 763792814 1250 763791564 763791599
    0x60a02130905040c05062d310b1305040f0c02030a03020711150912010b010203070204020d0e120409140609010b16080d2007020915011b15050c04 64
    0xa07004240b0f612140380800080740c0a030807444d0800804192034091010107403080002e800c03002c4600d016010084800700603486002c045001441c40401500d60740340d0011070b82c0c090000741e8030085d0784903500d900000c992644000600c1524090f580d03002d216515240c03084060b110725458080080340700484000e5120300607040d141c400c5c15404035a01040c00024003002080e1040107201c4030318150720400300c0e0540d07004156524007400c2c1500003844102d02c14130940d07400d40c805030010b5050020a034208000b07540000c9a070078400303454500c2c0c4054003200300b1085100d0480d00030416100c5007403120040860b6071800c1d07096072040130401802110b440307200754181501c0c400c0311085d944031001c05c90f4513034410660038020a8040e0001d004c0c84031600c1c80e40b0840500c990700c456048410340301910f0004078010791001a5021a10700042181c0801c4101b9013003645c030040c140421201e02e80c0c44d01e19104040140b095803206038035000500c11804134403075035a209402c0c000d07150900d800c010321b02e80c0850f081e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 763794064 1250 763792814 763792829
    0xe07021213030b16031d030910091212021213091a0901030c0312050f0910020c060c010f061502120a030609050c0d110c0a060902060f070c08060a0213 66
    0xa075003062420040035010186030442004000d504100d035441c07105125024032800002d160101e5946895804201e410708100114000c2d0b06003070f031010804c00f0680c0c2d5a003404090010041c000a600b02c0301c200c6050b0002e01840705800f4400d010b19020742003118154156690000c1040030601c200b21201210043c0c50000000140e5000b50480210340080d40c0802180e0181c00d0400020030091024282d1003900d101c0c015120201013080f80c160b555010380107c41162000a200640b028180360b154007032415241d104441c3c20826040209410b94480d0106803a60b03511420703001c0368108a0300811000300700550b40b010480140c040c009486074401c041c003041c42c0c200020074101c098840d0b0000d80107802038800c100702c2410302040d08445030780000102104035007080603c8107545c3c0399606460000380c00703c01410030341c11182c0e20b1800504821380f049900480c144a42e6034680b400c40b0203440c88502c9000008401410320410b1490144000c1c00549000e0041040da04084c460100c070a04940c0300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 763795314 1250 763794064 763794067
    0x903031e06031018030906050a120b032b17060901030212010b1905010e030109080d1104030b10030b133f05041d01080303011214030309010b0a0e070212 67
    0x100d0340001d00f0038100321210103100d401c2c03500e4000e6105a402c51600060320030340b94070481613178401040d41d0301c0c000c0034111808941c20a00c0c2840c50b00c59504a4044200010f0942d076103102014010041c2c400000414240d40081c4507800102c1a00f00d910007003442a0600e00c4181c900e0110f000443d06034050000031b0042d07035070784000c040d084800d40100c03030140310050005400594100010140f480c41d48a20740c0018030301860381c029400c0c107104921000c0d420000c1c0510f01048020b0f510003400805003525610801084000041289004081d019510781d5462400c005d10f14205500c0c000c0d00a40b84031403d50f01010b400e000036140b1540b0400445440da04291194842d8403403146040c440f944c401d6415020514528600354008000c009844280d052180b0605c0803102644024501340121002d6a004000503c02450301040300320240d40705110b4450105c0400c000ea60840e0001e584c18000381c0e445000c40580c918050741c101028010501d200e441600e0603903002503580c0e0801440407101c000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 763796564 1250 763795314 763795321
    0x3050304060f020a05011e1410091d031602040c02032b0b0909010e070902070f151e020409050114030c090403020f0f031305010219030f0e150901080903031e 69
    0x34088180001c2e0400f00070401260090f5140345046201520b1211a91619023070f42421038075210844d0103152042045401d4a092045440c01000f60440b51125400420b900c4d00352510100000d12a8031076082d01d0805059062040c44191201000000252341007072183d41018501ea01c025035031403180c1c80005000b200e81e035018000400b0000d0149821103034100801c000e61005401c440451141c44048807101c0e81d88504000490081030710003090090000000000f0603050307600740200101c2c0c0800020042811710b100100000b03d0340c0342440240c0c004c40c040010000702c4c400d99004000445a0700e0500da40c40c00065211101a11400c3c440c0e40403070081024548204120701c804640c3c03c080300c18031548050029070765044200182c0c00c1c0001d04034081119440841d8050b40030b41c50340101d881c0f800c0960740a40340700b0151852641000401060b005071540c2c1c2c070b400d041442c528450500d50b90300002000502c0d401008000394503540c0704106100d4001040402c0c480500285207990500b5103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 763797814 1250 763796564 763796567
    0x1805060402070f050102030f1b040b130504021909210f030c0501290d020a06050c01020c01061d06040902060f0d0906090c060809070608011703120c03071803050304060f 74
    0x40d030340c014100703a20f20f10010041120560080d40030b280120350030b00711562024000011480304d400b01412420080c4400c0158072621005846403648190203d400c00703071a4400325080760032040002a46280140f5aa50340383e4100072044050f00700c0c46a00360300e5158100c0b010b01c0400001000515507140c007072801c010f06214407524400c46034080024460305840020440829144148056002e440c00e09003c80914040d150700101680c00b03483c6015031441c1c06410347e11608160300d502c49a540800080c2c80401d000e00c5210080d101490710326410340309011150321029001003450303010300c0c44d05000b2409a45e0b080140c917041120030004664a100a0039060082d081000b402089141003000c16001c11444110607002e40e09a5a158001c0e595801602640c4840b44e1103000d0208010a006001107003590300300c0090320007064216840d200f41c240e10006c82c07a00072141100c0342070f804001c0c0b040361a4030618200c002a0621000b40c100d5045840d0540c072031250348205010b0028900d02d044405 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 763799064 1250 763797814 763797817
    0x501020c0d140607080a11041d130524071d0402030601050904050c030105030f0a0f03180e040302011a0604031a0a060305070608041e0f121101020a0c1b1805060402 72
    0x600300800352851810020304c0070b840f044096501d1071040c2c4c2443d003890b10b043d15000c04c0e1012914130b40032000302032003c1c0074030ba4840030003d40702003030000c50000300e440070400400001506001d000c01000010154170702d013a83c010000b5120b0000c0150001c0700c60345514010080c1d4400c03250440340107a5030f40326000142d03814802d0ba0fa42d180c0260405007000081c561490146048032410f0b000d680d103120f4000d440742d03103402c030a01000b040ba00240300480d0210303102d0095117032901e510448100c0311903195280e01c5a0403104440032030060307440b084080d910b050b030845090394051041e1502030806045650310b0820401c0c2d0f00150b00c440300031100041300d900700c6410002c02140c101c0c043d50416512000000c01c100c0d405c6a0903610949800e43c10686010140d000c280082d400881002480301c445d61101d00541d604c4900078104a044036100060f80001e00c004c081082c0691507203d900c0240c0d00c0d2000c86a00420614403580340c0d04101008010741c502642e0025000041001038290395200004000703 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 763800314 1250 763799064 763799093
    0xb03070807090b030607080f07050f12061503060303250c03150b01090e0106030e0f300a050405060a1404060306030308060a03030203040504020f0424180501020c0d 72
    0x511800100050500000c60031809907181c0450070b015510b01c41d41032544e650019149240000c80420000e05204000070b60140c1201191810f6464110f1002c160f85888d040781d0b1714a4081c0c14a0020300c0a540b030501d03c6080c000d02c2c3e001d6068107601e0f2801c002500d90050810764001801402000203012030700b861203061441c2d01c208444203003038807420b054040030600011080010b2420788000300d1507005034400021247c0750001002e60340c0c2414001c41c040e0007a007641c14000d00c248141070350a00c8042c0404500f443d058282001d0b1a00110605803400780042c6d0103280c48501048810400d40c0d0240448058800548440e6540c18840385c00701c400c6203480203001c200003030200d4007040c8070707034140c1200046900070340e0340100076159042001003034441440000c1c0542d004000c06c100506183e005440c50b41c200d0403a160500e03648070a945011507050f90752410914150340b508000b10b40210000007c044001c078141e500381d040c10b0007c1d5848518000342031140d505c200c8500c0400074030b800801c51 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 763801564 1250 763800314 763800319
    0x30c030311061602121b0322090608030406030b0d0204050a0f0f1116020d12020c01080a15090506011b05030406031404030f0c0804260d0201090302190c12050a1b0e0402130b 76
    0x135107451845481e1441d0109a008050000310200300080880c09c034000d100907254204003551810740f4101d000c0d0000d050051919801c280144d80501c050703a00c9104140c805c046903400810246405071800085a254842c20100035241c5203108a8006109042d503a060411074180d41c800c88007400001c5d1854400203009000d101012880007a10742c2c042191390b203115084e242c040791515800344a8090721010119003d44c1d9000060070448080c036904080d410000604103ca00d0091080c844000b04070200d4003500d041d4800102000b1407503040c4151880d420311540140d20a0400b5a001010000d40300c40b14010840074200c21428402c03244104c900904000450078207802c004c0c04201c03101c01c01d210201100c0d020760342128036114010300845507245d9240d40980041e01e0718802e0090848130902041c0e40ba40b0021304089400c1000d10b90280c64640640c0091900c41c055140078942d00e07458401045500e02012030400450181145258120b6411101502088002d90307649000300306103040365a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 763802814 1250 763801564 763801567
    0x3140d110706020d110c10050703020903100b190302060a0507060b0d03030c02101a090c190914030c103c031a01020303041704030c030311061602121b03 67
    0x1400c2084035070044c00c0760390708100180030301082074007a9a0310340640342c19000d01e50491202c40c0ca00320003035802242d001d140383c20b0050824020328042841e04d072a0600700a4070583d206a220034519241501204107188400306e0342c0682d04640c0440d0250003103110704001c0c0100401d03070504012550b0800301901a01400c5400304500d1420000d01170450724802c100940100000240340d20520300034411030210f52800880c900b10b00e4030a00a25a00c010040201c04a0a03c80318125000e1004814001c5601d6a40d03080750134140508220b840e86210f140764460b602580104025480c1c1d031640310310307007100b9003054210b140b0b0f01030318103500e240010072550b880f0711020b00c0d407d210b080602d1102c80c441090356003080300c86943d06c500741e03440040344610707070160713100f8000500002c0441e81800215581192628101591390340d42d9401862150800c40108400c55406074025104020b410361107600708886d07814200802c1c001a4654580324940b02402c0400641c2400d40c484001038007198040300022603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 763804064 1250 763802814 763802827
    0x909090b040209070e0604150e060d0203190e0d030b130507110c030c1c03050c030406030c111f050c040302030a1101030b090705030112030e0405131b0303140d11 71
    0x1a84040c0100d4040b031007103c82002041e5120701c9a0120120350b90007500403172420342890801c444038034201103000100082982000741684990000e0524150600005030300d905040c866806481c0241214420192400041359a0001c00003910315a40d00c1c01c0c01c1c0041c203071003100080340c1000038a00c480000caa04000c20301962952196102c20b401c078111050302d4070400c400f8201500c0340d02e24513200f90f01042002c00905030340203643c1023600c40f40c42400c041c4d24002c410040c080c2550859400800402d82e117130004100c0c0f541002d201459030340e00704041c1088809a02508400389000300381c0e114001d80d86c030001941c0343d00f52000c540255030002c1c03c0300c0d103442c603d01d004900c07041e000d50343c54002820060014050b043c0f0307119450049165803240c2e42549c0c00c1440030103110381e2b008002d508011800d541000c240d242c40c41514041d150840c141c0f180c000c0305080c5000c120b400d00c201c49880070040c80081020039400105650f101008002d00d681e218a103000000c0900300b203412802c84210009642c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 763805314 1250 763804064 763804073
    0x1f020d060803160c091103041205072003151e060102101a1509010903081c05010b03091e07140609030106060c050f0303191d1e060c030402010e010f090909 68
    0x54401441200c40b85007031503c86044005403945080814040c440c2800402d0009585181072009c200091503da070411026445030708100c200c00c0341011001c10701051610701070506001342c010b010951440300d0014204140c00305c01081ca002007250f5a003072881d002ca0120b078030074000d11900d945070700310501c0764611020445890707041c0c0e00b0072039100c0c0d001a1882c0104031840f1096440907a030507100d41ca0500d140da1542203050388809007440980941c03c034a2442d000341486803d0107400c603c04041d84a1a16824aa1408500120701c140201c0c09080036868194006001410798200c0200101140060400b10321280110103096926508020001c14020313880300100c1c030b8850107101251107000880c0b80350358491005642a07000c00c87e03104031440c0c88031078a4000070180503070340070010b00c00807042440034100300030401340c0690b0750311981210202d030300200095034000c0201d058440ca5414290300181805c400e24040606010060b090b007100e440c0035000031002400b01401c10b01508466151 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 763806564 1250 763805314 763805347
    0x507030206042d1d0a2a080708090706140706050c030618073c0f0f02061905191806110306010903020f030c0607080d0e1f020d060803 59
    0x140904450b10301c582442c0c8800c0450030089816003c00180c0d8461040c1350700c0b070f204400504008070700f6151461401d08188440070310480514000134001d4041684900400c50003002d400b1f00104911281844961030022400604072505810040c10481600070307150100e001f02103011b40502d250908028a001d909401107102d00c2c3c003126980843c2d03000203035810b43c40d5015200000064030440041c440340325410b03880c0b88022100c3c0300580410107602c0d04280380c40354242c440030000c2c2031a0800701c0300c0754101c0740460b10398800f030000d89140e1410301d00c0610103803000c1d071080401c90744603c0841c20848600044070103039007010006001517002d01807103581d0810303030362021103039070345000d8107a660880c110382500d001d010705075101560f131481c603020003107480c0c12005280c6d8035004503443d00e0116512003000f40162445901aa5182d00400c0140750486108603e07070051608484000080c00f41c1f109291140080d40050042c0c6505002003070000a00701030b000b80c05944000201c0c2200e0703801c48003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 763807814 1250 763806564 763806599
    0xf07020609070605030a090303090b0a0b010306050f01080c09010c02090708070f080621010f090f060c0207081f090c030303090b06040e150406020f1b010506030a0c030b04050703020604 81
    0x202124a1521242115580d841041c030039000055070a00100342e0002035070f04442c14071402480c000c9a0751030641c4a048043c107041e10307420045942c9504c1680e10b941c05000e0880100401c41e5100100415403001a000060003800040050310004401c9040c3c0c0c059000e002c1050307005004540c21780742c15240070700401c4003503c0f0080401c442c0c601080b4a10311601102d40b1407080a003590010f012070541e1420150191642c20725255240c0c490717004040c84a10030040500c0c0651020400b03100141400402c4990003641081150406a4148509400045d8190300400070400440c10024901d0040d0010404207000a140d445404400002e1503410740014040c01e009079010000341d200c020800084030b054416540c81508200c0c060781d41007501e0216103078414000e00000d4902074404a9184040d80903080300c504500c0d040001d0907030038100f40b01f03091344800305900404c0d240071903443e0303103004101c80d2000801c4802e4200004081000501c0b49000071070740502205c0c3c4503902c82c503000d244220f291 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 763809064 1250 763807814 763807817
    0x10211b0516084b0309011b090512011505060c010b030d120b120d0c1a01030c0602070b0421300e1804080a0c05030c0a02040c1809020a020a0602030f07 66
    0x1041a44024028001804801203034083c0d520314000241d000c10b840380c2005046800da03560b90880c0e0b0f800c04010101403080d140013551558043c0c0e00304020400c0b180e6801c051400c8581c90002804403613900d0b2030700c0c03600303456045514540703ca40c00b207402405084600c0000341c1500896180000198011403540040c007600207080c41016140c40c24407401c0c3c80781064901d081e910890180541500070380c0d80620050080c0c1e001800c1002040310050f98200a900894030b0001c00b040030040c07030354184a250b000d04001c141142c905445e040030304c483c1400a100204428452010b02c00030082d0842507500c08045110700742c40c080b161140d2042070f4501c80e001d090007107420700001003030741d10b00b00e030170040302844100340810715840d6600e54016541088a00d14203000002c007590300070910820142c11007241e1000189080c0c0010302c144010b444416440d0001d120600202c4881c4000ba61000000e9945e016070060711340020780d86c22071401c0c81d40140980200e00c00414481c10103c00c4406922400c1203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 763810314 1250 763809064 763809127
    0x619091a0310030b09010e0610030b010803030702030702040b04020d0c030504021c03120b040b0a080303070201060b0f09010c170705071d07020a030804020f10211b051608 75
    0x1403550394034040c40211080c00200410a90a20000b5884088150419211400041d02e04201c400881c070305241503d6001d40c00f00c0040d0104204840d00b90381c14090000c0101070b44c21420001c0f00a9609e001d01500280b0407900e074505070406441c2da6041d5202125101c0c0c0502801c02c503184083c00030401510140c0c0201010908285214134400110039082d6040e40c555840d40d5130390421200400003032007503603401500c52507d600c031a5200c1c4440009000c0340000340d0f50b60300340804040c1c2190f4099026080303e4900b80302c59441060b2900582e2070b401804c1c24a00844c00702850a441c440381e10096007440114049080810f0080000c1e46109071050214540e03280c0024810070300c9403400403280c035401a40081c0340c41001900c206c107010b4005101030400d4203114009030008450040796002c01000910005107600d00541e030b00d82d0400e4141640804018015540e0302d001c0085000f107030514144800024076605422174414911403098021140c00c6d125207a2011465902e03400c4051600b60a0b02d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 763811564 1250 763810314 763810349
    0xc121b0d060e091615050309010e060403020f06070c02010806091e01140405010b090d151b0c030f09050109090e0a05030711090f010e0106140d06170d170a0902061909 73
    0x4c5000c2c010003a1044900034811962102404860035030000f00b45005039500c400000c1c00301c0104001ea50b0140b0310a4002d000409500b01d0710720f00c1c5c80320041028040024901394040541d800a2045400c04010b0301c00c0451655581905640c14400f0541c150f03c0d0a88200001920075802c2ca48082400045509128070b03640c802c03252030180110358249500414500132400015503021004183c0900007402245c200d45c01000300031312500441d407031000f01d0700c840528810950b000424460061160030503804040c02e141c00200003400c28080c45034030b15621015580d0043e070400030010041d5202041b240d45400515200340304100c22208180201e45400224100187e80b1300001d069400180c0301c1c0d095070f0320b44a4112001003051103048170b080b070704100c011040700280c09002d001d09955990748901072000d4182918200c04180c03130b8000c0000505410103000c0101341d010360021002080400e509001d030001504c54400c40c0f01c0d0240284200d400303054070035040380040d821a000c80807030850002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 763812814 1250 763811564 763811593
    0x207110a030b090115141c0f0f0204050a02070314031b0409020703110703260409050405010b031b0105180f0909070503101a1009080a0503070501050c121b0d060e09 72
    0x4515014214507440c2a50741072040d070520640300310255220b1f112885042100c5d031a08003002c0c652060554094140c1014002541040c1c000e0b503412520480085180000c1924020110281d95040c02c2c2e13440700000118040300c200e441507403a07440340c042c08140c0d503582c0d074010070f4025404540200e01103038450f6641c0070038141c0880d4150840381c10102d0700f01c20500003501d5084680c51140740c40003850060001051020071413080d544202d11407800000e140c4402d90416140c4070004a440c00c03002c54461080c0b030310303076400700c2526450a92940b00311f1001501800158401c80111401c40c1c101ca2481c00300054660002480411030b038050f400c1d03c04500a0751800d906445d10141000d4000b240a079140e06181022100c8510783c0c0b04600d00300007100e072520004c908081e07c20300259407551010036a841480310a02ca002e070041040041b2a18012151120038440f400081a4000c0e0ba00c0b090004200000354004031421140410f008206980d1640d600c810081f40a5980c00e0313546c800c2180c0c004960 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 763814064 1250 763812814 763812851
    0x602070b07080c1c120f0b060f030c0d0207030804030f02030406050f0c0c060a050702010215090c060a021c410c190b010314070f0302040207110a030b0901 68
    0x1249125400ca180022680b51481181d008500001e03d0f4880c01280142c6102c081c90600d003810300d07a649611310001d407600e040f010b4030311100d150083c2d02d1800140e0661507850300211140c046828413100d1301c0780d460b0005a1401c1c01210030740c1004500014170701080681c0180d0440c8620b11030b842e00c40040008078030407a92400345000701d802140381081160106060b0a000e0101e09440e40b00f181c00781c0040b80c02060094102281c0b44012881c04100782c0c0440d81c0522500d5441901c0c50000010b174030301414042e90394140c035804c00780070300000510310a0030f0f4400d100900ca209150b1030712a81e4103c420074010020400749002200e012500701100a4808980e60342820714646e20800904400e41d0384c000c09003550040c44c1441652045050780d0795450420741c0102e2401d4000c00c100d112a42c5103041c40300c0c0c500410000700910740c1045400707000108130401034105072501034400585401c2e551034000b1000c140080e609030300150000001040140c56811503101d003003000c00030b0014002101d072a1025 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 763815314 1250 763814064 763814069
    0x30203010303020c0d0f050d020106060e040b03030a0f0c0602120a0b09090a0605091f0501052110020a051c1a040e1c0309080a50040503030a02010b0a060207 69
    0x68120f1311403404203141891050884500400e04000d071039810303503078080ca030807a100e1604025035101c642c108a5507400102d6000380310701c01e840c203018014101002944078414050f08800f800054404a00e40342d118007651420941d10800840d174030512001c4000c04910704860f801100c42c108a40c140b41c90611000460040240c0380042c03890b44c0c10356035600c0261034010030480b864442c034aa070041d6a9255954001d02d000e01820018095041009019402c1500c0c10414082c07640c21f4207000c500340000803184a0f0038403c03800161a0109104101c8092160402e01450190101d0405030400301d1a1f2103120000301040c01c90403031051600501064641010200d404d541181d010b02c03a5481401302004c200d54074a10b0005143c8015607100e807030710382003259032000017001c1121883c607a0241c3c0381181240b001114107459140000850200c8400314210400e00982c0c0201c0341d4080f240803c41990003804005056a84940d81250001e00078011b40d006544900d4002e07000203060360000c1a071005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 763816564 1250 763815314 763815317
    0x140112030c0b150d061a06090604090e0715020d030506010e030706080c160506160801150f11070801020d0501050607030816050702030106180c18050f180406050f07030203010303 78
    0x75000c9042d00d519140309001489a41560100103e0074059544c0d038504c0000280300f4000042c40345445281e6440002c0500603031409044200400c41240c0d407130340d05660441e1520f06000c40c1440d81c50380c2c13880c1081c10541c40300c0076082421001345200764000c101c00a866940c1e51381002103036104401103c608146c00401c2d50542c214140500a1711300c2007080b1a4044c103c84041403901070072583c01041d1400c0484144d515400c10350a100e1a5440c0050200d584184c1e860b0541d80355060615a4202660202010084c03002c81e0900d18a00c07400352055954620081003501c001940c1d50195034040d50100c0141d08101d45000004511031900c403040d0b07203406404d50b82c0cbe880c440d603440031103082d08815a82c100d01403003003c2c4910070040e0343c24000c48014000c55141500d19141e100040401d9490b81d091303003000d00c07103003403038600340326a00000c4841101d50454410083c0c0d18041c0100300c10403042010341c1c8100c1220000c01c0184880390b00028024114180f061a4941d501c003002c804901003804000c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 763817814 1250 763816564 763816577
    0x1005060a05060901091a0705060906070503070e1c030306080708030f0702010f23040510030b0d0215040819121706151b0c01030608150112050c0a030614011203 70
    0x2075030502102414006406040142415807210a16840d1410325002c840101900246100c20440c0504c000c980100c02e260042906042c50b07400a801408000e00240400c890039000205a0303441005a2801080594440045201c103050081c06400140038060843c442c8000c0012020700020072102610038840c070b2507041000c664011103001c2c60710500e0030204945400c03920605005507480101111400b0a020794643c0351a00b4400f11411650301320080c1482d002c1300303940c5600d404148545080d411075640d5002c10340326504c11024095500038520520035005000c040350f4095802258950041c03000302d020b011480011181d0000784071003000c0300c01070783e03000c64524107140e80942d03040c55140d80050704201040104400c0402031802d45081030380728a8914400c1d5170144120b1000c0d0490b80041c284070009400c08056040d418455141c200f0018a11142400428401002d4908c00140402a22940d0303081c184058590305008034080c003030403400005c0402d5071000380e0b0b040741c0c0d0544646 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 763819064 1250 763817814 763817819
    0x20d021f02010605030d0e0105122a2109031606020c0a0f021503160c060204030602030903030402010801080f0d0e03070509040c09053607090f0204030b010b041d0a180c03051005060a 80
    0x1940c0302b4001e001d800f40807144000101185400c0c04c1021f82500a42404544a0311980704050604d42f40e9545041400c0f0fa440520201003404412100034441300c0c403129240c601285801d500a226004040845019640810040060f03030503202c08040d0089a010003444034204201113540b00c20b0394003a1200385c02e01100e40d60705000e07400c429041402a5401401c3c165251200c906a910465845c0a550800401c0004642c0c002c4c0c00d10b03000d850020000c0c4074940107455260b0369016022303103c1052040013003111000c0c0e9420841c140143c0006805d4518504091920f6442d0350254050b0140312401c0c80006211034042c8103540000d8225841000380e51506400341c41032001821000000c00d000e5034002140b8524140640110726912510060381e591642c1001000d241042c2c2000210b01001c01c010415191510f00c131040010340501042e0b259212421004010300c04200003000611010410a0500007548c0d510400c503402078080d07403510a0310040110442c4ca080740c503280d0100003103405 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 763820314 1250 763819064 763819087
    0x20c06010801052e08010c030605100f080c090a260607030b0901030308040f0c0e070908120a03020906070c0b07020a0801050f010e0a11040306021801050f0304020d021f02010605030d0e0105 83
    0x6600c00c0707805810001c13100c030746588140d400d40f54800d6060020a803a52401c2226003840d52140203403201502e0300000780130b0042001090170002800a5201e00000f04103d000e90b40c904c2500c00040504040040d0b840c60306403603e10b122032502400b50b80b640981c1d4005415503000303010316540004002d002445c141c0c00d41c1d90540c2c15040140c01a00d9000c103000f0400c00203050050020094100c852002c801031500e0340e0024004c40d12504040826004800ca41b0315030f0034080c040ea100c0302c00904001d40c81d04840e0000c20540d025202c0003138911034030814001810350f400c0d001041418000d0380e0100d601c580391030b202402c1e40e1082d00c07201d07040449140100010648203040982190105001003069007a400c01e00005810035002522140d0740003440703c51002c01403021140480c802c0c00c0242c10840c503052400310074000184040e000e0710007030f821041190713500c40400c4130b1070341d8442da00800340f414414024000c1540d4010b003070080c81200d000780c00182c010050000c418005946003480d2410f207601 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 763821564 1250 763820314 763820371
    0x60c050c22050f09071e0504022506020918010b1605011d0c041a01020304030611040b0a081501030b0d03180f170705010801031205090102150109020c0601080105 71
    0x228a0003441c580d003006030315000d1036000f01d0302446211014100312014a00f8212940e12603480005420b4011040f4082030803500b0032520704036030040c0c80304145c80d4000b0350f8110759415071840d1140c42c1d20200070400903501038072800b48266601d0301540114003400075402002e02030400d0621040c02852203148009502c3c00400d40325000120f81403400050746110b14000f52401080c80e00301050082003400e0510504107281c0d400912101e040e1039160020b51284528040a00480c0c0c440c0004e8500d0075808046500070241c4d030034840d98660100e14010000031043d201c1b05041c4250805082c09588a0f02030152030020080c414101c00c28280d13000d99078100403c0e100102c0c080701010024620a03a0700b000070050252032454030108105449a80c2452030300d07000941400400e500502c0402d6102680382e0f030b4502d503400c150390b030f0b40f80800041c5d02c1d02800e07412030052a4402c40010071040c056801510111013840c0459030140d0700c038001c450a075481180e40c454181c7c1c000c440107010401102 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 763822814 1250 763821564 763821589
    0x60f0a0c050913110409060e090303060d0803070c080f180a0303020613021f0509010f08010305191103010915110f0702060906071415090d1e0e04020d060906060c050c 73
    0xa0008101100b44070310003464000d86c2c0300055541e690308003000002c41d080c1c0b01c180d1220100b000b5501d54505a00040d01c40c155013a03003d0310269021000810940c0900000890305070080441c03034a400c100c2d0174040803944604100350120450350b0b8007036034034113240c8460700980c0d5158000c2c0c002a0703039500c10030203040c0c0c03400303020382e03101349040c00345005039801c00d51800c0d07030410540d1003a0303075503410500140c5100d18940c244410404007070010008104d0201300301e001c0900400c011006910305041182d80c41d8440c2d00491350651030725010004001c910484502c4a4031210418001117813550801d0b4014007641c4c0b2503020a1004002810061801c1c8000709442da030700a1040e030910403076498036001c40c80c0420b000605580302d8000303002400d582c918821380c08500302004002d45022641c0007000f460b2240030240a6a0f015500601004d02591005600c04409401191245070703c01415001e05200d1080d407041529007400070404902c548848015290050003d150a05421080c85111031011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 763824064 1250 763822814 763822849
    0xd05060f06190807050411040b1801050c19030207090228020f1005040b161b060b060f070b06040c0f0e1306170601090b13091b0305060f0a0c0509 64
    0x121602c1c00c082c0402d0018000340441c2c03030040c502142031409200856441c2e030010360103407900b07103c10410544800c0c00c41d4030120b013052100200c5450040142c401d8010030310711541d40e01900858010b0034041e0781e0b040e040140a982154900782c2e4079842d2270200e20481c84034510200b0b443c84402003000f034500000110491510441e00c0008254014500b401c0150a9069429840703000340402e100d0000c60140d00409446144c000c9400c20b2240074000704408810003190324280c880d074070706000e40d580c000e8021344009012141d031401850410209a848100100c601c0518030004c644c0c6403c1c00e00c1011034900d1170340c440c10705a408121094981d51200d07464a40d0065049000090074041070084400034002038484000010f103882e111420600141c02007520585005070718000b03640c50000c000300803410500009505407507800c100480b44182810712080b0302c8010000404c2003400180c440c824021310260303e0305526079904007000d40e510705c0c1d0b85100280041c02041c010346400700c00c191034440344 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 763825314 1250 763824064 763824079
    0x110307200f0607110c0f01090608090708060702031c0905070b1b160e06190b090a0b070311060f040c09240f1d1027020c0604030e0d05060f06 62
    0x8480c1a02d0300b081143d01c180080c0c021059000f9a00040101000565040f83c50149051340d5500081002285200752410000b180c40404d110310300501c0f4440182070b10380d09a40701898150006903803544110350b0003117640240012038190201070f115002d450307648840a862860b03d4005d500009400241e0380c1c0000c000040310113050204100901c0c0480f44050000f5003480b860401040c030f116800601480c000c1c00408800400740d03400150b05000d48005480090301c9a2035040810b807014100c0d0400c00724010000f4951007411381201403007024242c4007040b500d0540e03c074504580d0030802610700070094050f10307e05215218594003c6001c0310020190000300f00108030420301a00e031140e010098012020300203000c0c1d440b280c00320301c0202820312103070442c81c00c0135001400c020752184140b180c0380e0000480240001076040a003c21541c3d004415034031940c161503002d4640d80c01359803c5000c0703080301e15402c4c0d1508140b54003610f265040b03c09440c090340c80c200e01d5100e444009048a6000a1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 763826564 1250 763825314 763825333
    0x1106040f0b043923190b0f03010801061a190c0827030a0206220509040606150e06031305030921060709080a111512060411030720 57
    0x1c0403060001d4031907010041200460605007449001d050310381044d250361300c001000480640301240c4000740d115060728400aa00c0a03807003010200d000e07a80141d0940200010301e40000b0308400040c1d4141c41280c0000c0141c6c41ea01c0302030101c0310b4180000800014024001032020140c1d8094800c0388414508100b02804000d6072000d030aa0310070302e10406116a03030400d00340d07481c201c3c024fc0350a42100350000c0c80b82070804d03000141d00b4000e1410540242034001d10030b140e462108000709009060180c10018a03051610704500580312034015841e01660340c1981a040c1c9104945101e108000a032090386141c6030300034503030195442108142e586202c01c101d504069110546c1c0e410540ea24501200000a82c2c880300604103000906100204002208180061035000c01c0382d200c595801181c010071507076980d02090010790a200d15105c215408104980e0080c4214011441420304075010801e8050116003900c540c001600c03480d0009000c480070b24201c0100c3d00d041c0a000c035254080b540e11700c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 763827814 1250 763826564 763826603
    0x3030815040501080f0708071d041407290f0403060f1b0c02030606120d0516150e0d0c08090d02150c010b120f03030c0a03090f0b01061106040f0b04 65
    0x181c082c0e0003011580d0045e140c20500340014806103019110000c0078200700d514047ca413500400b41c5000c01ca00710040c078000701c0d04004500c040e041c08101c2201c04c0d18000f0780d40e00310071051000140c2d03503880711035520500c896075003405108449002d00310b9082c5904003030a42d140c80004050f00700940740c0c0c4a65415040b031006c43c51444007014a0943e41c0d031003242202c1c40c81410b080507400750600d8090f440c0121500310b11100410181252074491034010786a2110101942c1c01040008000c3c0a9400c3d01c83c44204002d1150000c50840101e0801c83e074070021020b104a614030032106010380545003d10480301d042ca05111031060741800104950b50181001c050602e0a03030100c421400300d6913460083d0f1182d4280401d03148030034185480075082004269a07180d840b8800203011203007a140002b64400720b50700983c49205800d03041407440042ea006072034017103217000d070a00405c000308418140007200d0303000008041e845280e00212603d043c121030358039200400c0001d40104d6004541058009800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 763829064 1250 763827814 763827821
    0x130515010e060a080109081b070b040602070609050306061e06090616060501060c0507030609020d05010903020c122803030e19060b04051501120e16090c080103020a0303081504 77
    0x7001c0700107684040b81049400c00c049141a588030503040c2c0d04011441c4003054041c0183c8040c031110384203405d8554400803005c0d003000e5483d000b0050101c00400c0110322240c1c006a48404d548441d120030404036100d00400d9602c000850b0034030307030001070303800008a020001719500c01200809403000c1e0800c0980400a69240c1001030212444583e0980d0740d014002c8a002e000d0052443c0d0030315101c84812504d0366515041d0f1404081c0c500350300d840e01074045481d604040c1907210340150081010b45107902d8000d464101d4007402e58402c3c8400380c0040f207145000725140d9070564100d80d1031507652007400700300e2440c081600310a07000c3c19511080c0c80a1948148950800244810a10341e54810180b03002c00840350741c104064001d5251a0401c551407c240311039140d000713000d0802e00010031014284d000600030754000c001e280e0060a0303c1c034224600c50082e07501650b040000502c0b10610220089a04010034800a5840040c001c800c0010134010410183c00440c022507058a403158840481c068 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 763830314 1250 763829064 763829069
    0xc0d08070611270f0a0f14030709050f061e010512180106081f05060603040b0a090c170708210708070f0c03031715220c18140913051501 60
    0x100d0310b50386843c0b00601c1c00c0c00841040c0d04003101c1580030b89042c43c0841e8162506030086032a180294040e0101658040006030000d01b040389050120f03140124407604074000c04c4d143e0034054049103802c071030380c030321414004100c80174181e441d28100050051030780c101f41c1000d010840e00000c1c401211030840c0c003e004000107441c00310000c062005001040d007038003607172071a50301c03508501d000d080c0005075032040222500301c0d401200c20441500d43c81d1120009040319400106144007490340001c7c118544109080041416429101e0302940c41608039200d0710007040038103580107500b1400580c40010b0b0058031403580141c092509080b480d60b130b1034440041d02e220036105100103503002c00c00c0540c01082d2103884100a414001c80303040a5500303480704160620618400c01d1000003115000c040807045103ca00165070040c008010710201c040d08a55030780c144803007485821280801d0034050f03081d10049458002d0001d0a040d6214080f0202d0300e1080c0608aa15008040304001405070203c2060701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 763831564 1250 763830314 763830367
    0xe010e1c050a060c022503030f030f0501150e09061309080d0f02120901150501030c140d020d0e06090a0201050f0c0d0f020d020c031b04020405120c030c0d08070611 72
    0x1404c60010701c019141c03100c4200c610000e600500d0918a02c04109400e500c105c95247c01c0c0146010007440c0700341c0c0903048000c00b148842e840e12000181f0946003010011240703003c2d40700e4840c452000d00c10701107812805c495940d0085c9103105440d070f000782d181d40a03542e898042c0c0c4c0540d00700f01d4239640f00740994a0b141d0006481c02d40125440c1406504020050f81014400c0c0c0200140c0c40d0418009100385014400d070341c107046d9145c10301c003441030045c2c640d03814040304035101a584403690150326009410200300b142c012480e0902c15085d0240c0080d225000d005854001c0001d9411503004403901d601010b0092100d40f41032001c0303c041c01c0c040124204d85501c0b43c40d500070b10272850703d0080c03911030803200c11801c41d44610000b61075a240840c002d0603106180401d4012120000f010a000e44180e0380705981046170400500050301020442e1021910200c0a8803007a1041c039082285050010001a200b900c041050000265550307100c00c0003201d00c1d240f030a081a0300078680c80c5000724681318541 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 763832814 1250 763831564 763831571
    0xd05010e030a0f021b0904030f02010b060720010905031e12120403080903040609090908360303070b06060304020406091503020112150308070f0b01240e010e1c050a06 73
    0x1482507018411040700e1015096a007a001c08805c000408041001e072014090050200382021411301c01e4100000a4002604150340c2e070740c4038a05031004807245500b48014102400001040b50b10031703441c281c2101c0004004210340c4030024500c81e0f031800c030807591030414420b0040d0f21440741300e02c0d4082c00e404c0100d000d4000700341c500703400c0241c003014006143c000d403a00204003d200302904100984192802d901c4001120038040c645100288202c04500c01900781070400d900d1980103068041e24010064400850101050701c00d0640c1c1e03024902d00100003603004000602241090409141d20600003000402c0e12039803200483c00b01c0e00c40c041611017894000c2414801d550308600c82d44204290701404000d00c004c070600c41c0081c4e440d503000003003d804002071910309100f0100310b40b108140d040b10b44c2c5c0c242c0c2d5175900c1c01c841941e02c4490408500c4101c02c8900000c40c0d0017441d04916140b41031b100e403000358454030104a0b40020350111034031910f800720160300106104121044225100306d4001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 763834064 1250 763832814 763832837
    0xf1809050109020c0f0f101e020310170a0c0905062107090c050301030b010302061e030a020d0f0b010807121805030a02161d04060e01090c0303030b030d05090d05010e030a 75
    0xe03080000d0440c40185c01e0f4800c4481c01201300f00041c011031042e805c0040011a164050383c550204d000d11510b0280450000c42804800d603c11080e40e400c0b6000c4134011429840d40c40e80c82ea49030703002140c000e840c0c109003507400c00c1000100d40059078010b40c024081a0b51180454070a1080395502c04001d07895409641c0a00c00c01e40244112288920780781040c034103561440c0e072000440001404000d014442c085400340b000c0c080300328010064407810311569103a1034100303807800084d0442c00394003d40c113080000840b26051280718500300d4000681d58a05140d0781d10805807142d1180c01c4800b4182960f40d450002182c10044c3c6220310700c0d103e01c000d1943e4001c1010000d1500042c06e10108003810000810087d9480c004000b40002a002c003101c1c9582c0e4842c20040000c049503034000704154241624007042000c030180090a4a00c251020800f19030130780141030f039030f2000b05c000d400447d104002c0801c06250032003c0b80d59492140e400440c849802540440c2180c004442500c0030400f8842c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 763835314 1250 763834064 763834087
    0x150307140f0a1e05130b07050102070c03260c03090103090201140705031308030a12090503070c1206050c04140622060804050105130b0f061f020a210f180905010902 72
    0x544051458549941401c042d8405c40319400614460080d00f078000003851030400ca000c1d01900c0c8141d4100d44807516150745da080c2205007881c1c554401802c1034000b001c42980380840420307a0110000c6038000c40c203101400005400900e08039209a06202207a1a000d0680d8005030080030006e02c038801450710b80407190085d114000c59500f019074640c01c20700900e09842e40c0582002450b80f000c110200341d907440c90034203a00703611901c403025003144940e030400f040c50001c40c0556004140b244004001d01d40c2c0f41c0e2840c202030b014901900301e51035403040d1090801d10f00030000c0c240c001c1c0c81c0304c50380640881c2c4000b440c1c45d000c0d03260311000224185008000500100b03110b03c40c3d0115868034116150b160666480032040340003007181d140340340c0141c00b0a0031a00d40750100d05a2120301c1c8041200340b5884032000e9954102c00c4d1084940c184040c2004100482072407025034401c005841b0250300158450301510347c050440000d59910b5200c01c0b0008884a031402102d0003840203034401031743ca02c403001c070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 763836564 1250 763835314 763835357
    0xa2a080414011b05062a0313020f030105010302010f0c0201020f030c0a02010f03140a0f020903120c010c02120a030e030d1505090108030702090a0f060314031305150307140f0a 77
    0xca02c0521030200c05483c041a004203415078080e01e00c18013002a141032040000180408050b078600d810008020888880e0b0608904984d140c0201e624202880010b410182a00c0003404001d000400e64080c1e25003143c0580300d084525481401079880070301284207040e14580002c2e01000c101c4d4060b5058009558001614007101c940310b14060100714018a201983c01802912044a4070307580c502080c1d421910b83d0540e014480d000301583d04140200c0304000c482c0d040800d41550b654130f0103291504a40c00082d0f0401c044e28503124250424445100550081442d4007445056010802040001701103900c100a00601e0050480c14400e09100034003001c40030503006004150300411641003d84c1d100201554407245200c000706826024034007c0001c0c21480d80003c200940e45645050031290100103010311110609010340415911000c00c680c80c588411501d507000010400302d809540f142d2010317030352206070451862a100c07907090760000740c0d8442c138400720002c1c5072200070700718200c480d2a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 763837814 1250 763836564 763836587
    0x1051b060a23070e0d02060412060c201507030207050d09031a090a0f031b03052101050105120403261b0c0c120a0606080607080106050a2a08041401 65
    0x10542c2c90516028001411031a1004c00440c428042c0d4006041155148412940a0311111520315010045864000b000d02803221810b00400c010003080e00344080d0711001004c2181d0210010030b800e040940034205610400361004041580030045d813808203000b00308030b0903102c0c800c1d51006141455400d16188a03c04a21403c03442102002441101440010b10310516600a917211204941e40d24042c0c9a02c0d100807500c0c07006510000007002030580020281203a46407540c01a41c22803142c41044081840034000e07603001c00c2c01404020700c410340d21206194810311900b000c0f20704004151030041e205c0d07085464030100a5070300081110300d40700c0043c28540b401d00c582c50350781080c03e400300c40c5458210390707036032940a10600049a00241800c010b100340d050b4014104202c0305ea240c0354459151481180c222000c280390000020341d80303126000300d60798035a0903a90404a00800071221011030000350f4141c40354030642d0110ba012071075101c0107000401c2e88800307040280030084009010090a42c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 763839064 1250 763837814 763837871
    0xc1121060108030f161104152c220507080a11100807110703020d080c0d080405030d02070302010605100509030d1b0b060f0405070e0f06131a040b040609030c05040207050c01051b060a 80
    0x60814003805014202780c0e04041e0450081107803400e4410082e0302d550001d08040d01601c107134080041c1c501e101003100300360140941030705034403022044180550b001d00065805c00103080c4000107100240301d100141030701d010356419a0b003542d43c0c80d0001100c500c140300301900c2402d000205001e03031400403c0002003044442c1012401d91501b510340030f131240180ca4071010a6a00041c20a003018402e51029002c0c0000414103407902e200d81b00010020b411105581307001e4415494405015030240c601c407114421f10b510314140b80d04050b5554110800040c05407600030702c801c011206076540328020140328002c00d40d905d01d40402182d040240b02098841083d010310000c21400710100b205030a50801e55080c800b00407000032080d055031100707100315401440c02c45400315004c20400d0303000700d1440c04c8034042e2100c0f00c42d403611507040000301d100d4000000e10641c081400b00700c0340e50003500a41500c128200300070201c4c03800000320a0810034112064803105680714207103290600c100d810a800b03801e69 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 763840314 1250 763839064 763839119
    0x110102030705090418050a061505040501120309081c0507030e04021b1606020c0405060315280e030d0c180e0f091204060c1121060108030f16110415 65
    0x101d1b02e50f5625000034045c003620349921003410109224000040c6401010051300400c065030b5a221406c400204911040740011128940041c0d41c41000620094400c01e405807626070303003030554080d5181d900c081c00440030b010f4490001025a66140f024052444000d01075004c02c801c084121400d04210314064468281103a00500a0300c1c0e0000d64101c2002c0140c0d80020191600400030380fa0000314002030040500c3c00e01003080c0f2840c501d4504411003401c02c181c00380c100000502c00b054034a080c03c120510f80c0140940c0d942c10f22103030051210700e507217810200d070800043e000d14aa2890960081c0d0704204004090003040c2c0d54402079250b0100f121005009107420708030404029100e0391203070300c0030030440099030360500402507001c00d8a580d0082044c4096034042c200c0ca240b0324030707001401081d13000d00400001e40c031001000712400c21040c2003e491a01500c0f40b000386400d09030110a80e4500f614195503d9642c8031482131a4240c44040215942d1624104c17610916a280c4034149002141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 763841564 1250 763840314 763840361
    0x705120c07030f0c0909080711010207150c1502031f291b010504111c080334081b0702100f0309050a060c02070609030b161101020307050904 62
    0x2000705036901501d500c00c0c080e540994141c18070004480362074001000151402c01e00e60108003803000200a40c40c03081810000004048c0016621481144140000101c15050600d00e06108940440409118007800d030100224001780b08101c1e001180c1c1611118149821040b04000011000000b403c1c14107a01c85030311158281141074454150022010341008601d8032030070b05500750b11001c40707590440208818a014203103c69600100c40c00240900028800501842283c01650000031b4000300c00524545403c8003120300c5140e428004030420203c4294218241503115600b51400d00070341e1040c007a410b1081e0b00550290390b100d16150211004c22100005803034030340d4403202040c220300b0304541c1031195080550107070607543c1e401810742c091191000e0410034a5032082680d880651300b240e0100d130311600281d0350600c00c0e00001d0420b4120100082e15000c545c203181c80218150f10b400107480402d596564266007040d0741c410007040c0b000c20144002d0900d0310070243d40007901d0b1003000c4a5030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 763842814 1250 763841564 763841587
    0x11803050a14040b090105071a0a15050103050f041b03080d14060907140310031a0702100216170408070f0e07051606200d140c07170c0115060302070512 67
    0x201781c0503401d0602c01c011601c5018000740000c0a01c01c1c1203d0440086245041c000ca01b00400c1c182540865030031585a01181c4e6510070312501d031041542c04402c85940e02d6948545001c1d44e4212060340b15260031140c040005681c0c4009414440c5425a01040320080c011080c251500000c160f0b500445080c010444174a50202e418080b25000c559903030f507251030703690b0821081c0e95643c00103071000c00140032140d20000081800e501c9482d56a0940c3c0c41141a003190009a1144980341c0281c40e1003401c40c2d6001c00d10f064500101c80c001d409400b4a096540c402680c10140180d201000b0003c0c3c1802c20002c4049603500f0540c404c3c0103142062400b10f040b410304203c031138000780260400d540c0b80d041801613a4100204407201e0046400240c694403c419080c1c0608040b48000c1c0000c0040b02c0400c00013044036058441d0940e0025040701d00c01410401154a50007006810050750340f80c4110b800c88010a28582005c3e2056a50240e0f80b68694244185006c4000c589103039024420030000c1d0a15 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 763844064 1250 763842814 763842817
    0x3020610090b0306130c0f12020306150607080921030304050c0303131806080f0c03011802060f03090a0f0609110d03050307030f020408070605040612050910050603011803050a14040b 80
    0x10318010001c1841c1549040800c203c0306e039a0000d1008690300140070424070400c40c0f481030950310807822201c0551352003148440281c10320071500e42008003808144006401e907000740400300c0000c2d203080c40048807441d034102107290415a00070150170000502040c00010720840422420a85c0114600703079046011a0b081802c5100d0b42c0844094041d10042200030b60304050300802c0488116484e941241b0b030103a031540051081c1910940c0b801c070082014219070a001d010b0240c004003c40e0401000c00ac00446e10b9100030204a080e010f90b01c0081c0c0001c0c80c00450070f0125016010005040155103081001c1000205459102d02c1c00034501d240040e5010301140d42c070034040d20b0003182c22038100c401c04011340159088288103009082000c101241e10001800440d80260b584030b083d25556004681220415520003d464012800c2c0d4050701d4a076801040d08040c02600000f04d21607500404010140383d10f2080740001c40010381400c0065204a440203103d8180d100145050302d0312203040c495 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 763845314 1250 763844064 763844071
    0x61819020d05011a0a23121e160e04050d03110d150e0603060f150a0b0c0c03120c0622150501030510060f0e0403110f010f06170a140705060703020610090b0306 70
    0x1509541100c0f40e00d40c60140030440308d41c440c940407a40c0140310005e6040d100c52100641d11a1032030143c400140348c2061101140c080c8e50040040c05408200d00c40c210050800d4262100803e401000441000c1002c0d200344107c1002e008000d51007203041290b01c20480c1009000b2510135489181032103034011030802d54540080d03480501c010408106c40200c0c154034103a9121603003504d40031910040305c41e4007160045250204400703132241407500000d600720310f01501446030b41c03580c40300c00020070000160302d03810382111426100603038004843ea5410401c3c0425400d01540315200c0004008001301000444054030303884d00b090280301e04044068110301c0462040742d401c840f2450200382458001e1a0b91b106810781c010560f000c0c00240144035019180004541c8940c51810200080c050030b83c40d9546080c0b820b0324041c1040010f0307030301c402415806910364030006005010000881d551007034000c0900030300c03e4020307000c14030b003940030385110565503402011030608201d81c01c90180d602081d11a0b1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 763846564 1250 763845314 763845319
    0x140c0109031d1c020a05040e071403060c07060c12060b1c0e1b04021303230105190e070906060906170402010f260408040305061819020d05011a0a23 65
    0x90f4440c090001030000e54041d4041134000d4070700286004480b20114144d01034800c00e028a910b522101014595039402c1100e940710079840c00d1003650001500360f00b02038002d54241c41c0100403440042030b10412215698000b09089070009200000031b0388002c005000c54031760031410000d00400e00320b859200c44a107034505108103810115206580d445074103a62070320300c115150507140354503443c0040d6210411401c000340c6a0300f00e601508410414001c00c4d21401080e41d9020341c8181081d00180030381580741c81e25207079008c0c1c003101241880c201d12507900282419030303e0044140c0341c01c00141459071600b02c0740181e444508c0801003d41d802410543c010360b030615103600b0491a629a08a1440c0f84038a6114005007075800d001c1400300d44005041502e02681c2510003544a40604030008008202220b50a421202c285190343e0740004007a0903850014040d6507442c580b5507103190840f0808458a0001d050042c0d4408890800024000c05408400d1040047d991780d0329503045090307800c41c801407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 763847814 1250 763846564 763846609
    0xf250e1201090804090203010e010909020f0f12151006091a03061207030803010302100e150d1103090a03020c010206040b0a2c100c02010c05030103060903140c0109031d 74
    0x90600d08254048075030b96070007032019600c55407582c0009010b0340c02032140700c1a03810b100f00042401d1a0b5817241d2292560700038a2000ca5002001c14881000315400c1c030594451a103042e4041c000b002809030007241e200ca641007482901c0c00210741c80041a55410003004c1201480d0184080411040c003040305050382800b6036240d81d1002c1c00101820300d01004ac04181c000c41c1000010060924007840c140d0740b01300d6070070a0252580c1001c54006002c02101540103100100f0820122001c030003d090f06403005d540480e02080e40300ea000042e41c81902e144038290701c01c14460080c103a0621030400039010900c0038154034107040e1a0380c0c00c640740141500e001e980d0f607140304140304021003010301c01c6403640000c00d102d03840c1c150803002d0302c55190303a10707d04ca03031414041004401441071050071840d15150303ca03d401c0da400e60310748000800d440c2038101c1c00e00ca950700ca002070400e00304001d0304083d00c007000041142c035950700d0000d120044d103682c0500082c8940189401660355841e003614140304242008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 763848920 1106 763847814 763847839
    0x424180515040c112e0c08160903061118030f0d0e06130f030c140109090c02010f02030c040e01050f03030a0518090f250e 54
    0x1010050781c60741211540c0b410740d0040075030042c2450f0080501101c035000030710306440003410b08004a0300312031082100e000448441c90308402c5c1501842a6421050058914403010340102c03501c046070481384100520401190b4000c60300312605200f0307070125200d0681241d100400e00d800b01c0d1900c101107001c1d0f041c0015001034103542c690040030030785008407003100c0e4101c10486a40d40302d00c041140184a5940c0d0300800040c2c0035008680c01d01514600e06141030b501564046c1e0600700e2684c0e070403121682c09c04243c000b1164903807004940900500000c900504985c0b104d03205640c400310501026601440c09401902ca10f003514010036600e0720104241c01600803001d640c190300800034a03219500c41c8010b0032a100d1222800c00401001c030001030011842152000c03107229195040000840450300c0402030440c0100c2050700d4403160350001402c505036846403900a01055529 = true := by decide +kernel

theorem cover : BRFrame.Cov 763669064 763848920 := by
  have h0 := BRFrame.cov_init 763669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 763669064 ≤ n) (h2 : n < 763848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
