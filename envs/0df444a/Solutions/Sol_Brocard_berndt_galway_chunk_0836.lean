-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0836
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:03:59.00984+00:00
-- url     : https://prove2.me/submissions/3932db57-067e-4858-a56c-1ba25cf51a43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 150179856 ≤ n < 150359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 150181106 1250 150179856 150179879
    0x14040209150a17010e010501080a12020114070c03030b01031503021302041509030303050603070b0f180a0b04140a030512280f1b1e020402041d0612060907270501 71
    0x103c1d01502c000c00000c49801c91241c00d84000b1301c60107046074005181c070008689500b0429262440d64000001c03c940030400445048004031803100102d040c00c241c48040c0b40e058010740c22390307a00918041140c01a010015407024105010281c0a89100005048c0b2070a80e80d0486026291b055a4000a200f03103035402001c850141c04124000f03420f00010a0582c1170006015042e02ca421152a08003370300014501503542001c1c0d1a15156841404c5024054464020310f0700a0700350b502c1d215540e9414840002d640b00c0c400920507002c0d4120b0340e020004200c0c04100d03a8407049552450703a40d00d17480e041d01414100d1644001409094078042c01c01492908560940d00300d52541c0c0399403000e428064240c0400514106024210b111020f1070441c0207c016a950101203100030401400c054072405c080e0401d403a41b8030210030104408061000f907103410003880c00b8003400c3c0e000030400381c81c015075002c2d01e0300c91500c20101d034140f542516045032404900c003a280d03400403010402c250340e51466003031030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 150182356 1250 150181106 150181139
    0x3160e030303042f03060a022107180602030c03040b1309061e080105071718060108100506060a0219060b090a1e02070b010e0903190807090914040209150a 68
    0x212114015003990307201d96007a050300c51303844010040e01e62985d800d1110006507010b4502c0c082034266a04001c100010388003c424003510b40c030340d1080c1215000c2a250759079180e01d40c0246013554800e12031400c2620000085606640300e545000b074135402c40070180c0c46205169002480c02c1420490081440014904150004001c59010180082d034030b02c500c5080300e505541d45c4002800d03500f12041c01ca0044003c0e9504054410031165280c04510003a48c2000e10030303000781c003041d042071110700c05104540c042c00360091400c81d611454600043c802175520040b00c2c041c0c04080c0000075100d824000c56a010341074008000d00060f40b203140010f540c0c8014400303c500442d1f4500b84507083e901d001424401d03940c4a9174401d24000c0e030369080c42000c64180200521000b0b20b44030402030302a0b0f00e00c43d00106036450041381c588031000c1c103103040f0160008100b9000b0214480c542510507070300d20200710046070400e070155002d0040e52241c1c030440000c02d000c013031019040f04540d03400094141c1c44458988 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 150183606 1250 150182356 150182393
    0x504022b0c03110327100e07050411040b0301030b101203030e12041503050a09050a0c030b07030c0e04050a06030606060509040b0a0e180109050106030309062303160e03030304 77
    0x11250300844190099400251002c52901d038100001346221020040400c00e50703c020170484900e00c480380740706010b403010441e01c04c1e06600082001c002c2030406005031150b18111024150401d81403d007407642d22b0205100103041c80030381c00702040301d05c181c080006018040c0180c6a9008401905011f4003400030000d5481d1603100b00240a440c0300b036000155400c0d03580b492503050000d00000b4003100500409884241e01c40d56850644000400400c1030140703407407041404002d480d180d42403200c00154014821004d15043c4040358030f07456884109030310550070448001901d81c490f604800014141d40e0001440e01d07140c200c2c0030841a0700715020701001d500c01c48041c0626440340052200420722446504200030b25440818240700404070440024403005000180c2900349444103820f5031a10750080d40840e00c0c12009020613a0b100e03200300080b070f00a50500000c0c1d4420b460443e002d10000b85144400032024000c400382a1041a40e003042d004004d04581d224101801c0410702c00d4424201d40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 150184856 1250 150183606 150183611
    0x703020304030e090c04090c0e060310030b09011521020a06020105161704060b1804030801060f0c05070315060e09010b040b0102071401051e0705060405060a150504022b0c03 76
    0x202c02460800a928400c5d06a04a00d5040c1441d109000004c0e260f690244001e0206991141c032a079203134200650700c511100c48465803464510704080c40b44600240815020380d040003148000745803181d140c136086402018140c03146605c0107501400301254040c00a60082c00300c13000040c0a1341c150425030241d80f43d8032202e0811060944140c41c0d2811a440720344a20548000003800304410fa0721040016401415120388114981c107008425103044500f00c0200d103403800103210495000804191095407400c16100c041a15100e2035541c0e070051100a115450b040c0b5161000000b0b81c208600902c42803c80400d24181011030602074016030341c1e05e90140385002c8c00001250f200181210485200c102403481e00001c00d00111026885204161040103103084005201504a03006048031800340d00a03100904140c6030050501d6005000010f6807414040160001c0e08036410030021118101c800607502e00c10b4418481140d850040b04080b503c804010300004288203400171004199682d604 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 150186106 1250 150184856 150184877
    0x6030507050901020703110a051005130e0603100906020c0a050109023a060204030209090d0801090c05160204090b01030f15051303031503050111040e0a02040303080f130b070302030403 81
    0x45a0601400302803c0c010703800300004001244401011452903d0041c21020103aa12400420028800071020100013980020244140d013020b03001d910103001501204855401c0842c0000d070f4a00d5110144010030750303100c2d203200c00c005031903040b030304401e03c6a07042c2c8085e000641070280c001e0030002c105900035982c9262045200c0c184c404211400c0740d650117803902011f1031040c00c01a20010080c11203000d5030812010006d0381e51380d2181131064020400a1070f1130604420010452101a40300100082c2012289502142c105050761140012104400050905d600004014200c4500e000d411060030000102c1409900c7e600821140e0240d0038070b916140444424900315502100c03503c41c605507150b501c2c40040d01c2904010000c00c15076071842d102545944589084842c100505a030b02d01c00000d040005140440c0c1003a40001c200c06e00314205880c4d03843c00782443d1070041c0051080d0b882c1c1c20018101c0307003c07003208440c4213401642d4100c0d1842c044001078020b50003aa010350103d00c11609 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 150187356 1250 150186106 150186121
    0x9030901110d050304120c0503130816080303060f0a090c0504030b0c1204020904061508030a02120c21040801050f0601091401020a030311040b0c0c1512010b0d0b060310060305 77
    0xb07100c000100d0a564144c41d540da5502c1e0740303007042808016203040001c4800b405c404a8020406000c140f15440e804025070b80c03618040c246040a040341d4402c0100c1000c808101c404004010b481d80040e00b920a140c2c03c5c484a000036030000c440750080300410b032900c2101c100c441d5102000e00180d03481455120115160404428400d00591414070150001e0130f00140c0142809007229806ca0700c00c000220b04401c4118607054805096049441550301c04180120150350412241c440003081d0105145021030000126488180200311100004903a60162400d45440e0045070010200304000b000135080c103961300c1c3d141000030b4800c5800079900c40c0002c64040e00750340d46100c411205070028580301400340d409a010b043c0d0300c440440c0d00d030f09c107000004200207088000d05031030120b0302c040d02550250b80c0401c0310310030300b176000b400c0e900600b0b1280071800c00007200024151354286040903118511325007000090326203006400d402c20008814080166044d1451800b51119920f0070300c0325580340207 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 150188606 1250 150187356 150187363
    0x30f11100501210b07030b0f0612060a09060b0f07030905060c01020904050c0a020a0308091903020a0b070509130e1207060504020306090c0616170304140f030301060f081e0903090111 80
    0x820190401c81c441010170754443c0a40d00480c2c010030060440130340780c0f58540000707038140c00210002e829206101c04008051800486031406020b03e070004011407410120103600b68021060800700280700083d01206044c00fa20004004040040c290780d500c0381c13405a290b01175040341c0c0302e5900030360506c0f012a41103807504080c1e801c1403105500411040c42c264608440514014201a00c1401298103a85802d6110007541c1703840d9009800400030303c4101e182150030b005000b001301d001c0103000d100d4050281d950700c140380c003002c11200011404014100e220303803c18000d007917000001d40000034200d040082c5908000d00c558000c60503100c2c5036488100c16502c1d821040310480c0d005408208480c022020f841c01d8142050266120002404900d0802c80682d4020341d0b043d1110791020100050402c010842801e0f03607880c8a024600710f515029024001c071620400d0740090000c080005a560740074640c61010042c6001d00c9851641009510980c90ba030182c80032a000968018040581c240c002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 150189856 1250 150188606 150188669
    0x3080c0714010c02060d0e0f010605120a0201020d0c1506060e0f0d08040513020408060906090714060405011409040606050408070501030b0d24020310090608150103030f11100501 78
    0x10f8480c0c9001e03019030b0742000300720750065180c0029907580c0c82d4100e1110104103c2e40c000881c060000082990401d020441d04440039245403034a40d02c44e180280040c0d90214090b00e528046080984614805240c0121382c0d01c081c814144034103180810000c0e1095001c18100c043e800140c44107900c00c80190140f0031031900c0710740040c040e0300e42000104013a06002c1e040c02d043d0062104010b090684500410f4140b24040d81c1003261540160309000071502c043c805100104074800c8130810700348a002c0441d14030b0041d0711400d07041c0900c603c011241714200070102c0d24142001001080340d16143c0300c01416507005401115090300c2000704c0800e855010344559040040c0003855001d01014941d1101c010b4180c264044000b035403054103510000c400307400954001d4000b66211094a811b0040d2041140c5640d80081d40e5030780907606212020fa040031005064941504c0c0c007402c041d82c040303010303030f010500707004c02e0100740c4641034140e070a03940503610140c10b84d8029202d0300f1003403546100c01900004007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 150191106 1250 150189856 150189859
    0x1512020a0903170720120105010b03010e0c12040209040204020d2f0a0e040c05090306010e01030b130b0403030506030c0d0b04060b031c11011d012f0405041d030403080c0714 76
    0x900c101450176054804c200c142c40100809140c480402c0e544007a0940c0d0080c3e01001e00104c012005000030901d0301102030388142d035117510302d0074481040307280280100c02a00c040e0280c000a0046415900c5c0e5030129442c280e4104401d0014001482600a0041c070349210050001d000c4000c040c8180c030b0350421140f00c90001d9440d041044403400800000742481241030b400d00c14200300210054a044c0000e40c0240009051440b4a40c51802c1440308014010213012180b181090703850002440e02516030382040e01498006004d03030702d031000300c0e241903144143e0607400610a1014020000d614074010b100c6c900c035030028000242041c040c107580b180306003158007200f010450f03540511482035000f081900302c1d1794000310b541540624407811001070f09842c440c542c1d454503400c007400064000000c5020340c44050811010558002c4212680038070b0280b603100d2a00d03101e403804440707200446004000080425a40c1d034070f9403490546119480140004a10f000b200300003d5260000c00c0c440915160 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 150192356 1250 150191106 150191123
    0xf03061806010e0f040906050106020a0302010c03091e020301110c01020702040f090503040501081b160b070806090c07030306080d08040c08030f040e0703020c0a030809251512020a09031707 83
    0x10f8010091103200801413190865610a03080012400a0003000d0007002c190700504203040c02030800a003507a40805824051504003a9907000040d1040b0007034444845910301c0601500080c40001d015000305465207005000c0401d1001041c207040d4014a5014800c0750104400c5044c08240015105080d0021700681c01c00d103c00c0040354021401c0d5540078051403c20001040e40ea8000040c1c0e4002c0090a02402c560301d07882d1080040c08404560060000c0c1015030755883c10b91300207203140c0742c01003e14450764000305450003054040d4201a000d01a8a0300b40c6c2e01550f5840c0c4004c011020484003a900e400440c400084c202c4004402c071556a072030b041c01d0a10f8103041c02c141250b41d00d03002d000b21003055401c001c0c0401d10700052101c084601e100c0c1e80c480c5000d00f404042c0c43e1500d1070510261003201d070071303030088074158400702a0002207408403d0f4039194084207000c10345014040148070302c0c03a14000a8401e14844c1d00c9280c1c0d4068a1054251080d0300c500c840c0d1079081c501031810018203841 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 150193606 1250 150192356 150192377
    0x11e0e0c04020310150c020a0902090d1e050102030103060e160602061f03050a050109050c010e0a151b0f031202030c03070c0c081b1003020f0a0503060409080f0306180601 75
    0x14541c00455010444024130881660b4a4008141100e4203503090700c0014003400f030210851420b4003044009061000043d410105980005103200800329401000002443d070000d52814200c10f0300140950048000c5489603542c1c18403602034004110a80994080c402c001c40080205145c1c44090360b0840c0d00030310055071140565040301c00c00c60410203d1440e5a840040001c0c01002050354140c815400464987d00900e040d5150916400c0340c641881086001c0801742d44618001604648038500a500f82088080c016280794003001000c40c001c0084d912880300b44002030121402c628032030345c0d680b01003c610800e44812800b090314407480e030600030008110150700c1412510425130046500c061420742d2406c0b40751600da950511401c8480403e810b9a015190003900030a0350705d51400c0c01d40c83e01c00540c8440c1090301c503100461007440070110200c3c4581e02c4580c0a400c0f034613130041300f9650b9415030b0a003121264004072400c2e8030a008500400ba000c2d40030340003141c0102010b03103602c070303150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 150194856 1250 150193606 150193609
    0x203191a04020303040504060815060906011719180309150507060515060d0c0801050307030f031107080d0903260a0309060f021204020307080d08010b030601030f050108011e0e0c 78
    0x800c0241003a64548424080403031180d4a52185500038140100248074424052a1a401d041c02c02080c0501c111514030410500c1c0e42c11030b04096039158140c079a945155141c08211121260054140c10840d242c144844e8041800704160700b01c481c001e40350050788a9841c3c501040c4144803903490400501c0074420000050072541010f50000110001c1c110a80c01880208005800034141840035940350302480d102c090708100b069015007005c0d0013802c1301505503119042c244103c0c1d88001c0070448115240c160250081c0005000751031000142c1c3c0c50b00c580c0c810028000d456602040e40c0f04e401a84103003914814980002e020500c0e1101c02d90308004140c0303001e0f0000d001c080d906442c440c0d122030080601d125148000c200c501c1d2400000c5c1c1050500340185842d1415507086928160701000d004102d445d0030500e1641181c0c030b5014019901d540d00c40048016014081d80406694100320010882484c19080400740a41c80c0412079000343c4030100e0a0140c42c05804100840d4101c0108080d05 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 150196106 1250 150194856 150194903
    0x10801020315010e030c030604150b0f0607030e030f0610060807020309130b01030207020402031306111c0c0516060c02010b060405090a0216020d150f09030e010c0c0b0406050304020319 81
    0x4407507005094074030f550a100f0100b414034074209c90485803c8400c0c04c1c0307200d00a15500c41c0c103145820690300c1c202d0700820000441c02e54810140007a040c080d80e414001645e81d07082088a20300c4c1c0e400c42c01d4802c203080c0752408141c05905070040d2004075942070001540c59100000351040c0e040c3c01041205c00b40070710685003000f4a444111541055001c100e44009620340d40003d5000f000d11010b0001c10601a0900104071440354806190412041050089044c691b1f107882941154030b40e0000b0300072020351070668030f40c8620f00c03011050350005100182070004682c0402c4c1c055210390003d020390054071080048512640c00b031103501c5200000890112060380e4017410451141d01490b4210301c074990000303213001180390022240e0101c2c0401002d000b1409020b15042601103150170700c17a860540d03034040d14542450001c9810410009011014802101c6851000f4a02c0c0e68070550f403240ca49400425940c002c4805a010303204032200c11550343c910414602e040303031304581c018041d444480b215101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 150197356 1250 150196106 150196127
    0xf120b1e1f150504030209090105040b1506041502010b041d0a11310f0908090603040515090c010215040b010e04080408070f030201030b0f0f040207081e0a0801080102031501 76
    0x3500605034030049910200c95a01442c000b00c02e88035a42c07218a144104140590001d0141b0090390410040c0070000303108445c21900801c02c0494082c0300003140b80494400e02980e840441c032859403040356084c032034042d07010900202041c0c070140103104c84d411200f044150341410102d190340c00101c0c803030041580090581c4410000500000f88208541f0508400300000056030542c02c020034414a4080680e201d2104c1d078030711408040c0400d203015150240f41d405402c0a182c02107100000203010440248603404c0e41102001d120f0f070081c00e107803400c0d950301e550048030345015104c0c0145005040030481070791442640c0c0124040856801d02c4001030b05010094000c41f1154014800465165424071805001d4019091071181061550000500792568110340e140229840a07000720307551601044080d200c2001e59003d6030342c0b0030a243c420124860100395801c5022481d0f50642c6a81181d00100307444c1e143d6503031311a8581d0701d804096080b88025143c092492450300f03ca0703401540502d000b0103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 150198606 1250 150197356 150197401
    0x504020f01050d18060213090507020d0311130e010503011103060d0f02180c0d06090b10140904060b090411130e0402220c03150303020601050f0a0f120b1e 68
    0x181c540c0b40084d000328400c03c000803c54034150045001030410484500e094000d0401c44018071182c227041d070029488a0a07400480201a115202c1f522408081000c0b104a42100b105040c40c0664034038507603051030b40c00e00a0512a5007804810500309035114190390040e00e00501d81d0106140f10f035600c0040291a940480e00f04144140c1c54105800c0200018810172221142036682e03481c44006d5801c03140c0b05d4102605403032a0048046158032032240b0241c2c640e01d1800d103180700341410003602c2824001c50b8039040d44141002008102d09c200a405401101d81c00c0c0d400f88000403006120b01c119001345528011540030320542088400d9000d401180c01c41d0020b0401c003000d203101d1450f1106418000304803c88543c40701d9958a180d0b51510034000ea0000120700d203411035007190f500075102d03141171141c213210f1409035045d00015a15145114010502c200451500954403540a02c1c01013105409030340c10008000090711683c040319041c4550002c1150215881c0e40341207070310f00d03500c2c40f9422aa = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 150199856 1250 150198606 150198611
    0x5030f0304030305040e180a0b160f0f0e2101060306050705030f0a020901120615020c03070f05040f0b0405131703040b0601081f0f0305060109200a2705130504020f01050d 75
    0x11b040007012300c0524512800380c031a00b111407030881d50b40e11000920002e00d0b020444205944240f403a07100b0b442054154240c5030034149543c00b0f40004510060481003852000c680111690f80840154485011030b031095000f0301c500da66035130341540c542c001140c5d03103100c80c0c3c240800640486240d90007003504480506080f1720140d05080004216282034202e8680321801c070340301e0002142c042110425229049000b401c86c1030a005140b10a0241480b550b4041da4986030180d04400454000e00c462003000751040140c0e00e010410300c210041e400109903a030b0502a1110203a1080240499100d2904407070113240c02d4507108011038403a81c00910210b200b86084d0380400654106403400401020343c0b107010003d0500318185981400c0e01030b0311108000b8940b21540049000380c00c000701e0103032a4819070f01d4441d001910151490f0003c0c1401e02c810460040a050101e0004921a81174841c26500c00341111213170040401180c030180c030060344c0406c0003410209190710980080002c4c03010101d01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 150201106 1250 150199856 150199891
    0xc07080d060b0304062a050d1806050906061002070510080a09020310021e030f0403081803030106050307030c0e090c160f0b0403180f05090a060e040c05030f0304030305040e 76
    0x12800b00b9003040d0707403c88046480e4111003038060708807418201e881030302003200f40d01c0b0100040b0103011840f0342c448003102c0944994140c1010201d1446080000750002d03010b100a15040c8005030329440225207070b030b00c0b9402d440c0b001660284001503103016200d02406521104400c074005030340380d5000908040003a43c030b50308464016142444200105483d03e000541c46100c0c038603000404100644580080744000e10802003880201c420309900590503090000311a03d070080c40c450341031043c0c1c011481900c070020000810360740c004011886200a43d82c01c00540380c4160081300c600030780e901000c0d4054a202d000c80c00d0034003040000c01a030f4107005010740c03100820750384400002c00b150308103844d141c000104000515800165101c0303035541c02528800002e00b42004502d41c00e030030380610340c0100045070008020101c60340c00384e4050f200001505584ac6803514204540c0d0129005050090040100c0c0c941b680b5000400d640a695141e111141441d081a242090b44200200101a10721140c00d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 150202356 1250 150201106 150201119
    0x605060a0b0d05270303060f01020127030f03050405250906060c022701060305060102011401030b19110906090f0a06050d06060807050304060b030a12020a0512030c07080d06 76
    0x1803050102c0c800d00441c0c0c0c1d14045071492501c4820f0701c04110b014203400548092000c010040b280d100c1c5048071601c000b100705e800100e00400e0698482d00103035002034150f5200400c407012000c2030301e10a03510001e0600000781c0032400e40b5429107004141c5d0344554214506840540d5502d8801d81100e51382c50f054a9440b6614020344031203034441070204d240326a552040d81001d0000d60044c81e07240c1014516030b1032220900e41d210605100750010103994102040d0305030304c00e41104a402400f05002e003400c0d40c41e81441e00380c48a09417200c8a201909022000340c20006010321010186201c880130b060403185024407503154018072113145d000c2040c1c9020405d59854440c0d00c006442d40ea07403280d807200103010322041211450342002003070188130401c0101d5980d1102c1103d0780b069101d01d004ca600810341c80400c0c03800c102d441e801050724484840d4154415030020b02862154081c0080f648425468202c2203249e00c8151200111483e0401540c3c0203d050301000713004007240b0035000034800c0d41c0c610303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 150203606 1250 150202356 150202379
    0x204050a0606090f080705060a0c02180a0c020f190302121909090209030303390c01140415050403022a0a090513060c0203040b1c05100b03040605060a 66
    0x280e6000000303503160414031400d5402160301e4041e250004007440090308080030159104954450140304110009140d821548115045022030354003810000c400c00310b60300c1e6111514000c403001590f0701e1901c0f0381303800210301c0001e03007085120b160000fa18032010107403c6658603512064090707040d0b200d490603011101034050001d00340a52414003a015003102e0403001450207015901c1000102d00500c58003243c0d0f50003000f03ca400c150804801c040d26440248812428607200311041e50000b0500000c0242c075424900900303510405074000c000b140386500700d20100d180c0589018001443c0320b1949413444809a001942150107030040701c80130104901082c1100b0b540080c21495009240d41c1c400250410b030b001280640030000081c806460010f1020403034a100240181180d0349030610103070701500078411500a8240d2280c07003903451040c0940031440009000140c0d12151801001801c8442028800c400340c95907806094515103072501c444001d060003404850f441300e51050002405030211 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 150204856 1250 150203606 150203611
    0x60315010f0509060604030302030405270709090b030a11040e03190f0801090e0a030c06021903020306330c1e0610080309010903080c010b06160b150625020405 70
    0x600307800381a01d0520003071054035180500800d0050b0000d00007800000d40200c11348080c2c403001d60760000c0f801e1840340c004500d120101150100301440d602400342c1c1e07941c400071610a82e01e44c0d002c284001c140e00c03024141c0d03901c0c105202801c6486450f80101a510702500010080003000f8101c034144000020b020b02a0b00c0340901707074400700c0c888030385045e50a50400381c45801440c94002c03c105e483d4070440ea49803911030b05080101089600c1000e0000c01200740e054650507a01003c40208910100002400950054071114072449c50340b0b810300040e130360408614600080300c44103180040040c00b84100c040c0c10814158043e0302508001c03201031074400390078440415459000b80862b007803417a2404103090a541014806070800c001103031003640c001a0f0b010440740d10150103550381c44c50450090060200d5a580340e44514000b900080e84030440203140003090056403c500c0710744980c5001905a12596082600841d00303100d10f1500c000c0b401c3d070842c0320000d22070768292052401d070f000030200c5208 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 150206106 1250 150204856 150204869
    0x3070b0a03090c080d020304030308072c0406080d09050301060e040302030703080c0408060a020a0305060409120c08090306010902070c0e01060e0904050c03060403030204170a0b01090203060a03050307030504030201030b0d1a06031501 102
    0xc00c1c00c01c01e040c0c2c0180740c00d80255290410925260744412011048183765000701030403501358040794255202c5910620050105030140c90704c002444034010300c40002481072030322030360801c10042480d150551840740210342c0b5400840c0381c506140e40503940240300408044400c40b0901000400840038003040b84104554000140d076131001060242c1150340203000d4a002e64501841d80000a80045103845945024100107002ea900341c0f40c0600907104403441316816010301c0000107004921600500003491050f03820701400f03900c400c0d002010810900c01c050000d418003c0c40c0b409030510041898015006e64182c030003000c1c000c0040303454024290f4080300040c0c1d0014041201c0d01c004000302c0759840c41301024142c50b950a0325820070199040c090348090a03400400301d5590760390b0900346c0c0020350f4050152511410f440c2400340594200c1c1c030043e80402d0604201402610b00070503004061540110034201d9051914510007540300d0003484580c00d4810690440000c151410b4000c0c0205613 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 150207356 1250 150206106 150206113
    0x60e0a08060a1e0b010c060b041d0a0203010c111c0c080a0c0c0f140f0406080a060212010e01080a0f0206040b040902030117010209010507120905120102030f0603070b0a03090c080d02 80
    0x495400e4078802c00d00c5490f00ba030b014070b00342035442140c0c0c3c040d9484080319005480801c005400800042c02068464a100404031140002c8504490042220b1b403289001310001c000303202420328181d076043e1312009112641d80103040040d007502c100c1d00181c1040c04807446c12a850303800c16076800c1000d41c880003480c804610300054010070021002d0144028000508000c070780345d8503040c2d070007040e441ca01032880d2080701c000210641036201c5da4003620050240c00101d402c00d02c85800d213100290f015a0500340010803440c0080707400c00e00d00c0485412542c0000003052000030640b10850f0481440700100d0b80100c1c1004001411061103015001500881e40016500d5141c0320002a280110701e803501001e174014410031056a07009825108000d0300400001c81166038101c080718090803680002e50311003812a14a440a40154041c501c15100c90600040e1901c9030005c042d03441c1c40e41e01c50781080324130400070180380358400d420400a99100300d120420282d00c50b90341720b0400084540c4040141d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 150208606 1250 150207356 150207371
    0x50c0a120507062406050903150f04060c0e061b07180c020f0d0c080c01110f0c1501081b1215040b0c040e010b030411100201150803040b04060e0a08060a 67
    0x7242d1044d0b285000d890400c0319404401c1c1020061a0314007032082d8400c0c0000440d089615890078400ca02640b04144400411807820910b00d8000c5581940c081d0b826501e81145540700c2402500c43e032100040090030142000c41d8450b040c0c211014803404140d481c05203841c0024815000c1d80310854403031a6000c0403500f10700c00e0314024589181c4403031002c0c0b00d604c000100c946050f0018510903a050304103c80e541c0d00c0009039292805441990060980a0000103411900b945001c0181c002110018103489204903200200d4400400a00840310035400036641c2180c0c811f1841400440914058a080620f20390f101d5210700b05200b018090380c606e080e0004000400144814075070b071280c07010503801d01b014140704001120020500820818a0300000841d00f441201a42400c007180010160313400f00301c0c0080001e0180034607900100030074076640d40100c2d00080c0403007503034150340303140c1013071030400b843d143e0100c4241600525094103c8020130005c604810240415403060261540100b80e40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 150209856 1250 150208606 150208613
    0x905030a0201240308070507270b030312070807090e0a09050c060315060a1b0c140102030c2a090a20090f150c070315050a090b0106050c0a120507 64
    0x481689011010031003000148202c240303d069105025241c1002c415600c40c1200c0c0340261612805030000407804246801403038440a100350b648440440f201c4007485601400002d05540c0e0040040a00a825681001900c0c880c4a0b80320b45610a180e46401407141c3d903a04540c209905062302d05c030140d00d8855000000380700c0104002c2680740c1c0c003610007034590b1405c2084140407884241e1042c0c40780000203990711060b4030920950b080720b03040e9001c4c01610329071450807081040c1c25100e91182c084210030425807540c000720079140701000e81d40c0500700210051030360392181000c01101c60400f03444139007000015141d10640318428607100c2000204044000001400e01d005043e00320300d00c00c000c104422043e1a02c1000c2c44419a0999450703501407410107110b46240140c2d40c115400d80f103580000010700004490220425050300010002500c0d03a04000c1c083e554040c001070101c034110001040150311906c000c100c004120b400760b41c001c10360b654808802440464200d00090070118800060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 150211106 1250 150209856 150209861
    0x5041103061e0109030b0703110301081606030203010b07080304140109050708011a0a0b1605030a090303120902030a0803070507020607060c110615060706060b0c060709080a0807061d010905030a0201 87
    0x24070080e00080c11400a41400081190b1210f00001b0144407460001c101864084d42103284d4045401c2c80d069140d68540740190740c0e8910741c074007002c3c03426142d6100040e181d0280c0b080302d040e101c8152005240c8640c42d00c1e0400c841d40f0150048482c1040c1814035900c1340c1080c4218070302035100b038001e89801482d088070039003520103860030032a034502e41c802c1100c51a95068007240498810340300483e00c0d40c6100d44c11041042600c10058440e00002950300d50607070f8400982d90503640300c0e07240c031030003005012001000c5402d96800203405500400c15079022842c84006180e0040f8130340ba00070b1601e0710b86d074003180d41c580268030200c40c040d840e408840e4031940c010200340e28030800031005089500c1c0040f0b4441c41035141c241002c0c0038241c000380d4030060242c0c41d00250050282951107640c1c0d100702003803141e85c400b0111840000105080400300740820081005480b49800440311350a002580e1100c00040c004504450080302722080750010341d100070b020f1880100c1c082c1c80610749950f0180d00103400e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 150212356 1250 150211106 150211129
    0xf21090b090d080604050402030a020a0b0a0f110304050105070c0f03050604120c030903030819020c070602010b010f0215060103090b040501060608151c020301022203020307050103050601270504110306 88
    0x4441d00403001034441281c1c040b41c0c3c0d41e4400c100300c6003c205a03c5900101c0e04040c0c000c10065040070a0903c0425036030490001080c04101a0740c94505101c8051012500b108104007040c0c1160401c1204110715031140000d0004603016548905034956510350100c0d0303059541e0310485072038100c1400c01040c080d5075550ba00003603c5900f8a2504000f20b07940080072405030703010040c1800501800b05148401140d4501c40300000c411045641e46d001d0f444041c9c1d03c41142c42a00015800c0051601255200320048482640650010111240c048840d500c40b00c42c024005810035a0390070501001c114084505405140510000210f180c10014020b00c541e0b1300030111078403070b4030100340c04c80b0303503284c00f02489841d858034150003e0359100c0c0d20000380a8417841c0150034080c01074411003400d41030840782500031644210111440950b50303c0054059980440e107050108440c9460074210582c03581000d40502502c001c903c0360790307072039200150403034070865080e040901d00442001160700340b40b0070b00c12 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 150213606 1250 150212356 150212371
    0x3060b030a15090b281206090b01060905181b0f0c1501051c020409020a1502071a180f09011e120503091302160809012601060f21090b 59
    0xc9544c01d8480410f0b000f400e03440c840d03501290030241c00d60401c2d8640c64610b0243c4040300000c0c1542000303040c00030151000c0d542c06e407200e02c0c6400001405c240518000000c840024001e2490502125000000908010b0000c500c05030010078402d0781001b41001881c0444400114545584805031030b40c0c500a0b8200068010074080c00c01030100369240c8139660000405126000a40021480440d0141441038402504410180710105442e01005c8c070300147c8020319801c4403529a40e0786040b943e050010041c031071242808100000c0c44285c032840031444008040d00c601c0e101429600032400e040402d1b408085000c02d41001c40081002151000000380301c1d0608820400717070300c0d880c4e640d124032499000921031007001185101c0c1c408144c05a07407103080c2d4003c0c8040315540c0c505104031260b10a402e01740c0011130201032001441403400c0240085a58980c00304002c1e0f0919006507a409801c07107840050000d0f002c47c5202184014684c03001181e07102c07030003141680962402d404501409400034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 150214856 1250 150213606 150213611
    0xd080103020303091507020a08010b1305060d0b041103100209030c030c1c1407090b010e06072103060801060f03020f0d0b0609040c0305010207050c09070f02100c03060b030a1509 78
    0x100302680c0d0000a6456008044a0000090540c90041c00c0c141c4110b0100940281120702c0000b084101944100395445c4103880c0c3e40540e5001e55542c1e422248121440c0d588020040444004a4050102d00f94014440c89641074800010310000e07281044070100884410f4000860700c0b40350500340600f40b42000c050b00103050b40d2a0220008801102c21035a0300d80d10f40358070310103609002050346200d0a141c040c00030390703c2560300c986104d0041c0100e200b41c140420f581e641007410a06240041340c2c0e140381c201003508407490150302c00880109080c16403408158a6480110342c4030420300c01e0b41c004000b4180f0b10110140740d44140602c405580ca0220700c9801101d01c2c90006c514070b40b200d1a84504c0844400c1032035543c17450480c020056a4001500310761022a40f1010090000b0329455100001c488a4038070b5659280d003120341d1150701080c1c50058112218030508000070f81c202c011100c0d09420080f0b03006454100d4080c8580003120100724141e128828010030710308044a000c064009403009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 150216106 1250 150214856 150214859
    0x7030e0d02060408250b040204110f0a12020f0a020c1005071203020703090e0a02070b0c09130f1409030a031104050918010906020a0908060609040f03050309010e03070804080d0801 79
    0x2940300c01e801000a04886400242d620158412005459502a002c00501800c2a441c10f00c0d202c6d500d4211130480c00b50f07241c81141801080340f2400c0d02c51000107404540c0c9490301c0842c0844070040e042c0d20030350b101c036004d0002c00100030f0164050411001c15900030720300f0220280030030000e809020200c0044c01300c10403005002c03c5030103511046819a604000d40d90b01c0d00303458200c411080343d50018503500b501005000c5600c140c0e030001d0800f00c3c003410000e691074882403106541480380c150f00b250b020120340700100548042d80c000101c900d800c81c20020314400f201030071820498084420a08503000004d414540940612a001c80e08600c0981e00b4102405c1038085118818050009440030b2210000400a07080135041800441d0f03001c10f0a54550070361100180036441103010340441802544005401407c10603003240c40ba5800c48030b050104806924240c900c0e07440070300f0030038081d501d81d0300568a0420401c0100401440b510150780d6592400c00300c036003040c1100881d4400c01404000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 150217356 1250 150216106 150216133
    0x90a0312020f072006040902030906090c06030a0b0a0504020c1e0f0c210d03020a030606030509060103060203180a0b0f0f0603060103080f0913020910080c0d1505061207030e 76
    0x90b07651440e400340844000b01125034622803003c00c0c04c008203030311090000d00031446003515005140100341200c2150400d86820901d80d881d41c18051905030000e0081c03000501700328080c1c01585001e900034001006094840c1c010a042e6480b09101076a40d9212400142007d21a60058a000d00d180f40141040a0168000e19150b0580d015428450880d444110038014844110003c01c20a140d0403582c09000f0440c001e006900201015401300b880c1450000c0c09a000c0c2c09462301c41c0000301f02030401030f821940e8080c025017002d40000b003005100044491100c001300070b15003400e40108855403042ca442841c40c000f03070364014034901c144003202c024400d850300c001515505480d031190b06a6200c1c031144202c3e488a019904003982e0200704261241c0e0101c0803680142880c0307405540d1070b4030f404a840070a4940200503500b0f0200c4210030014078000002540c0003c184a400b80a44501603030340e00000b420030340117a44203140e040b018805006006405208070f48064110101801e031480c03410a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 150218606 1250 150217356 150217387
    0x109051c0803040201140d0e0d050c06011205070b0c070f1d13050c0411120a020307020304120305041d0a0e01051b07140604080403030e0406180c17090a031202 70
    0x2030300902101e400b01c042000c580c09142c180c1c0e904120418030a40303602100101102401d002100f41525020b40100c40d10b6162240080b1050346050b030f00107001d00c0c0d1801280031040d040741e0300d0076110b42c0615030000c40c003001160002c3c241d40310150010911103060804000c5c0c0c180c003540c484240d01d0300908080140000d91400154065003043c0310754844081414481c1c100b038002003c0355401441c0144d11804280c800001e0100e4601c0c034085e00b202681c65000880c100c1c44280c800d200960710034002000030300d00789080711704200d110f46130150030107030f0f100c18244040f007030310203002c5a035605c0d03000300030b081078282c07040c0740400780c0c003d000b0312190520166440f0092120070348110034a00c005040c1040c429140411220368000360300302c036100c2c601818010110f801c02e0000b03c000944055200384240303018042d200c1a5012000360b0210403d400f11840002c1180d800b41ca028442d5441c0c1250b0207104a0030708174894403405000c0c0a4040380b516004001540b5000d2000c0820f1040c411282440c8055 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 150219856 1250 150218606 150218659
    0x1090f0603021305060408070305011109011e050d0501170c0a060e04090606030507060507020102100c0f0f020c03010504030e0f0105040b090f060d05041109070507030215270606010905 81
    0xa040040e40c4a480d1850100c2449050304481c5d0044000a000120361100281c480c045034004c1d4000c001c031400a4940e64842c2c4140c515160025407040e146550705190302e00b0100504015060880c1b600360300c4621001500e42c240d0105c500a00da0080c4441c0c443c6050203000e410000850f01041102d09010703020305049405012640640d0b60f030301c0b12200300440d9a11150145400c00c046882841da0749000804940c000c1d0750803030060050840d995511031040c040c2d00e082ca00c45488004414500541c103c442d281c0c114000300441c80f81c02410178460301c0a21a081c0a1400381d40c07103c2c0751542c40e00605c41e20b000102c01c0310b810400100700c1008004810015a48901030071200743c4011507403180002c8481c0112812240c146103402d0500c4100440d4140d440c0c2d803a43c0641d1400c2081d9110030f000d0366640a0420080c025030003060302e0480f84030304503100c1988400d5540085000050f60b95907070b01b04c0740d80c24100c0d01a65000d041400403e42c0c00c02e003503000918046a0240e1010890b0403510040c0300e04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 150221106 1250 150219856 150219869
    0x10f020a05100e01090803010b250309031e24050c0a02031e0433050301140123040f140913060207020418060f0b01031a010e03070b041d010501090f 65
    0x302c04000000f90401c0d089496103e801501c2d01707460356181d10b90864a40c0c0306111a812010780d40c1c42014a4126180e624900d650705034513507000191464440846142041091008080e035007400c0b040003e104003e0500500c0d069103004d038060554032400350446e180a030501180b800140403034400d840d80001103940170247c5c42800c129020031045086618050f50b00400001c901d960103100040d100c05003004a0f00c06440c00d10b100405c811081a0b540b03100030302440e9440c484860b6000f001d9401414007a4003020481da0711040d280e11254880026086134021112508030614100400e46c88440390b02c061007412038a0036181d06120822019125825000600707103600810081d0556030f903640f02c030300000000d00c003040a1550a01c0c01e2401020703107850901086280841c9030751194401e208018500c481c000c00b02c00340319007903401951100070101e00306502d849404c031702286048100740580300800d44c11801090407040018215442801604020f040009200c010480751707920104406c100e428 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 150222356 1250 150221106 150221111
    0x30d050f1902030309070906030f02010c02030f07090902031e0303070f1101050115081b090d0c03061d0d020a0b0109050a230604060618050411070b0103050c010f020a0510 75
    0x1503142580c05169208010404444945641690044002c6105112030700a407544680c03914a20b82c200e5a0900000d05502400c07901080154007801402184c00e000400700c0701c0340d0f4070140d49245024241c3d0401c1c9161030720703030041c00c08500301000102c0040307035040780d002110b08a20240e680c0d2400028907140803c6004030710444c1c580d004210600780c010080009100540c1c489006030700070074005002c6000110700314005209401140302c04800254400e03001c5241c581d500d000c10460783d0b0078002c01d0740e01907207503240000090290310070900c8008440502c801c420b00c2c81c55043e418240101c60950079508841c0c1c6400001e17960001a03815500032460000c0c981d22002401e00003810641000082526000f100c2803c2d4060340b00202d10a00c42101c080c82020348804040320144a03082081d120b054517100284224600b03908041508100141e4140c1408002d0b00d41c00c0800e030303007a4000d94141e0412240c4d082d42e035901101e00300b440d481e903000502540307510b540e40c103503a115070039041c0d0985603 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 150223606 1250 150222356 150222367
    0x61603050307050705120703110f120d020909040b100b030708040f030c050a030306090501050406050a090902030307170405010212250c05040e060109051f0e041e060209030f030405030d05 82
    0x60185090790440303608001206d10b913007901615800c007640b021400394041341144a904d4400d0300001222600d10110030302034506001c0c00320000e9400d030091035001c801d0540a1002e40019210404030ad0701c42c130300440e0702c9246400c0072103080d9003084940c0c0240c0c0110100300204180c250f0480030144e04941e0143e9603000110417801c08a502415009000342035000700792480d0180340d07160f00b00720305807038880d08200b2150b40d0b240100b0085034220722034070303403c0381c03c081c81001a00190341c8041c003c1d50010b03059902d41080c1d551049201001080c5001c200303400840c00b030020356070421659080320340d003007481c0c0d252003086074100c42042c84100e49500910b046100190421500c140001c004240242091103051440c02c01a81c80700b400340070358044e462038140010704101d1031003881c3c03c0945d00103c90044050030007070b04042c2e601c4028011f43c0c1c905d80740c0b40104000c48036260122410380c001d210040c0c030f40c81c2010170942014501820b080c050f0b4002c0c00180900e035000b160007075242d440c50514540d500c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 150224856 1250 150223606 150223621
    0x41d04050309090106021b0306060d080d0e2a04020304020f100c060e1510051f05090d03090509100806072003040f0302091b0a03020a021603200616030503 68
    0x18070840c4042030f0425445000010f1240d00000c00b5100786402c40b40c03000d050001d03c0245070f52000704917140c42e809a50601c17500081102200204604105000c001c81c030804100f08082c5040c20343d4881c039230035018108002e844081d6180d10320250b0401100d00713614600703040c0c001803000c0404064035481542ca000100b40d469000c0d5015010580c4d000000b0b103d13050301e0b41d101507180c00100301d070b42d4464689600001c0b6603683d18909002901c030024482c22801c64400120041a0080d040040522104205d104850307070b111403021100511a54076502a2410442800312580c0090414804404043d034188104200810034590051442c07500c81580007407000c3c01d03c410040950540c04a000014003c290222001d40d11000d42e070090368a581c00c0e031982c40c00c182c0a441e20340b0740b44980107410700c007407651140b003a0014001d030101841160103000801c132560b160144240d00854004040d00140f800b0700c074203034608020403038080764000c0c101400d02e010401709040107003000302004030020002d403a0307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 150226106 1250 150224856 150224863
    0x210020a020c0f1c0309052e03050601090b120403110604020a0902090f040e010501081c0206060f060903010c02010e07150801052103030406090516140910081009120203041d0405 78
    0x144c12120102c2a03a030340c25080192072440c403401502e00a0011059052062541c4000c8041481d056190043d9800844504074010200641464100849004002442600f05d00078191038900c3c0c1c0340c100401c0c2010f00d00030340602540340660340d240c0c00000400c00941c2e100d2298400301c0381c5110015a42e00880c000140d0308a00705c03142268403c0c03904482c0c0302c08031030550105061b10074040c1103030b014195528940300c00085032105500141c0c0b0000005845042030030f102200643c001d05414100ba0440000a00b51214a030344480140e6488007131154500303040011500600040050101505c405400140f034290140200c0e806008410340400c4810740724100d21013140355880685e5181e0620740340034005010b01c890261401d01c19041c04044468046c80c0c0f0030111942000303503440c03180a10081c44080e0b8401025174580000000303000170000f5051000349400305010400040c4c1103d50b140042808054a02000842d8414081403011f5050051031481103464004594039680e100d1500d1842c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 150227356 1250 150226106 150226129
    0x90e18010b0a0f03171312050111030c070501051506040603020306120a08040e151e030a0606090b1305011401140c030426011b0509030c04050c04060210020a020c0f 72
    0x20030107180c42c8000749019601d00d06106583c8034004405103d0340e6224071500a0040d030303c0c50603000141d50b10030000112802e8803a0410f0b440340c000400c02c0002c040440d443e5410071034000c0c0c100d1400180110401c0310030310682c0e074072103000841d5038981854140800e00c140030b10b001c1c003001d00d42c0c004081485640d43c000440c0002420b40c0c2198407040319450500d01541051044103241021000820404990348034245007040010705940e80d10709420825000b80b0302142c0806802d401050440008122603008150141104043c04945042d401d024040100034800ba2030f1740d018901001403100710f81d82d82161507000030928190600c000f00008445a901c6038080c410617074400002c001801c60b415a0300e84010071864000a252000241421401e0312401040712607001260b070b20380d181c101d002d400580000c403006070886502001300300100301100c2068030115404800814204006541007080320741d03da248034029818280c2079800a9555140c0c00030707891280e00071643c1c2c0152074851410215 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 150228606 1250 150227356 150227359
    0xa050f06012d0c020d12140403021c110405010b09010906020a020609090601090906081027030f09030204110c01051006020a0b0c0c1903021e0a17130306021801090e18010b 75
    0x610707045c1145040c0300d0310f00682c0c4030400030540506041c20340c0340004060360101c94004d802d098a4138207021a0703441c01510200201e17036802d03038801c0c072848546407440307024040c0c15402007555a178690040003400e03000c442d078029402c55000d40040390050300c03a0401e0341d141d8102650070500c0342e1143c00c0142e44a1442e0340080350010314010002940c540d00050364110140c0b1008200311208031000001034140b841e01c0c1148034880000441e200280c4929032105401600e454a1441a030300d03540018180d600c0550111350148011440c82d10000d030070303c9601c0e04803958031183c5400d20300d8220f0181d250210039502600d0344040343d00081c084000e440c210b8540c3d403000c1090750102c2c0d441800006d800709030a00207030014031070b9800011100e80750b1080300c825683c000e030080100580542d6040a00c4514030003262a000c002c0c00b001c0400ca030703550802800317144200d00150311107090560046505401c07003a61410001c1400301049240403841045400080624160b040585401c0c0054003500030800f40e01d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 150229856 1250 150228606 150228619
    0x708070b0c1902030d150608040314090a081005010f0302031027030c1103070605120a06080d080f060d020d06090c080609030903070b12070c0f0b0a050f06012d0c02 72
    0x1a52099000c0011700321110780580410600c8200140030350800b40900a810124a40f000441d002c04e008003480c0d440c1c885da100c009440e020b60100812421015a840030006502c80f0540c20003041650003428050040098018402851900000e682d40d105404078040e00341e90b0f540303c00381303191441001404480030102541c0e15050504c0c004202b0410030005540301007030072415400385e00c5c000c50801c0840b0320316030303d20782403201002d0203140a4402074810f084440d81d8040c000f402c000144001018010603455107a41480d0803038030885008001010181b0400c4d5254442d00141c1e00c02c01d0542c68142c00010005a10080703207401c50608100d500640d425105080c00c00501101c000000c09c0c8405007901580c260341e5035020307020040e015580c0c1001005445600043c1241d104020040e541c41c0242003032404d5001766199800c0401c420784a078081c00d078a502c100451071008900250708440c3c02c0c41e05003502d40c00c0000d4252443ca201c00c56042121484407040b01451013804a100c0311038000700031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 150231106 1250 150229856 150229897
    0x8040303090f140d08090d110313060801150c02010909050a02070c15030c0206131115041203030b09040201020703061a04020c1509160b13090e07080f01020708070b0c 73
    0x11020114030f520076020144550f0b814800c5036440742940c3c0d80240ca985004041001c2008030a40b10210f003007140e070350300f44000c2c0318146d0f00d105800c90345002003032903495001442d41401601d0507607600301000502440481042c100061340d004007000e0848400748000100d58680d00300d406d008e07100b0740201404041c00040d01143c603e13610300e5007210060040d101001384410350302c6d00340e0b12118202e80c14014006204041004a4030040d04070125907002000d17010b040440d0302d4602c2641c0c000d0f030401924039490051540403d501031081207400c61049680c185030b45400d60001303594011600004102603110441ca0f9035070621803060705000a001801951034105401072995141281800d41c0015440310010031000d00e800b14280b20700303074a150003000320a414036188a02e95800000c003d80e6070541040b0025400b03025102c1d5140d65503846d40900280d915160710b440c40c3c0b140403260080e0b00c0c0d00c100074540c0014451412a29502e500101300d030003503500e54400351158007440c44d42d410301000d141c80 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 150232356 1250 150231106 150231113
    0x31202010c020106050d020904020d020105120f0615040b090d03031b0203071b0b07140a020915040c0306060e0f03070515030108010e0c010c02010309051e030c12130608040303090f 79
    0x8008074200c402d9000b080041d03624002c22810340002d00c00a5000603044001c503002d828800304101c1fa0500605129181910704100b000d81e0580440d880740b190100501171041d50b01e000540007140600340410305082a040050022284c4500c4807100d1144492800003003c0500a400c0560b07a940701301701c6014950b03c0b484d8046d4503540486070031942c54408511840d0000d04800c00002501c0c140029603003480580c1c0e4582031000c94250b07120751184120f641510060b904c1841141c401d25420b82c100c400301002c1c20a01050310f490410000c10b060401105104855119011041c0003004031b81c04600c04840001003404d085080d000b03c2d4009901c4280c4121010081c002103040750190b2000f0010f1203420300301c468a401000c01000e0001e20b0700c0f62100302640c0309402589a030742c010402d40f5840e5440c644801e081e07503100c2e995805aa0008141c214800d9428400c440ca00320015810900d040d03c0b0201c3d0000d445040d0280c0014003454802040906100340d00040300c00303500400c0858141501d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 150233606 1250 150232356 150232361
    0x90e1f0b01021212010509100302040c050c0105090a02013501090501060f030902091b1b0c121506040e28060f021c020a1418010906020307080a0e01030603120201 71
    0xc0440c098424240c0c0c0500c90a0b00c50300300c130f4080c0302d2801400c000764241000c0001c01400a42242e00c06642400080003590315440341038040c201a030be9160340e615581c40c05500b995402840c141090304100c91000160360804003550f0b1405c550040320500140b0800c0880340c22600700041124030b0882000428158440e500143c140d4000d51603650300c0c1c10b2107100803002c1e6400048000d4010301c580d404542c040d00b0300500b1820302034402a20608000303400d81500c00d200500e907810480c0341d0050005640c01c0c2020000441c481c4001700180400d1412000c869240074009480765001c1da54503091030124410900465407244030325460310900d9078000303651002000703010006403007061400003e0000c52143e4400c80f081d02404450400744203440300c2100000750841c00c810000d12500340400726950180000606205c0c0800e00410031404c84a4001171081840e030700890203550042219401298055081c1e807404007251070108011108000100d01070500d541c0000c1441e5000030300034800c0754064 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 150234856 1250 150233606 150233621
    0x171e12070f0b0903030c090f06040b0a02100501170a08071103070f08061e0a0908040801110c060603010921170a020d0b010219020d08280212090604090e1f 68
    0x2c0c8141e003103588a07008003940b00e100a4039004980041000050264100a0b000d0044074000a018074106944c0c1c400b8640180d0050174004011381081c10142c2d180c1e2550b02c030382130141c203042c20b440c07031041c1c0280002580d40c1da0200015140f0500490740c0804c2202d030300c074126408000501901c00b81c0ba9108040d400514650241d40c100e40a401c00144030039840150400004c3c4405400c41400c0c0ca64445040040c000079000f905c50540401001c501807000340150700000400120f86913071810341d4030394035040610251a40303109905203d81000400d24a030150740321400801051240a0b140040c151181070311043d04420140945040003d40010795000e03100c0020341c55000d04c03604403244c0c0120384503803041f0030310680742c40d00f4041040542032420b182d251891003a6440c514203010042052035852110036034401c0300c0070700200780c1c140d1541807110f104484a0344580605140600c40082d00c10700460144901403a6584000041c440342000354881850100f64021807402d10142400050701d0007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 150236106 1250 150234856 150234863
    0xe0402041502060f0702030a0e010c02010201153f02130b0a03061d01111606020c060117070b0313060b0f09040b10080f07061107150c0c171e12070f 65
    0x100005170f08240040101d6a941e030140c0d0301c1621041c3c4500040d1080504100c09a0441d0750b2800400000403100c04200301030f04001107454074203110007840d003031141c8080009007038195a240c01f020490015148548019904890480f0640002c8412100526100900c243d220100c90400800d1050715406042a0800708114031148034200380381034281c5814884054101d10204403848419807090b08400d4902e01c1120007525081195903070924010382a004400d5a1a52a82c0092256001c10118008002c1d8800c00c4d800c2d460302d07801c00781c074641540401410040d15000e580c142d85ea20529480842900100703442140d003010b04140580384000c862031044140303080404210080002500011005004010020141001310403030346c400c074541400070503100309200455032051001c0b4140807100c0c01da0303564201c2000d5040c9524003881c2540503000344c116210094078980000300e4213040d0802c1c084401d00da11003440c90300a140203281d07071380310b10507003000315100080061240000d04906d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 150237356 1250 150236106 150236131
    0xc05010e03160b1b01050f060105030c07140607020601060212030a0b0604050306180c040207050307060f090f1515050609010f270807061701140105040b03090c190b0a0e040204150206 80
    0x81450341117080b181c0c107851020000c00c2d136030001226503110740011a03000d0004068141440241da49101046080e0440d0344041c1d0444010000c400e0381c1040180e004085030703c000e02540c85110041c8000d4400640000e050342e88401262180d51030310701c2120001e10018088429a28088002d840040c008032a464014001d00720866030074503050080d5011990883c006d18a02503180c0c0c0e4400090480c8520044002e888210031008116a40140c0c2c85045c06003c5013100c0180450401d8200e5201403062460034801c11401d000c107440300000c0d1100500b003820035071a000c128500070380307414900000c041c00302084a400010000d0a10000404541001341203c14a5440320800e4680980f002c1003d48606644001003111405590500104800604105180903220384100125a20032501025683d20141d040c40e02401c0c150b404009518903041200704460501101c2c5102d44240041c15040081c003045001542e622036040b18014180c00c0714003280c2c001074060103916030701d0844500c0340840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 150238606 1250 150237356 150237397
    0x1903022b080a120606050322020f030d08150102160b0711040c02030702030c060a0519032a020c010c051b0118090b13050606160303020d090507080c06070c05010e03160b 74
    0x14041d400b51f9002e0550091030302180829035410b960b07600c641c40780990f44240e04e9100c400c2280c40500000182c44105d9071084250b00d808185c107000140e4201100f8110b5109520f0050030041212411080c1c640c0e0825030ba6070380505041c04180b1454808800b0392141c03a080c00c0200e4140c001004150151081c0c0036038140d00c40b070300f0403c00103001e641e40c0b010110341c08000e20011154400d46500e10040035044c00500d81e603000c0007204403040e8084681146204108402102a80400201440100900e807000d0644603554072540c8501c0440190344800150b220100314580c000c0341e602009104040d10441030641d03420080014061341c400301e40c0100884103a0740c40500440c0500c61145030054089840c1c00032003140541c200c03c00310015000c155090010f03070401c484902a0b584028007800003011203c0c10045054200b0150b183c03610312401040060000080d809110041194000d08140000c6c0c03038010b000c2414a003198a4451002e8261080403800c84403400280c00c2c01e41001c0814501c50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 150239856 1250 150238606 150238619
    0x2190608190e03040b0903150106080105040f0e0d0806031504060912080c0909040c09021207090522200304050303010e06060702011b020a09020c03091903022b080a1206 74
    0x21142d9401d0210a03810400080c003030305260400400680700060100d1700b00c100c0c500c40c0c080c540d14080c0c0040e00081c44000c0100314030325040c0601100380d150744204110480000d0910f565a4480303012440900c460140042c0441d0340a0116034400345001c2008106841c1a1410200078409c548048500340e0401a80e001c01911640c44548524a5001854500740f6003c7c1080b140e260010000c8580c0703007034800c02184400050028201020f980006a002820541e1010340820380ca50410390241001c0180708014819800c051409040030030400161801e0248458048544030319000c80c0b240d0000040c0010000000000c40c121201500403044548440d0100b10b8030b8070031881e0190015187c3c4481110200007083c8041c07110744000c0409440c15900d40c214000e0b80c002c01c070b07603820b0350308041340d0260641011140c120116449020142050b820b5078005003006034090224036003600002034405021200549542031641c108100c07607207038590104000c1150710f81c00b4154280c02d05110001854 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 150241106 1250 150239856 150239861
    0x110106081207051504170f090d0303090506060910030b060303091002070e0105030303010f0312021c03140f010b030106050f092d0a0612020f04030602040306060533070219060819 78
    0x646e806111052001e161101d0711070f4582100400c1d001c4200104003821250780caa8190802551203510013003405140e504020703042050060141d8014003d0300200510100c20255210949600c080c84e4030203521b8520100c0c0c554000c00100d1078101346401c0c078190710b03d038000508004940d505010b00c1c06680e00e0f102410340ba80821300c1041c0381c810013444c0c28000581e0389003a48211810510499040c3d884601e10000d140c288403c01c1e1012030303a11066124071030300816813241e0001c0c81002d80000c0f9450304204003060b100500c981e070200040401c032800601100c20803035038100402000142a4510680c00e9015801e40d408841007200d992000440541869040d140843c3c0c0c1644541e0a0155400d104001940c0709244004194800300303c0800000d000788040c20203180600c1000900504100500c40810500c001c407001030340c031200354145c0c2c0350550f182c1c0400207414400320a4a401d481e1002c988079119800d01c0e020910381c283c60220b40c642e4020f0419100322071039100c444241328264190800c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 150242356 1250 150241106 150241111
    0x90a020703051801111608070e010b070201140f03160e0103050906010306051e090706020105070504180b040b060c0109150c1b0503070c06050901030b0105090f011101060812070515 79
    0x420420f1004101c5800e1210080c62074007010b040c010050101c2c0d603c00c500b01b1400c41c100c59a50f40c10440305100c0440100070503000f60901030815001ca5040c44072640c0c40e170180b40402410055581812031221540c00180c0d6000780211030f170304ea11707414908214884400313010042c0d000600550485a200c1d072082c010b45028403011005003190740d095888480123060002c08000002040120690807100c002c0051071082044001a20516003032520090035550f002e000c030b404000c400c1c80b09100c032501d007104070014284521000500914030b10040780151598108003a03000801041c048103003681034100c0c684180c0301d59280c4d9010802d103c1044129034030b8a11810002d02d6800d00d03903450103500c1070040c80c030b980214102c0b410550341d9500c103001101c03650001c0703001480100e00080156054010001d0088003420941e040c540c107840031070804900280700e01d0400c202c048130001c0700c210a40c085400b80c4030090603164903140344612503060741c1c08a10100d445200760b1220903040e1004120150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 150243606 1250 150242356 150242363
    0x3060f0f050f0a38070606030506151005030a110c0c03070e10030209060f031c021501180504020112181a01050109051002010b0a1d0906060112020d0906090c05090a0207 74
    0x101300a1015074840c02da04040702c682c9034210001910210038921000030f00b484038030906000c070300300e0304501d002414860064468009112400501c2625655112080c0d0610800b450200e44035074490308120003074240c5072615007000c003001400c4c41b5071140120b11400a46c20a40403210026900c05031410000412121b406004007031820620052034290b0a250700410010803c41302c002c40c03040042d00380070030000440340d14041209045142501440300d0407021026410595aa62403d802c004158083e00818510039a03070f00001021a8001c00411414800d0320718100520081c002600d07160314a190f40030f464030000014000182c9001031a0281070341c0040c4e40c0c18040340c2c6030038180480e08072140300c03410a654a030320a4903085d444800c4058010100c444011140803141c0c004c1d02c0381040003500030701a0b504032200700082640c006c141d2031050740d041140180d0710050ba03c0c0d424018481e814000742070b942885200414404810340c84802c2e90f41c1283e43e0b2480da200c052542c0100d10070841c004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 150244856 1250 150243606 150243629
    0x10507140a120b060f190c030c0f03020a14070f120f03140409020a1e03050f0402060906040e010902030403030c0203070c0b031003060c0314130314030703060f0f050f0a 74
    0x41460611440141c500000c010b0740110f284400c010018000390810704010740b00120118078400404940408018881e43c0c50030442c1012045807401070440c003050201409010a00f5600800c051081007880742180e08405502440080140e41a48030005442400c038080454070012a8a0410740400c0c002141d021107000d101e1280c990b0140d072142e00018241c070002e001408000740160940c0001d010b07200c980c2d0b6816071142d44c0c0141c80c9982c40c1503c6070500400d46818108200b54003100081074205070100c9034241c940d05c10900045030703407045401c24903a0101c402e00008031015180c000d0f41c000d910035142400555102c400803079480c01968805001c1d911b408000b0442c40007060020340c4c21640100c01c1b10300b00d03501c0362580c4040c0d03200d034021100081d50750348003821034a5500a10302e802c41c4954445410382d81c0103440052102e002c5256000c01010000086641c9a0081c0c2c80000104512408040e540e95610480b851005180c4103590003800714102c13004003480c0003448503040d04e0080152 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 150246106 1250 150244856 150244867
    0x301150609080f211303080307120b0603040609061b020a05071502060f09010b0405091506030f070b130e13120e06190903200a0504140420060304080c01050714 70
    0x408180c4e0b4058a00300341c0c0013000c10400071010806142903010714022200c0e43c7c0e032810301c284000c200102491f8135444107440c00a03001159034580080381e0304180c0040c07002c124910f290500c1300c01449007010000e003071040030565105154002c100d0f0324083d4000d20654070300300d0f070702c450f55101845584000740040e0842c00002c0c00e03000380c504030a41c011500f5800020780c85114400308080b28019528281d903584910b07507803404401c02540440e800340d02035025203954050303421304554944287c00340c0c200d131420218007122000078020001c4e00070005410b5500c141e040036a40e94192099094040c3c0709404102d500304941409080064542040500b0852030000c0140060406200314003090301001b03102140000842d405807524400d58202c0420b0002004001040041d80344082d4410350040d418503400b642c1088042540039407041d00300c1e075120364171881100003d452030101c0c83c0c403951091001c82030105028604001e08035004005000308600e03200c0040c151040d1410000074807104008016 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 150247356 1250 150246106 150246133
    0xf0601150203040801050f01181a010309141b19050904080706150806090d021204030f0c12050c040b033c030706090302010b0d032c0301150609080f 65
    0x200300c92040d03441601c1c28151691403c60a40d141500e040100c2c59541c401403000040c01101001d000e402081b042001d4400341e44d071140c01c2400001028145541e541082c01032090060b160010b0003943c105940e000810041e40064003804040e1036400b44000d0342c070b000d500c4240d02060205690005284075081d07078850313030340d503082d944540d8084810790b8039041d02080d045020091480a4208440541024070300460594601050322581c140bc5600c400350070388800d420300d400c40f01030b80d0304184692840300311410711183c030b110780d0f522150380310b0b050000b01c0c2c051200100301113940c2c50084030244000f030711040030980c1e074007403401c142910004000b0008200c0480707031000004440034000c4c3d226144a9204807030b03003103400025043c0c900948035080502015820711800400d000b08a4810310064a140c4006060701121803036400780c3c02200403140400c0c8039641900d440303400d0040c024081404aaa0400c01007035641c46480007040300320a02140000010039292a07140b1a0700041180b00403218 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 150248606 1250 150247356 150247379
    0x1401050f0d0f0908120f060604210c05090709091d0c010305041b0810050a020a140f160305090f040203150405060d0c0806091005011d04060b0402031006110f0601 71
    0x1e128125030354a00343d0000a008401410000350515400080e915000301c0e802135800d4002c1503184078100030001032219200f5203400c07a080c44041011a01d04001d00e107000045d0540300e030130650303001401008002c182580000d4100a81c0c41206d000d22100e900c810070f01a01d911150400b81454001012103030031940301743d11a40d481400303044507154181d14040510308031800c40e04550000c0d00000f40f010a000d0f0f5500556030882142081140b800f441c2480040ca02c061003107035129503540004284508030300400c00e907110221811541c001002991070050b120303901107140180941e0094000300880d1a2520036030b4414000314800b450816a032030100801000010020356008054004110100c1c415008075805001c01d40010242c07401c00d4042c0d41d19110508004240d81414600188810718500d259490030045040b0111100c2e01d03649088405000d450240c00e030400d01c0441000b0742d421708110268101e40c95600e980b41e080039800398003a06c0d0100144003040540c00178004120912100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 150249856 1250 150248606 150248621
    0xb0102010b2b02100207030615030b041514270a0b06060d0f0e01050f0906070e090403121b0e030102040e040b180307050102090108090d0207090b0f060408071401050f0d 74
    0x104005009200e50000300b50040311201e031340c0140d024100034400c020740b0380b190015403801050003001803480c6a03110038810304002c00092944e151051443d4030a42c0603082802040520400b2000520302000c42000d15503803014030074a182c1c0403080240c404000861807600c000d8000944d90f07000d503280418408a40e009002d10008680d0315064100c4044851090040c100e5000c0004645400c0c012105244520b024210030000d811007410304c0760080c2c101081008402068642c0c4840da9210308003a164441c0d10f003141a03010f4206400100e494174603100c844804401515903002190340c03981410f080b0702130f80c0a403484410444001c034001c80ca082c520142c1c08955000d004076840704070341d074a44c01c5402c80c200c211703480da401140c00c1800b5a0802a4240d010b400f40300101405100e014000b03503101c02c02c0c03003100c0b1a1651803140705080e803940c4607400072241c4044d01d0180d0707856032850802c0d503034003035446015801c03242c0d030100340500e6204078211124090004c585508020001c01040f0042101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 150251106 1250 150249856 150249919
    0x110c0f0a0909050c01081608010504050601050d0911010f0e0307090908040815100509070e040e0715090801060e060d08031302090c030f0604020c2a0402040b0309010b0102010b 77
    0x1045400030724606280104400188a1005060103229aa001400c3c1c8a00581030140060b42c201c00b0b180f0041c2d010000c1c504682d021030300800c4640300d020050340c80d0310940034101440da0400e00d200003403080300102c80d100e0710001c2e0303240c5204034030402c0d04031106511a18580c1e4141c014801c10044400c854001e036040b01d0107454000e242030340c1d1f4101c05107030020868116a10040f41320410611407900d070b0007070004200545c1c1d04507aa00e030005000b048030040c8440c941c0f04964a00c10119000e00410669000d84160b101d00070703600300d9800d00038000700000d00c0f402110b03600b0041301281584102c82c140307028000c0503100d44d800004642d51f50382c080d000240a584000d0361200c0c490702503642c4000c1d4a000e540c40b1201c044d980d0a094401821480c00203005ea03009900400100c6c0011030300040e2052030ba84040c40e40300d0820003000c00035801b8810f4455180d0300500205000c5050b8202800131401500908001c00080c44071070016800d8a5090282039400790081034800c0e081800000070000341145e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 150252356 1250 150251106 150251119
    0x909090c03070b130b0a020d030e12222105070f030305070f0303150b041508190c0e03030a020d02060f010f030b0a0f06060201050a290d050a0510090210110c0f 70
    0x200d410b132802c429004001c180c030062307000068519026415100741070060500602422401903860319000d094030804602999149103d0202d00d03901b0314200c0228054211030700b202040c102040104c107801d0545440030b13601c40c0100100010518021451581100c5c1d045d04d0b501c0c1403802a840701c005034240320006805054807140d4800700603040b05800c0300034000e0700c3c2c0210f80740ca003030655135050100059265018000700005105401e42c0380d2000302c0d00100c0340386011460b680b0158049403041a040500381d098800032401e07560340f0380c000c0b450f01001e103520b50071613009079600000090505000e10601c0c040f0071845400f480407a0f000300d100360b03201507001000b14012504880000860711a9800f580050355540140800f61106001da4464505030000d503d8199400c0310102d882e1801c0400802d20401060141d14100001480104d81c031541084c10341d202c414118071450041c28405004a100d00594000c1006507405162070202c41d17001d400003042154410000d128520400421095201c01c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 150253606 1250 150252356 150252359
    0x30e030405090f1e041209080d091a04030203060f09010e0307080d2003090a0c05060a050f13030b010f030506070c0506060d080f0c01061403120a050d1e020909090c03070b13 76
    0x4c00c0704044900461113803050307121202054000610548198101c08819000050365003c00c50340400d19400766a0070040107101201e958160100901c21a031000390103000d008200010045d400d00076901c20030300c0c1c0c4000e100300ea0324019034940300d216110000704028418416101d1607001688030030f0455004500f040002a0b03000c5e040c0d031450f041264001c4156000107901d00400940030f0000000742800c0e2506d6060003406a0040d00c2ca0066408a041100c804908050300000300c022400085030082c524071815612a45c9584a081503400190b5040c461040410501480343e81c0c2001801d8000c40508841c0e1500d408000256440303005c240c409540074404080a141d2940c010205841d4a4000280c500e18240d1411080c0388001140e52007500a24030807112441c1c003030111203000c031142c504203544030300503888080100140d280c0010f0101950001c8469100302e03500030003110341d04a0310b00386030350f55009040b80c0e24807074044140d070950800d203001c010a00703540d0040c089104a0804280400303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 150254856 1250 150253606 150253651
    0x40b0a02070218010e0403030c0e0117040503130305070801050108030a090b0c0a1b0303020601050d0302030427020706020403051506060a0c020402091306060801060c03020303150d06050103080307030e030405090f 93
    0xf02070b0013020141d80c04105000405406101d00013885410b4245070504900c0c0400180030300001c6031501101c003001c0750000f010400180100c8040090381c88085001540b41e040c00317039550040d401980480c0d0710f024000f058100c400401da644455603552003140303150420340451101e0b040b0641d0540244100040800095200180b026030030300001207030803000c0d03e0b60600a18040069200c1070144040140710b0340031a9002c001c07141a9442112440154440c106c00700440c00001d56102c110350748081802c02c20070845800401c2124020f90403a2844414002c00740c903128404e603035256002d4020841404030b10b01844207a003006000820060420403800302043c40010150841640b950381e0f00c0e0144410358000c0301c45409000e05140c0086202481c1d60045c1d6244406041403003500d00240c0a4a200d17a640100b002003254003050600c01ca5942c1d141444843d0401e88450300030070f0800101141d03c900000030b98044600007410241036031140040300030384c90b9002d0b08000c00707003600300d00b03040d0300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 150256106 1250 150254856 150254899
    0x901031a04060b09150c03030f070207080709060e06030303060d0201180905040b04021804030c0b19020d3c05150603070f030b040b010c120918050402040b0405040b0a020702 76
    0x5201c083c001c2d82d690440d0000304030128503010780c0d15280e05824420030017605000000e803075010b1302640b03101103644c40d5000164036040f0154854040c5200f44d100114500141d5000710341121184c020301e04181c0c1300d54080503201c1c04216891600600d511112601640c07203494112020012121a000a540c99407502d505482c0d0413a4140d40500c4d42d407050004600700201d050660480440c030000c401d08050750024005c0000c514080c1000b40c012020400000d24403003828000c8050f0541150383c0c00762402100050b041e8280715001c6842c0c000c00c02c11041d40d0f003e15440039044a6107031130401c000b0440c0304a000305006003c060015040402c4001a030711303000001d5000c4d800c0b81e00c0300300079541402001820f81d1030403504540540d080072624650790342c0060008214031f42c0a00485210720020600700c0300001c0ca580406504070010b0100e8800e4207a503480745001d0f600a0340c00780005544d1a0074030041e5401540c0050070000c403080010b0135070f00207602800d6160700c01450400582c1c864102a40c1e03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 150257356 1250 150256106 150256109
    0x13140411130b010519091a090f04050601050403080306040212090a0c050609010f034d07120c03030e0106230a0f120c0503070b0a080f0405030a0c020303091c0506010603050c0901031a0406 82
    0x904420018502da049c0c0313040c040c0f0210001e400c660034803084c60100c0000b0564016840010506038003c0042605e5544980545004400c0001080380d24581800140d6464442100940b4044100707040403556082580445601c0301040c1c40b0030241d5100440110014402c08800742240d0b8031203090a2259080c1c0070780d40003201e202002d054010061661103000350820b855040358401c40400400c400584110410304600e613070340c2444a010152070500760b010f011210f0240c0d8180d4a800c00c0460150042216443d001d100c41100303a980c8200001480510486409041e5068604500c2080984009200751103490310403210050034555580119183c0305613500038201034100424611042030f031015640b07a1141060300503818609058941d0f5890703201c1d03408034200b0080811102c00954508004a83d1202009441146205180000441112482c001c00c6406001700e20001611510a0051901600582c0307050351030101c0d48001900180182c00041c00c3d540d400300b031200c00e5070740c95200f03110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 150258606 1250 150257356 150257399
    0x70302030a090b070f03270b0a0f0c0203030711150a0807030e01090b15010302041703090f0306090c060702040e1f200913140411130b01051909 63
    0x40d154030781c260001d82500002d400009140f081446108046980790740784100203a01800d0090500c1d501d8a02c50300f13003c51400900f842c001000d40c000480413201401090700b00442d0759100c0c84041001e00440e21220341f0725000e54190701c107100c94800300d210f9038910700007100001e0120000782168400e041301078101205010100d03c041c010081850307010301811841c480d40b10001c2280c80c4803590f405001e0240988452a00b410140882c0d980364040d60454001d051800900642c1c0740305590300507a00d520060040d80140701100b1401c2c46410300042960245d421513010300f200d0070808003405400d400881c4140c0c1d006441d010301c0348036420144001c404203106400e410454444a0681105880a0700e04000011170001c045c55031034560f8100f0b450308150111040c0511840c25000360300500480c0d000344c95000380103003c3c03100b00010b90700606c4e06000b050700c011544001102140b0120b079450860980482c03410400d491070454a0940359034455a24104489034544421100c07600c808a0080305 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 150259856 1250 150258606 150258613
    0x91703120c0306030a0b06040f0e071806050603010902070515090a030f0f0203041a040302060319110301051507032007050a0f050a26120715060e0c0915070302 70
    0x3801900d8104a901c0358810700e010b899410308102103992908009409009403a40001140507503440340c110303c00b07544c541c00e028000310400300489900c0e402948100703150341d07585403013072003c14545014040442e44004c118074110303883c24414501070362290004544601800d01030031030a45200d4003c0c0d0185540070b0081500c5000b031316020b0b10030595a1288028000180c130030413200742c1e0001c1201c080c0c41000c03544280080c100b60065aa41c01103420080d441500442080030b04400805a80039000d0b1400c02401070441d01903540070a88000c1c090036400407640d4184040000e82d0a00070300c0310501ca40b400000280c42c00544082549640030104510740200b0710400443ca0f21004240213052601c4100c0704261800000402c2d0201a10a01a4207442c6000d010b8042420a1482e540f1110b03d10640d141060b104491b050b855005100c100e40421300161241c880303950506c100019242040342c841e0130384c0c45074001d10b20190400c418050f4841c100d400d10b031380940000790250040c07921a8008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 150261106 1250 150259856 150259867
    0xf020a090b10110d110f121201140109052b06050a0b040204150c05150f06010318110112020d06180621061a09160810030b010e07091703 60
    0x42100520724408010100f000d10024403001d0500820b0080a801440c00c01c01c04038410001c200e8103010104d400d480c02d9000d40384400811010620082040b00201d0181c101580c0c1c86072081100318020068050000326001814020303801c145000c0d01070784000d10388400520b01071000d08900281e41200485505031100c043c80003124050085480a0030121019800c0c18288002803540c0f084e40740540d0100035000070b0f0340d000d100e424800510503806a85501d8039524055034410004a020307035180d40064901020f01c0d4a21090351403404000b54402074070040300e04000c0c011108084c500d40c803a075606a00700101416a10b142c42150010050701d0b00404101c00030b00340b0700c3e007201c40035408030101680d02700551a080341c0d03481301302a01c90781c020b000058590f100c100500401c1d5105114541010751030091000180010707900b52151243c5644042442d609d40c840604c034209a8400181030200000051000340c20700754001d80d005203245054407410f59900d1000e10701d44071075584217455800000300e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 150262356 1250 150261106 150261109
    0xa05071b061e1107080a0e0303180306060d030f030e07090903020c041802060a030908040e1f0f062102070803010308040806010626073005010e041e0f020a090b 70
    0x120a038608510321000c003c82401c51003052035912954100034460300300025200301d9940204262140d000c005000c0700e8075030f80c4281c4045a001000c07102c1310701c203100b000005a036510300075107482210365159484680e4500075107c1a0090040ca000c02d4015024a03800030403103038201c0c451880d589000754002c104603a9000180300454100b400c403900700107a03106429025071034520444004605a1900145101c03031810149400d01a6401c424110100c0105201c0080880038014020048081e02000400d03075a80d400f80d11501c0b01d12800700400c0c04510003c0c8800303c588030400c160002c001001d850b1400075039a95402d640260008c488070300c008581800310764000c0108901411581c00e001c0d00d40704130109440300324288106412641a8803d000601d04d6100c0c5038400603d23000c8200116110360603100b5107003c6182550a01c0d40d00346000000601506a5800d0b140507907008410200038012007035088010f00341103401038440d40030040003100181c031014664030040150110001c0c41310507880 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 150263606 1250 150262356 150262391
    0x1503140603010605090f180a030302191106012c0112030906050f120901090209091f09081b03130303090905070503040332070b01060212070b0a05071b06 67
    0x1000c040c040da24110081c0020303100d100740d01350400c040d40315103c0540e4400c140d0814001c80c40d0010760b2107000b8003c00204044c1c050300507080c95001c401d060441c1a2643d402107039116981d05a0400940c400c00040100030061a0340707001c00043c5107004030120f500904010903100d401c0e4020220300326264041303400d040e4030000c81001341c0701d6482d1051424542c1c1900c1e040d075014000b28203120401e12004540311950950149092030b9020380300f00030b05c2c900743c040580c0b65031200a46240c03c442071100e0002d400454420b1084a9901100040c1410708100010282c900c41013103000441c40100000c80801d120030318940015440782d03a59180050804002109440c0058001000c1c40340038800c6c000026008041016108080140ca020902c1841009a2043c0c00001202020000014110140001e911043d81030f662030350200c0d82076082803040401c00d880754210191850500101041d051901600510741107250f6103800b503408084a01550108107468100b164440e65407400383c0e00c03005280 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 150264856 1250 150263606 150263611
    0xd090f141c02030301090c030b040507081803040b030c1b070e0901150b03040204091b0603020408150702060c0c010621030201050601080108030909041a0429060a03110109150314 78
    0x40910740940c0300c0c403103000c0c0d80c0e4001809805c00b000d8a42c04290b00c260310036403103a242440010824030042c02e09a002401c0c4244c03e8420115208040d11683c42204000044408540940c10a5455940d41c441070000e207800a01c9074010501d1404802802d42340c08001d100c0180140c040d00d05100d0800c203040c0d50031504080038504070701c59400800c0000000040c00c1d00d034000c2d01030b40c0105003600d480c9000001142d905042109801100e400811f03503d60503400740c01034512440480304801c1e8403081d09070756035030100ca910b0b0069205400050f551440240503007896410f06c00041076482d200c180000e0502180035400f0401585036000100f4141d090049a811250038203000c1903950414040c146c892060005440c01100948042010031a62030404104d40f031114080020504052814208000d626042c0c2000c41c01d03580c03030f0701404028604020b4001d150080c82e11010500d15030720902d90840070f1074101d0601c103c2840020795810001c0385114840c1c0e059070001103c440001d440040c03614003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 150266106 1250 150264856 150264883
    0xa081203012c010326033d03170d09060c0215150d050304050405101503060b090d240507030e070b0304030503091029010305090a020103020d090f14 65
    0x207290500755100400b801a60540f034100c00151050060741710f60ba06a00d0020201071601d250010130805414a203080c0100e09010030300130410000300201480c1e280c4880c0031154940c14207007032420800210b8403040214010030080c291750070141d410312100101c50b18940c0540d2020386502080b9942070303040c000450b402914480c000d00e9030520f2001c542000a404103054002d4100000241c14460200295001000010030900513071414203d00c41d04000b0034891050b10003040c200584d1740a00a0085605407900c800803541044000010440742c1285007106640c0c41c00206001001c1c1115a00032009010140102041c40d08019400504850741c0b000b840060f83c0024609103c0700010104483e001901460304586a40340c40721070138108103401031180c40040c5001c1000903000b02d032284ca007540309481500c0c006281c05200047d01900c008403000304032038010783c50a10056009a0103040f910030360090018445420303680d41c0710820007024060310344401d08604e5140300d560412450313242204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 150267356 1250 150266106 150266159
    0x1508030703080106110a0501060f030c060206091902010c0f0b0412170c0304060e06040309030b01050105160f050309060d050a0506031615180b0a110d090b03060a08120301 75
    0xa141c07401003400c1c0c03040c0981c0c800c012410101c002c0c0040200282d20800350454001c0101c690b6801080d290781e0401d200881c1c0c070644140b00041c0a50005c2050fa104200c0000501101d90f40e241034107540300c100d00000c0381804414079001e004100242e110100152040e03134544102d0a150615406140782c24040d01c00308450711440c0d2050403421010190005181046c894407a20307980740010241c0f9203c40e50760b001d481400c0c200f0051507446494402140d00078040e800070b99880e0401142c491140c81500c488980482d50110b00095110407544682d60160068038100440301c40040e05a60200380b41095480c4c4503414000c00500030f1080a411000480c02003002d00001c01644002b0000d81c0700c1c00300459150350520f42c1041c051410281100c8141c2100101c00380c0b241c6e1101203039040301d1909800107100003c41e45e40d84100081100003991161076100c0814034000e0f40404950000b4040c98116071101400146010100701901c0000190001300e81ca9604200000b11822414860001c00c0c04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 150268606 1250 150267356 150267367
    0x13110a0501020307140a02030d051908060604060809010b040203010902090102010509071a07030306051c060c17160c020a03050102041d27010b03061602120705030a0507051f150803 79
    0x2e800000301c5007825806407242c039180c110000c0d814200005004065098001c0031310001000d40c0c42401440e004030060100403007032881140844540d84103e400b40d410840802c800d101c507a0107200e00580c0040418004030b0100b0780b00c004a000d07030f082a4002c030015900410a40007642c0c0a020302d0b540102054000d0016600d00300e010403982c1ca210244401c0240001052405d041c807903000039002c0c010250240113061058a0920780003000c1d54030035102e0130300c1c0c1940800c0081c41190115220b0070708420065050f00c552060f040c0707803104407260a007408046442080142ca481c40a4001540160001030b03c45203000d40d00b0b00391940790411400c1c010002020010041d40d503400c0b500044100100101030b03c210318480305c1c01410f45529440d8188658004c10101c007008074210030b2407407199400d84042c58110703140281e440c00f5059000708240c00500070140402e2289006d080d15078080c0d000c954804003d030740000100f05040b811140c180d92144541454010706070320000003041031100562608 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 150269856 1250 150268606 150268609
    0x3010e120301150e1309020117070503040b0f04020306180c0a120b010812040b0d020d29030a030509040506010507020a0603020c061501050706090c15050d0b0103140114040207060513110a05 83
    0x1c0c40c940100c17601103559403240c0c00c2907912509100030301d05042070880110b420845006480c580003201c017109d1021141000981065000081d2805141c0c094010903c40d1224101c2c2e41102c2c2100700800810720800401c131520b0365680d01200010080080c03c002c40b03032503909004480003416041001c05074004800c3d40211303c40c031002c42d41141c140e90051b6071201801c0c0b02100c0a44640c0b891a120503082c0300c4c6c04514103121200444003031030325502c80400032040c41c00707064a8000080011303012401c244058020f60600b40c0040d0b030700050514140e480e007038440d80000d40c3c0e0901500113800080d03000c182c0f00d00c0c0080401c07400303800c0b004c0510b090b0f094260b582d00003062031044810040c02c00741c40340000c400300822518840003400d01c43d0410b14006070103080081c410313000b0185040506040901072030955000c1d01c10401d0b94080b518001280343c2c00c10300310032202005200f00d80d0b00701c0d03420018040420b48502c1160700034110b10000c00c841035101d00300340b06010712050903540304880403141007266 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 150271106 1250 150269856 150269869
    0x106050312070f0519110a061805040f0626010b010e06030103110102070302040218030105010b07020f06160209040f022404210510060e0a020307120b03010e120301150e 74
    0x51070b91100f4a005141e8980c42d0050074030804c001c0407941440c000300701804000c408210380398545810b60764a42c9040d42c0702011a540c408900c074040110b00c0c00e0030140507504041c2c07c2604c50305007001001c0780c8141d4522162446107040352030680c403c945507412001100c420b010f0010000001d281c070600c4400c1307120000d50140b00601c002007101040303078268180d6900920001c0020741d0000c00844d2625800c4841c0143c81c480900300602c81d528082c000b24071021040c0689100e5500540007030040c074408410702405500c149a00351024901103550700041c2d6614210b40d11480c4100b0142c6e40d502c050b8414000c0c003201c618207045d5451101ca1003a241280d460b020303030b000c440415603c803100108800411207900c0c03010740c024025000780345452070003004c1a0041005c568111101240310b94413102078101f240001d4520740e000440c801708084182001d90000d80c08032600800000e05006c1a03004a0f1401078002d201305600780020004000c2c08103041d1040040e0000c6090859105009070b000070031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 150272356 1250 150271106 150271117
    0x61005061803010e070e011403071208030705040b040306060f090516080c0706060807083a09090c1112040608010308030a06030804090501090c0504050f012d0e030106050312 76
    0x40c11001c928000025581c250010306a280b00308040e034002903121011848261030900418103072032108050403059050000d074070740841340e121040c9410740d2455502d0000c0ba80c0060810320811034180008a02101800c00a2000350f00c120300000303119181405070400c0d502d20794070401216140c10b04020038204100307100c1815140500d0b001403a9914800c4445541c091044040c100d1483c0c00c01c0414540c00c005840b0701500c101c68101c0d040489030000700203e50481d01d145940501000100e41c1940d040c400e1550921017042c00c00707a8200303851720500000c4072000382c44480012040800203482480a0110410192001d25428507103400d100c80903002c0201844000c003440800800034980e0001c95214401440d400000303565a1940c2c0c41c00309000e06020300880b60441d00c2c00f24104400b42c0a139046a0484901030042c1d06504607020041d20060031603440100c284409245c0c000081c00c4040059801e0704194481c1840041c04509160071910160401c60180c0d109032400d14000420100713880c2c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 150273606 1250 150272356 150272377
    0x51615020d0f0510080a030504060e040b040e010504020a060e0f01050313020621090312010501110a022d0904030206011203020c090115080a0b0f01031119050c06100506 74
    0x1a28021040514024800d022008885925100007900da585181e0410350051100d0180341c0314080c1c590441e2611454401c8004000c180300f04407c1042c24095544440302c090000c00c001030440040000c03500303031000e0350316104290755074030f04102c110321b090f00c241300c007518591401010391011640491840c500300005a414010044009138a2440706100700083d50ba001d030541e83c0305c5184001441801c0c0c000d0540b0701200d03800200080788000000f05075a205880481e420708141d1814005666100403136903050410300664600e04090703141d403003003802c04501e0803c07030907080401295402444216080b00620032540032041c080803e900042d11410368821074000e8002142a10b000c0e80751190105900c0d0300049280000100d2540c460346030a940c82c10381c2c6403100d080c0c0d03030044032400f01ea110544041d807000310030224003540d51090f8064244090403004041ca0807030b224140800411002e142080003d000265580105405100c2142c100078681280202c0e02d0604000030f01d28040e030701451 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 150274856 1250 150273606 150273623
    0x305100f15032418080a0807030b01021e0313030507090e030403050705150705060a0c0e03030304050d0807020f0f07260604151107030c03020d020d0909020f09060310080d0516 77
    0x4400d49003944d4020500400748803c1c0d1680700341c0038a40100703142c00003d00f2034003045920b0002580c050090145c01d20280e41640078120310f0303142c0036003030301c010140c0880101217100c203202840111100c90006005140101d00410390300d0700d45508902a03c00c0e540c0404025002403100f040020790004000f4180c4404031050400d482e56102d000440d4024098081c103e4402c10b400e00000c040c96500000480701c0e00ea40f41c0d80e2448610051541c0d0f031105450080080e4021038881074054401e58650313400c40203510542c0c1d840445030710780b01e1400c66138441003502074000d0002005801c0c05030703056038915158000f846031310000e494196500d078440200007910448161807014402c03901d50f8071000310907000d000040e4070f402d054140101381c8101b480d0110003620a0300c40e103901043c00041e00c112500040c0c0d4030100c105080c0641e110281d0030440080300d10500c1071294408a0f41c909e000346100e0345035000f102c1201c40c070705101d082c0f62156005500d800e00108002e000ca003940071403021400c00e900840301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 150276106 1250 150274856 150274913
    0x50612030720060403030c02100c1a07020f011d100507020723060a020109170301050a0909020d0204060810050f01050108070c150c030b0f0402030f1303090305100f1503 74
    0xa910302d0803104800940c0700300001808010160072400b00b1a026000b60303029034040a4440c07080d0345036003511201400410740071400c10400c0002d00056a8812100e205980c04046008040d0303007940c01d4601204205010038034160000d21081080a00401e407591060210741842000a9125030250140d0034040e9000d2001c00300e110a004100d18207040007070301461ba6904841d900034001c00034404116000d0410303040c20755401035000d050300d040c3c0311300400800110b1b1602c07071030f10000d044102d012a003121011403400301680d0b0b2442040d0041030086c0290945006c14106201101d00090082c11800c59000060150340da10002c016403050a074100b0940d015598104500d0203ca9442c814044a0070300804101455054001c42d8500c5410f545104907440320808100581c003040741c5802c1d01e82c5500d40007070441c88003202201d840300d000e4103044c440c0c25100d481d16424004100c1c0007516180d2034a40ca442d9181041c880e20031840c04c040300c900101400c40d0343d03052480e207030404032500080c0784190 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 150277356 1250 150276106 150276143
    0x1030b09280c170907051806030105060d1218030206030c0702090703020301060207030b0c1e0c0c01020a02030a020f06071403090a0503061009150f0f090501080615150c150a0506120307 81
    0x4000902002041d4042961887c0c01840d8610001c989480c0a5401c0c000030850360b040060014102c9070380454030820204e03000c8000c6451710070780341c0750120f800d402c0d04c000400740e00d403d001580501c5543d5001a43c0b40b03040e0041c40700100003d80f0384000c1610400042040540c0401c22000b0340398004503400d065260240091068020700b1051244003800241880350010f0150080405a040001b0743e4486641c5c04016a00c8490002c8c0194241d04941a40b00052030240a2000c1a80b001403410f41029a01e8546861940a821541c00150300001d00758002d4074160706084001c2c01c04800404a03860109070301d100b40c0450744105070840352280300c40300954042e40c048102401c0041c1e40502c45030744c1d6058410303841d1028441c4e440a07520f03200011440d10b00104c1c51622694003400c10503051034001090003080072882d0003541003588103102d009030b4107005110b40400b0082e207c80101003411300001c440100c44000d40020710815900321230694040c0044242c649464021034151418a0200c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 150278606 1250 150277356 150277363
    0xc0d020f190905030f011a191208070c05060903030d0c0912051e0118030c24051006030b0d030c06060b0c060a060608060a0e0601030b09280c1709 64
    0x248008007004091070306005031903101515004460301203040f150b42c20003c00300d46080395000c040710300703d5070722030b20b602402c80c01c0c801040e0007006107100300c229080e90748042800300c040c400d01c4222034004000810300705110f100d014072000f03054105d030514070700442100020327501d110340700d500c248041e1a16100c452260088009000414518611511200c814a407803030302d602e6040241000c9015520140e0001e58051184405484806059250b01001030300c0a8402860100b0122449030301c1c01203000240402151003003a0010150021405003071507480c044030b041d903941040d401c05107008500c10941e030341c4c0810404001c1e01414030341c0d184200b07424140003901c0d080c0c2004200180000310000800c40000e241071040400020802c20280c48850840c0c20761010b0702c00c1d03580100701c0742081c0408081840d005400450505000852918080c0442c034a400d040300d0400c075800a103c50285035004107254035a0120043c2d500b003090b4034039010040d10390804185d07500d1628602c030000030281d05080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 150279856 1250 150278606 150278617
    0xd020d0506090309040e031806030907180b040c0e06030705090607140a0308010f05060403200306070207050a0e010e04060209011704052409070308090307090e0a050706080c0d020f 79
    0x150a441c614600300b1035a5907030741d00030540e1901031407402da07101000360404406e90311200782c0b10342c2100780810a139041000e20f07007010b05900320b0340c002ca4030001004036080045080c04620700b10081064060b8000f00011607402486000600442050104440e07079541c00b140ea02c00d60324200540c680303803000c021980b14001e42000410201000619514503000020000340e0503100396102d080c10381e01c0303e14003c4811801d202d01c541240b0280000d0000443c0000c80900d02c50400c46444030313080e142c0d4006441c00702d054504c070025070070120041c040b03418010064805032424840d10a0554500b69080648a60081001d8011640402c8144c0d050f8801c0d01000788440302d00304010894205801c040303072034040e00c80c12200342c4030071041107012a04425185030f20810060004e803840350b282d03881c1c1601c103500c580b072220f13454000ca980116160101b44200c034500c02c0351000402030406646402ca1030000300760059418420507400700040c003080344085900c1c54044000150b26600a6071f5400181d0054 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 150281106 1250 150279856 150279863
    0x21c0216020916140d09050a111017041211101a01031814010e07030c030506010f180b010c02150a020c04050613050c04030f03110609030f03060d020d 66
    0xc010a00900180c20101140d000302d800c858280c0314807454000c46210320903804082041d20011140c0c1120140141480801950011850f0740250351072500700704003440106c84130207074001d42200c282080f440d20445142c550a111079006d103d442c032074880110041c0028146140300040030300051040c07170b041d5a030803001011a103405040c807400c603001d0281d81440c03080f8406414912865036101c1c3c02698800103060740f101c03001492035220341c12889045440201c0c1592079241081115204003c018015400380d800310714418103510b400c3d0300f0404103034418032100405c00c500380a6081c0841d01240800301880d4000b0b00c0820540c0186c0f03a4021240000c0d5003c40000280a80c42d801c604c01056034601550030348120603024810401102c0003911001d80059004a43e0314227000035502058100c071180100710b00f000c3c0e0700c3d5518606e0301030180c021400640103910280b4072601c200b1045400810300005913052040400441405000080c5500d01c50480c10640ca001d40d29405100185d8640 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 150282356 1250 150281106 150281111
    0x60203070c03021002270d020a060c02130e03160309080105070509100f21182d05030315120f0106141203030609040302030c060403030506010e0d1203021c 68
    0x40c0400d01501040192000b034016010345030b200d00751269507208540c100c01092200c0704140340c069503414a907941da080850b810264004001003d070f40c0d41d031103680052407150381d040c182500e86c5c41032101c0c10b66024014445a4103081481003805008015165400d20100ba0100095003038201221403032000c2d40903c42c19442c01040c4142954088028001301d00700b80d4042c40d190500303c40c1118841e4040b00407000040c1034610060f42a15042d100c50780e480910b80012540c110030345d9109102510251088030030a249080409031030700543c205024030a1416403903400c803210b684405440b1300c4000d2580e001d8142e040c425400d13541d2416450300d4105c0d21681241d010b03101e5048154000d055030b004a54441201e80501c40b038074904812400c0b030703200c10390000d582107848550902c4003d860141044080d80414800140008004c2144520a42c000c0c0d5020601d03007010b8002400a076a500c0d6001d02800d119504280410005100700051032102d1400503070311811201308958201d42199088116030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 150283606 1250 150282356 150282361
    0x50d020f0307091401032904080a020a0213090b060d08120a1d01060611010b010210020d090b0c07020a2301081b0c0c0f0103020702030601030b0c070609030f030c0e0a05060313060203 80
    0x869590086040c0d0b840b90780e29000362001c47c00703d44500c00b60302d40f45c0b00e05010010300040004427404040d1031400e2140c0101c3c0d11445c42540007401503030301e03080c100c50b846540300040c809010720045981e030041c00c1070300d5085400e442502c41c00c03200d01c01c101030300ca0000e0880e8082900300c0c445a1155003420540c2c809070054103001002e26018100d148105000200c460256880c030074410312a00d507803810140c000781507243d0b02007803d070065041280c40340a1140e9a80c2103401180341c032403406220f102c150b19625500d8040c1d1040110130f900c42e40001310f0102d040e540c445401d03d904000382c80c2c03460702404d00d000240c0d1032000d12075108440320604181004040b4144041541c00a5040d01c5944220380c001c14510540f00114202d02a490300039605078008401000170804c0f05031100d07003040b100e002c42881e022080d26000191400401c0071030001d20007030004079500354180300742050403000b40ba090305a4020180000d00080d80c5026081c890080080402c442c024410511404590b00240c10354491 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 150284856 1250 150283606 150283631
    0x20a050a0206060f360c0714010b010903140106080d0908071403030f161e150504051b0102160f06090617070804060939050d020f030709 60
    0x15002822030030090312810001c40c160b46446600c4103c000300180041909409980d04080200c058001e260485030080700c0d8207020b0b042d0194034520826076829010364640051928220741c001c82180303a01c880c1d15061020000307a03803000354001101e80121500e030400c00d60b080480d004280c02d6100b25468818044581c840f9034002c0c4140c2d0407144080103652305240e8030064401c2008200000c03da150700104940c40100210002409001d10051461030040f2003a82d2400e0045130b200c00d0094450b00b5906141082000004038412030100101003072004d0b0401e5500c059440c40c1116102500c2040c802c241d91a5900c2001000c4004400101c074480390744d980c0c11103080d01c443e20300401d000601c4500010170241d0199200524031350060224443c0b03541c03900c504840401e405003003204e5840d110141e91000c15445000c00100301501544070100d00941c648541b2840d283c820200013010390350300208543d0340c0e038100f2100504e405655010f011560103000904000c555004451a074dca840040c1044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 150286106 1250 150284856 150284867
    0x4090e0f100e12030408090d03090b0d020d0c03021c05070e0a0306020306040c05180d0305071406070e01090e1f0f0306020d0c050301231306060507120305091504080d020a 75
    0x5625802050303410440c3c0410b440300d00c502c400c550140805000b00860441800c1542050003070b1402450304503074090315002c60390303a182e101c18002c0015036000b050701241c504440c403920900131500d041c11071825aa46081d460b00b9104040124580d0342d881f0f001540e0540201c104641103480180070407140b82d1207140840083d00151119806585400301008203640210308840701c01025103402d0151354210b2041002c2c51004a000310b04004080c4084800070f0488084085a100c92401400352071030040d4005141c0f04103100340740c1c1007025061040102c40b03e107d00d1036412021160380c20510a00703011340242140040c0d171180ba44126072034000424401184d016041c0d40c0440e51060085140104007107465020030302681d51850300010141c042d0b2a1034422032400e40c24003a001045170318100d0030756422184540e20141c00f00360000303124010020444020b060703080722030600300414201000020b07600e400825910980c043c0b040089001d03c0b1824080c0c4120764483c0c207003590ba03503140c00e500504 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 150287356 1250 150286106 150286121
    0x5010b061309270f0305090d080306030c030d0f08091c12050a021213050a062405040e060609090a06020a03021b06010317070212060408030105030d08090304090e0f10 73
    0x14910303207038088000b244034010541010f101c4448142802e4050b448681005070155011010302c02c00300000c243c0d685503a182070304c100380101000313922441e05000303241c24680c42030f100a219401000400e0071060f0080342000c1c2c0c280d2103180c0207105a0302e070002545001030000c052145450f480b501e80010340d900c4810301c0d6642604110a0005880e1410500300381c1c00350002c00b1400c0300500c40002c481c40132101c1e003582214084d1049031800030450719254111a80e4440e03d000514400924851140502015400600d400e803020001c402010f01d0f0f041d202c16010341800c0c401c0102070007141000c64104650034602e0b030881000c565900c0c100b03030081d000f544240e800240004592403000c1031081c0100d4018100e0350030100990360054034503d0700130a681700c0a0f049a01664050241c010307c6800c02140d413043e80300c1d10ba16562541814100351402c4040100c00381080401e0042240400c0e004c410340c0c1c1240e40e1004003069110b045501c442c14080509807070560741c803c0340e40b201a05c0007140c00410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 150288606 1250 150287356 150287369
    0x2030103030f020d020a0b0403031e020301050406050303030f060d0302070816180e0a030f050f0c010b0108061f0507020607051518120708032205060a050609070806090405010b0613 79
    0x3040c490900070103a03110250130f01c0103000f40e00f00382da541c004140300b03000b81c0398464824500060106061410710b0004682c113885017012650100050215041511a1f03c0142034100c0c000c5003540b5100f81c2d83d240e00f07140200340320300501c9a04c0c0304204040c0204101800f0380b01c0d2100740d0f50524001c611403405042d80344540381c004000100c100341e546c100e83c8601860009144060650860f5035101030b201480b0407000281004000c01501151590b0130018000300c42940002140c4070b11440cac0014444034014208138402c0d10f003603919039210f200c40d0604182d8a99a801c01070b807a6101400007030031074010700c1000307003050003240300c5003541201036140035129504421487d80000007508910f03030390340484986280d0070b807000c0140b80c0c0400c0f90440038561044018407020284c0040603178101020b0101502200c1c0c96000c0f4040c00b101c510540a4a0f6010806403294603140c0380010004000c0714004e004580907a03003040201e01441400c1d00094110940948015074a00450340041007006e010320466 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 150289856 1250 150288606 150288617
    0x62802030c010b181618030b0f07080f07080718080609070b13090f1b1805040203190e0106030209090a0b01080d0507021309061a1305010302010f1b02030304090203010303 75
    0xa510526084c040c1d96068404414000e980f035a855507070040603070708259120700307010300265500c1448440c607125070055445410341c04401c1c200080c043c0c11151018200c542401100020071041130301409840c0c0e445001890700b00d80686500c4026106024449802c1d00729100c103483c049a0f440300020201c2c000e4840d402154852030362068154018003038286c248000040701ca070204005001c51300100c03080c00209c580050095223401c000c604ca4205424010f0200ba0084d01c0700854052065070b1500030841503c0c25440d526008485100488078690030007040d940ea1400c0240c40b050940c000406190f0141200045082102d98503544160078034040300e02d0140311001194101003c6420b2004001a8032444d04015040e800c001040000c0401c0782c00c4540d507451010041046400b80301090301000591600340c0b2822014030441c4403442c4400f201e414200b000410050344d0110f803c2844174014904407401030501411440e900a0000b00030f9490311001c503000c00e02250301d40c01581264480d03201c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 150291106 1250 150289856 150289871
    0x70302040b03010b0702031516260a051b07080f0f19021b01050c0c0907021f0203061003090b0402011b081b0610061e090909060e06090c0d02062802030c01 68
    0x32508d200c078003200c00c50310101c4862014403605021700000e2a01e144090140e4030318004000c5000c041520448021040949690038003010f85c40c40030030386061607540ca401524144658580494610455200007182c0200090704448106070005440c110814103001404d07003048400000e5454070705909491001e6050010b80300150301440464840c5020140602200d402400030801d10b004001e14020940c0200f803409550b404018000d1198031150400050b00c80c00d00009100021144240300005e06180034150f902050001e01c01e00da0090b0309113001002051070070710140c00400b0160b001000e080c40481c01d51002841441290032200340d003070031a0716135582e030349041010ba03150744034000104450204c110080b4004d400d020000c0241818200c0d03070039503140120021551441d1040d180c0555565844461007803d01c0540c0d000001c2c000140032118034400001d0706020742c0d9070300a01c100800503044050300003100c1c695141c0036403810038510b40c40d0b00000107520303640610300001c1c02c0c5d40303003128 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 150292356 1250 150291106 150291133
    0x203030d0906230a0902030f24130803060f01140c032d040608060109050d03020c0301060b09221b090306140c030c0a0201090203030a0c0b06090c0a0503070302040b03010b070203 78
    0x901103e4400c02520751412038492001000c01402d200d030040c1e0f014001e000303002c17030518010400d0440ca0002450b486401908640100c3c03401c84004c1c00c0700c0c201403039076410034000c40c402c5825641c0180c00bc8405203175054455005071782010950803603580c0e10101080c008009003000c005821044001c202f01034070550040120b6502030828007401c0880d0740184000d010980c46031541c1c036400341b018100100d00c00d441e04000307072085940000840040e4030108803071845050070300800c001412642615030030003411000244c1c40d402c41c140e80701142030381d4019103100d4191a800100307291144003580c030240c402290009281000b031b404291001424080700240000c0308058041c030440d00340c14101d0458482c80a00c800305d6002e804108115034991281c0f101590b401d000034101201d40c0c0c4c44001e00240b15150503801c441c2c1c0188141e00c20710004d0100b140701e00e5150304032100c0d4051032420b16601e175184070040d0004d002e10b800441e480c1d20040000314480072100c2c0201400c50080b01124000d0b900301c039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 150293606 1250 150292356 150292391
    0x8180f0d021912080408070803010e010305010c030905070515040905010e16090e01060507050c0306010b09031b0303030a150e07020a0303062c09120705030703030608150c160203030d0906 82
    0xa0001c00004200d1002283e0520450080d07810038801c0d03005501c3c03c00c1d41d80305d2420382d8000380c101800301e11500d401041080000d1051403000c03040e9040900080e031598441640710308040c458940151511042d400c1c030b844034002118007510310000100a2545c68203400c00003150121400101400b034050b40400090194403501d003221a07144040c03010b03030300b03000e81266940c006e1902111580305200c0000c0c11a0740a001490103490a810005c0e128286001018544641540c104101c0c007080079034141140c8000c021039500c10034180001c211600d01c4690444030001c41da0080c144280180c090080540d40417414024035800781e54107000142d190460704402d003401d1000d0000c000c00310001d5022540540102c0c952082c1c481c8103503100c8600900088855501500044a00d600001200010903416115080203000b4450042100c00312400781e641a54801900707401e030f1041d02092040c009079400c1e42c1100002d6020741036986820f5200000c901420103010304491450404800116044ca80e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 150294856 1250 150293606 150293653
    0x10801061d010e01140304030c0308010f06080a09050a120206190506010806041104050a14030f0102030106020d0507050c0a03080304032c040f02040518010e06040b0f0108180f0d02 79
    0x1103424545407009001541c00b40714149500341404894503560103151a00700107144201d020f51200c3c0d10f41030103403a00800701e03041604040110300c000d01c0280000c3c0c1d80082130544c032540c11f690001e001101800c03e03a18200d440b6a0041c9052807100101074040d50200e0f049005e80c0f4001d1a0901c40310070b01400109942040700e0b1280054000000501c103440d041c3c005c41d0806401e012110b02d040d8403580801e0002c140c4d500310003201c6a0791a4040c50a043c20090310100c420134100850031541461002522800e0010300001005030200300082413103424810041c0d0344030003c1c04000c5565884c5001c00e10303904100ca0030b07800704c0e50380c0071781c5680170071100c0442c0d451a049030010440030030b1800802c0020903611001c564019401d01004c2403e4640d40e5030740d4401c08902517501034562404501030401c504c000c00060256040c070b01d14124130b40364508602c4c0d40c0701c4242010f10032550ba000000c00b0700c0d08031500c540a58442c0fa0b01030307805040c001c101520b0050259094a050b403000c0c0007058100603c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 150296106 1250 150294856 150294887
    0xf010506010306060e09070c1e110604080601061826060601030b010509120c2709030403020609040203040624060e06040e1f0807080d0f1d0402090d050a0b0601080106 73
    0x1d0801d085031450f0010f0940e5002c100342c00d2441688c3c18035200d01d0310b080c1c41c824030b003445400c0080c20903040c0f003038031007550200300f80454036030389450704010a40d6291390040c8603410a20000000200e881014a248280601010209041201410040b8914540003406682014040d503404038420394841c0c010b010b0002010f0710b41500d8001d68806000b4451084c00b801c0055000300c0d038025174281da612800008100104c4005055141c0c05003483c5a142409403034801107a104200070401078840c8001e84000241c2120016240e68441c00c1c080090a50545130b072410103e1200410f009821024071002079441070b94035130040c0b2601006000740f0b845280580388080310b035400003c40c00081c3c1003d204c0050081000d0051641e91694281e01e003039141e07004a5180d420105054803100e51003c1d103141016003e14001204504100703640300040c003c252240d00070394001807070907170b19220009180c280981c80000c9948080c0e0781d08100d00000b1040e610305001484172800040c4161190220f0500e0060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 150297356 1250 150296106 150296117
    0x1305030f06011a12130525050105070206040b0307170c0403030c11040b0904030306081005011202010e0301150305032104030203032a0d0b0a08011b08040f020301020406020f01050601030606 83
    0x244100c04010f80c201641c1806104400c000030101c481110790418003503805c0300903d0b8071400413803901c0341c18a160410300c00e000740ea945031400c1650005c03a549204031542030800540d074011600118480348640d07001510020000402d1006003039115142d2034440f034a818400416850392a20101705100741c1c030028001036006482400030600c1c1c0c0c0060880c01c1c00c010400124015000081196440300311021b0340800ea880c80200301c00b041c00d009044c1d6045944070208140d60511070b00c0d040902030402c000c1e0420441c01d84440640d2025805880b4642c0d49581c1b88281031f582e807415a035268040c4643c1d101c9580c41004400c000d01d00e20f0100341c05250f1503000755095a8850314106443e11058040c074000c0413010300441c0d504143e143c01420184590f10002c69101d00480c00d101c0d40b264190300111007030f8900b08444040c200c0440350082c40d400139191584046d180c0d0b0820100d6520008800b039410b520000c1c000a400b034000404904071140750307009004907600e400054048803098801c0c8000b289 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 150298606 1250 150297356 150297359
    0x4030e090c0912100c05030a05010e0115030f06091a12060103031e0509040203040b04020103150e01090c03060503030c0c1309050d0302070f060e0c03213c1305030f0601 74
    0x107014850310144800703010803a100030000403103203800c1d00c510b640751700081540003050040c449001c0c0101405030142442400c2107514002501190140402e0940c04055540d1000d03040281640c200e0801454450018049407a071010f590552451845030940b050380611104002c202c0049601f6048070f82649449580e4108061500c0a001550000310100242008800304680c0c0e5840a1405180944040322544c81c040c40054100c0380310341c1d150005000c900c8020048003a50328009810b48440345008074658990f605c0a402030305080d04101ea15000101750940082da00150355803032900202c401449041d021514130b000c40307001440203440703034200f04550560b0701e00980040c072605210300c1c0d50810443d4a44c594204075400700c5008000b54000b42042500c0b49010460400c0440e01240404205c0c0e6002c9840d81c0284600002c20b004054403148000c50f0070765080407000403601c440c00c00303102d055000c85c5050250303001c03284904503613071040d2000c01c01d41800100d2500c18803403e401098540d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 150299856 1250 150298606 150298609
    0x903040605280c060b030309031b030109020a15080c0703020d03090807020405100e07050a0c0221030316090605160201080402040b0303130e060603060a0e070314090604030e090c09 79
    0x6600c070024040300120210740d0b595148100c40e0900c522400603507034a40032190213250903c1a0381007480c19600c01d50052002c1140ca40c1e02207180c0481c079401c00c40c40c0750340310303001001710b40544400403020394043c800c0040007505101e0951018181c1c1010303a20034400790350b000c00c084441d010f00071000d001a400f05a038030380428003a42c481b2280d503028105d03050034481c20303034005025254110b0389502640c4100b1002c0121815602113030390011011300f0010f00702060f89034018626403500c00081d1165202c0fa9841440c0100139882002d031300c071100240d80c2d0383e240c010030001e000c44e05554034400140c608040000c41c184154107071520644492011403491701c80b0740044503402000b03441a80e2007a65a400b4500a44c0c0400051a070f110090700700c0b06205203840b60748040840e0003880980901d404004004c10707681c800c4081c1050390686a4080e000d5101c0420440c000c15418094040f084100c1040c00440751001a40034030441c800c0e5100070700c0144100c1404402c40040c0d5a406414906101c4104035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 150301106 1250 150299856 150299867
    0xc090608090c0a03080901020c030c010c06051915140a0e040b18030c070f0e06060306120102070c03111002070f060e12030d1d010b090c0919080c041409030406 70
    0x421902002c075030700800b02d0000610189096401110111800075044080e5601400403a40001d4110050f02c50742d0740880010740f1030a80b00c54014880c95440001403603150b01c4101221800c950700c8402c0101c94140b581c1181517209600611054052075006c1c0c1d110740c0343c903110344016911034000c400d5450f04e980d034840c160307081c003d401520060301c05240c4000d0340000b00041d1860301e18580051003003030314041184894180355040803280150800400c1191345910085980000058484506481085484078024025084001c2a9000d1100c001090110340d00400c1105074040740d9045080c681544181e0355940755200f9081021001c030340030030030107006000440c03031100c0280286001100c01103500341143c3c044034042e64499030380c0034540d00205c01c96015503030600c07401008101003403030ba0f400200c0c0a41c00030282404058002500d007e107450f002c48504488000d42c2c1107038132803510355041e241c481c000e1242c510701480c43c203030307201c01380e44802d081d070700c2c001c0310a680698501070074034604540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 150302356 1250 150301106 150301111
    0x5030402011704030906090611071502071a04091d070303200102040801051017061506120708040510061202060c03071506150c110904150f0b090a0c090608 68
    0x1031215000400d040742c0340900115202d10302c2a55441405801c0100c090700100b86604084100286e8028050a10800040d20400d451482d0a030342e44505000100300d1034110590004890100d2030b03032050028501d08800b820907191031100c01e10840c000048042e07071603003001281180b1907210341f404001080c09540300c501014211030001c2000d1003440c01d0a426640700f540000c00c681e548204021091201d81c0780070015040d0350700d66a1012011400c0582c2c2c1e07000c00b0300060a250070121000701031f40c1c4d40e0000c940030401d0310603000c0c0b4103280154024054400444050300e0900821a025000561500c591700035a041d0710802320041201b03030244140e680000c000788040380700400c20710010031609030003130440062301007002c14142d0030030320340c400c03103082910703d000c24840410b0401c00011000c941300144040d0a6401d9001ea070740314142112844200203080761404e291480301d10480010760090040c408d0f064400304c09982740d002c0c010085806140204c0c000518a2106110700c1d48904109034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 150303606 1250 150302356 150302359
    0x50405061f09050d030206090f030708040e090a0c0308070515011d04060b030114041101020d1d031c030903080c1201030212030d05070801050405100807050424032a080a0305030402 79
    0x10402d900c440115150111850301940507038400c40070407406203130420900b042c041c4058055800c000440d501e0003003c0c05580100c41c00d6060304400107103505070800c4094a0240c1141d0041130f96580c9050000d90756105140944842c0992075160031a92031781c01e011030490788400301d01c09005040e0110b5189e0b90034094000c03609182c0f196407480041d5024003032080050b650b42d00d00030160400d49440c0d242c0080c0c40000f1415500603070824852142c00c610340b05056004d1140d20000c0f40104400241007581c2d40100200700141c203001c3c00d070429819400a2035041c425111108280c0303451070380001343d000d0300c3c0b4440b162a41a10041c001402c00f044c10b01441030755082124209050301b40144142e0380201d40302ca0004040900400031490240543d41c0c0068a05c65513a07803140c1006a01c40e01c5a205000b241e018a03256980c04a41c85d0b400d8102001101000c0c0712818140c1d240d00d000c5031004541c00c1318540e200f842c003000d8802c40c01c100364404210741c00000205040d841655040d1041c0c4c00c01042139 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 150304856 1250 150303606 150303617
    0x30a080f090a0f0b1c05070507020108060d020409050c0a140d02010f110604290610260f010f0e16080604110a120501120b061e0d05010207050601050405061f 69
    0x70f10300b400103054a015200c1c40400d29144c000c8400c44541103d4401da503c0146820f01050050444c4c00c04111500c3c2602840d00080740e5803181b02042e000300c09200003d40142c60300d002c0005201004c60920103504003195541c1ca5280e0380c81c0c076900f94458101000368813844003d564001903028696504481e24a41419110620003c148a080080450381501c0c64101545110fa85080c0c10794080041240f4640d441d03124108500820036401c40b404c009403d0150305079004000d00b504840b5440448400341e80c801c410311700620240d0b0382840038800c140380b002c20762002094204140d10b010780705a2100c0030b410031500030410b040f1104840900442d070801d945174a0511480240c80041403070034582c0e102d90028121a229400880d0f0050740915440480c040043c00080c90b600e1065030814000c4a0114141c00180c0002c5003540e448202c0d16400740350405001c040010640150655500800c01c0c1c40b001c2e0303030700c1b418030081d118121031690340801c04030480303600300020f80c0e44480c4000041c82d0a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 150306106 1250 150304856 150304859
    0x3070807030602071a0108030304140102090a0f08060601050705030a030f060312080f0108010b030d0507050312090f0601080304060f050d0e0607051305040b09040b04030e0a090207030806030a080f090a 88
    0x1030308182041c0c105484803500062110140131100c407180341c2a11002c40320025541c0b50000064480c000540010301b00604080d10b41808002501510348207d40180440180780e0380b1b01c41602405c0152003141624010030001500c0b87d805002640d42c0c00740c0200c05145007070820300088000300b1550701642a040e99031680400406c40242c00450070500030f44444205040201100c401007005a004a625030f040c000808950744000c181c940c4000d2590030030a85510f60380c40c1150441c003a498800c071824580c0d504106110100140308492100030200b0344038581d032901003540d140d100c0c0303001c4c07540882c00b0250030044040c8200e0060803481c289900006103200074034405030804000341e4609000460200e0403401110072004c406004000441e0100900305240c008140ca00ea80200081c285a0010f0001000d0601820282099060051151040a8507403d02c6002500861815030015001000059484c03c000407074546482c1c1200200341001b2440c40103c850340e02600400c1d0700726802e10070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 150307356 1250 150306106 150306119
    0x19030605010e070318080409020a0c1e171201050d2109180902031e030c030c1c170103120536010801060912020105090d0b040b010602070b180307 64
    0x140d24041c115048446840d41000040102541c0d42408031001c40855181901d0010b085c890454080703030140d644c056264444000251034035843c070302e805040307900c942800c003401410403c0c2e0703851000e209045500d080d05440d0a44030140c01012203400100140100510240c42e117010900d44aa10460703244180100405c04010402080c0b144600030a4822030f05015000002c035281c100e03903588000800681000d030b00029a518200e81251880c10341004020b040050240101c1b2a61074072203080703035545c40d000100903a660420505800b8140d607546010200c55114140c0d0b0f40b00c81402c04c0c04250241d09540314140d4002e51581a40c080c0801000383c84e0a880a8042c040c80381e00c100049024200058a001c154080e64450301504010f40071005210040d001118281a140c000d1400300f0001850710040c1c1d043e114209800d584051f1400300c4400300075924500034030661298902c584240d03a240c409076502d40250103500400401072140707502d400ca50698410801c84000c040368246560f416 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 150308606 1250 150307356 150307361
    0x21c03090302130221070c0b0108100b090603030d1104091e06092009060d0504060516020106080a0803060301060b2d070f0303021303150617010e0c190306 68
    0x15421004206030400c20010b5140c03034040c0c0340b2040c402010a42c0b800744039030309159042d00a01c3c44074040780c0c0c104000c03d240c40d100d03090b4441a0742e4403a01d0030340b165860709501e513a14004000c00c40d80c035a05182101c00d517030810a42c110b00411024000b14180400000c441025001b00011800c2c842003d21001450003201d00608490031880007640003140051407428040d41d0300d64006c0003c3d81d043c01e525410325001007528058030241480400c3c1c99403000c000184a500c20150003030002d90a100511091004590009010f181e4040d0814010078100009134280c0d0203620582c0c606400c284072000105d04a2002103a002e103008000140803a2140000c0003e500500000056030000380052030204918400440d200b080c0c11003114145a090350324140c4c46a00007800408240d004207402c0c140f81082c14150b00516840752000f030442d90848a248010403646c4110005950010349240c492101845110000b13400b600c040e2100c03075240b409004042600068108811500603400400314001d40b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 150309856 1250 150308606 150308659
    0x409020f1c03021203150105160b1602011505010801061202070506010305160801090b0105010f11060c0d0f0522021201050a0b10020d09030308060d2108010b04030b0a0902 75
    0x950514500340d01c504000780b80451078141079081301d4040041c000c00700e444041000100809280441e95840a402007000b80311000c10014411031120003841329071140c0744580390f501e0b22640c2c0200184503801c03003038421003d020b1050741d01055800c001804568403620703915510000c46a40549004020b68946140041c243e009130361030f400580c610b03400b21203c25000d00013040c03084002e2200041945604940b0703c01840355034180103100038150302c101c0c05034104290b040d011a0030b83d041450042c4640d40158458000c0382c903018501003000103542d413948510f5000d500d1500380005642240d203121118189080003e980c0302c3d480c0d0a06d404001d100f4003540d8030034080140045101079032202402400e0651800301300039900103401601c9201c0d8040c007000210ba41516152116031140e201182d03a042440401a2040c0c1612542855000d8a00055802201c040d5150f40c40c683c0e9441050b191800743d400020003000041000c1002c51400d40c00c014200360005001d8113259a0394500c0a9502d80c0a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 150311106 1250 150309856 150309889
    0x1b24040b06040c0c0212030d060806011d06120105040f0b010b04060c02061e04141009050112051005030d02031809060d030302090406090f090201110c06071b0504110408010e030f090409020f 83
    0x154031500108c42c1c1c020300d40204401002441907505108040c10180d814a400b00031444004000480d41d81d00d10160000c0d90180d10002c111501b081d080c101c2401040c440305960908250b000060311850140441d421100580e0b680b4100510341e038200302d0254050b500c8144805000420300546450781c2001340020030a2260740641041c0010a00c40249101f65070b4400b0311841030000c02007640c104200c541510010180001d01fa83d03458280d4400302020b80009826202d101c580c00c81954000004001b40d8410012344015603002d4410000c6045040310035030f40181c0b412003503a000030b010340c024100f0000c0040c00495520b45030b14010013114424030b2001c843c141c96a0f02c00c003d5580202200c800400c80f00007074040800c40001184c90341c07052140041110309920000b80440607410409000f510000b0000e10001c08107011300001a04a8011800c40d54a170511006000f280041103a0b0f0000c0000c040c641050800b20401000300004441030743c014840070440c02c0f4a6030b544c20901200c00c503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 150312356 1250 150311106 150311113
    0x51c0207060e030105010f0612093305071b08120a0605011b03082208030c030f13020d060c18030309060e0f030c040203040302031b24040b06040c0c0212 67
    0x241c0701009068101400c1500d0003640743c07100500c02c0c1c0c000002c405060300c10300d08011240044425161000f0103442c1e2004c2c20109144890b079100350f4084981480e5a8810070016035031503600043d4004944054400e407001c500000821403801c2c5046c4600765405000e00e5245007481e280c1405101c0f60001103519814451340ea0400340041d40e00000c030145070420b03802d90001c01c1c50070f03607070041c01094000c3c003125080a416131482e03a0f4400700c0000c0c4609160301910f0729031241001c03c06000c00fa0015510003074480443c20020300d080d10800c003d11040354005201c00242138440c4c5034140100801500d803001c000684601e41c0e050040040c4a40007148a661850400c81c54031030018541d101118040f4403a00c0011284803d541d4002080621160100c46c016603d480d940313420b07451842401021441143c1d1100c200c0714880d00072032280c00503044800c640f0500400c10542d8421a80125002000144000d0120b001414164040040c0a509040c00e80d000c014a40000d0a2034091603540300840c2d2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 150313606 1250 150312356 150312359
    0x15040816180b130e030f18030c010c0b060103090c12031106070906090911040e01030f0201020c220522060608010b01020106080304150e0d03030f0b0102060105030a020607051c0207 79
    0x1c1c0c5514246040c0390560404018000c01000007500240d20030200c50440c41e116640304201c01000c0c4211258100f0300f14000e69511059034110b000c103484003072020b1090103180400d0b00c031540207450400b0560b85c045c0d0102400e546810055008000d441c7e004c2d901901400404524656000070303204409010b5204c00e200c1a00c0114402e1520a00514400c100802c12600700074458004011005440c56014003081103844c82c0380c8000b41e4051540204000760026000000303000d034a80040048500030390954040c0c48040050000b10326505607038540d05611202500b102046c55400590090221102011001259024040141d4030010203807841555810100701c040005d210b6100155028002406036a190141154030ba01031407042400c0d01e00c6429110b05207e1160502030051038000748100340c40349090030024020840702802240103454042003608a60001503698100c0d08018010f00301403240e9428031003075820000003110103104958680c1c1241e003181259a071844100c0d0700400b01203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 150314856 1250 150313606 150313619
    0x60f0b0f0f15030a1b05040e090102070803010e0402010309080c01020a030b180f0a0e0118030e12030d0c020a050a030c0302120c0d050901121e06090b090615040816 72
    0xc059200340c0d5403180400200c0480280c44840c1d50005a516094026071a591141056005004188925074001d0303804151980c03543e400c80064401c0c4e40d03118400c0b000580c0e91100c0385080780b2440034081c24019003440100f20800d07c5a6506d58000d10601d004110300b011503884003510f030464030b00042c2c2a5008201c0c4803516a051040500301d8070111840355103000c10070b0b942e6544100250030b00b090318214000082040c1142d82110001c01d1604c0c008003c41c0c186407821b640c0f8440a90320403400905600c000e5082032400401c0e45a1411030300026502e0300d0500d02c90403009200030a07600b001d5002d8a0700400100304144a0740c1e5800340641c50f403958507905450700034100781c0708078100c000d402d00601c0164141d41d40018503c0e01900c141c24119503403402c50006030340c60716101a445100f1410450404c0c40d07640e590301081e03c060ac2e011424007607240c88501c254160750340c8050442d002149907001a107240382207040d1040401d1061101031405460307030085404c1c030100030084140116401c3c01003204 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 150316106 1250 150314856 150314869
    0x106060305150102150f040201140a05250c0608100504020711030105010501050f070b060d0f03120507020a03050702190e01080604032604150e0709060302030d0806031009050109060f0b 81
    0x2c0b18002d1003d0400620344009100701d900c40505268458812400094216401988102842c004003801c00e52a4180300b03000800c141d225202d25090141d010351400e80300780c481051500156400f0280015003030400504030341c0490700511682c201343c800381c1c00140f07a8a0710f10080c90300034000d210756030300c020508040c1800c1d1030043e40700c14100310342002007419110044094175500c82c1d00c4078012200f81c840340b000884009007001c0241182221001400800d0b403c81d201ca86415010401448256074220707069071507003100750740900424010044800149010025103100070965040051010344030188c0c081040c0090700070344400e03030000c8103010506030854103000c140c90410210301c0c80428944615604da4901070300040041704040981c0019600e513400c0001d1010700d43d011120b0150351001024058142c1d40b0060303000e1700074201d007140201c2c411684039100d900c0203001840d07000414050b450051000c22415501552782d848600001204c41c098421000361100700815034403a440d0401c100d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 150317356 1250 150316106 150316141
    0x30221090a0f03080f0a030b041803080603031303140709020a0c030e0607020d020f0301090506100e0a23040302010b0a0905060112090b01060302220b041511030403020f060c0106060305 81
    0x2192a10b20000b00002070100049524201c034010f203058480380c425000b03801502243d859260702c103044c01690400b12002446510505020ba507075403016132a11070505449105600350b125560040381405d001107a483c1c0070000311144a1000c441c0b1441d0368220f104100e0300025400c000081903c054141810b40c01f01c504001c1c140c1c04c450036031038016194001100b1410b2040028087d202c41041490031365020f40c0032104550b007100664019150070384247c4224004d5018660310700301075102140400d0050720441c40c03e006a207000d001030f64000c916800c401a00104110210740d201c0c42d180e101600c0e03880c0c2d6100100403405010660342050400075000e65041901c030740d6404e01c0c280b03480010810384a029411203071a0b040040e0b951984103281e500c01c1440755018410080c0e10440050b885000c1002001140d8246411240c0d0b501c400d5801c030f84c0d0100b001c20b4840786034801d000900151824001110244100604441ca01414290128207481c2650f001c180440d98031005c014004610030380001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 150318606 1250 150317356 150317369
    0xc2a030a270e0702030904060807330804080c100c080901020a0914130501030b06120d020606192111010c020102031606020405060408031c06051804030221090a 70
    0x610702003845001100c2001500c241c01c1846104004903180c0c43c0280202c80721644c0c090000c1c04000d0b21a010f542d41e0b40718610031f4951061140c5103003e0400c200c941619a00e941500c41b814804503588801c40f45604050015900464100054050040208949050b81d4800307500031484004c03040300500220300050100009034010403182c01c0a9034499a00b40a0301c50003400c00c1111240800441c5192440800e50b500684c40c01c4008020b1010100380c0520402c0308503940254619500b41190710f4102c50030000e40940e01c000b02188151030000c104242000c105032180300c0320ba68408001d44201c00c0c110148250580d0510310005008203403170305194151081c2042c40112800d940001e5580c07060741403011061060200c02c904100a5030100d900600004016580b61030301e0b00340c2d00780c4a43c4503560703500602441c004c170420400c501d401808201c41005148220052400081548500300184200c00314010314001c112201648001c0b800e02c132424600540d150304000040c800d45c0380d055000710 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 150319856 1250 150318606 150318647
    0x1020105060d240b030106030b0406060b071502090d08030403031a03030a05090105090a0506040806150a030b011502070306060b0702030f0615060c07150e03160602060c2a030a 77
    0x200201d00031024403c030004090800040c007180e4008203000030076106030302035419401c124000040c04650144a40603d001712030800070182e8500400010b4801ca9000402e40100c00d14001c240141d1a400b42c0180080605441c1d50101c1c1c5656400c125802254202d011a9851401e00007466081d600051909004d0f0b00841c0351001010340030301180142090141009000070391a00317692a80d00c40d080080001825440e1140d443c0c0300010b45582088989800c0004003440403d0700d46042c0c6150011650400034185085e400c20845c0240911081c0002c42584030b5143c2c0000083c0c00d61095800030604a05c01e240c6811940c4101400d2490b000f54000e42d5a00c04814425084600214a83d0900d4200c03030441d40c0300c0c0ca02042c0e44c1856015800191601d0300b0b82c2c0b9400b0000d41120381b40c2d004080480542d8480070413031540d00300e042c5140c0100760050f8004000101c808240000900342c0040300984581c448560f0b4403054011641c0c0340302d54800d03400c00304820200c25000041c0200f40381011101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 150321106 1250 150319856 150319879
    0x501120f182105090409020a030b0f010608100b070204231911040302030d08040311010e030301060f0201051003140102041701020c150108061b1213050d0e010c020d020109050d0606050102010506 85
    0x1c2c4a8016448454405c41da0342c5421001c41d510503848100030b652251086242e8a4a0030308807100c040d091086c4000703c2c82c5000014900c81012018000b42c1d101d01e445182040f03215000e000050a6041ea07001c00480305540b18484200c0e005005803007602243c02c10306007135003ca4801c40c2a0f96183c03100200300442884244010395000c651103c02c2012440e00c00c9895655050440c2c0060500102c1149940307801c4482c94030401c0400154180c445070780355800c41210291049080391011600303080c1d1440340880a000080505a014451742941400507046c20703210711180e4116403007507141003001d03940091740c14040007013806401c41005d450702c1150401c2d8981400703940c49a900038402d8180301e0300105040040c03c0b9220a407503010321100d19004032850154182e801080780c240083d2464407038154003181440c80303041100781c07003807040e5075402d604003403a42031100c05402e00000702c1c14000c150a000c1080e40701c00301200007140c022400401c1140c0340030006800c50318058542400381103954007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 150322356 1250 150321106 150321173
    0x1305010306061b0605071701060e1008012d17060a1b0207030305091f08060108091c0c0609020303121008030304110607060e030c03041802070201090501120f18 70
    0x380f024240c21100101c0c242c1d44021007100e489024680c204000502840041149540501c40355000c0740d0035500c1c00002c10040c0b40c26260325009110760004900a45005c0c40d4900c107050507610208150483c140200351202c24510074000d068000301100d80c8454200542155580280c54003196121101242a00c031010700a40b0307008240009000e0010001d400103058841a0008101c0400d4400d400500600040300810300641500e045002540d00404601c160b000072480c9000d160120f8030018100182c1902566107200703403401501c180b503981200030003588041c001415440810f882000c03140c502000d00104030030464000601541c030520400c8002003245450200c0d101e000c45100c0d0305ca2081d4a0700300050110300400d20483d00001c202040d91240000103802a178944e280d1200c81e50400c47c1d5004224001c8550103400501480c4042115502805c03005142c0000c1d030f100410482c90385c0d24030200307a4500f90f4440341c0070101064134205006419281a0342c001511502c4015600002c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 150323606 1250 150322356 150322397
    0x1270b010c1b0e040f1208090c0f0307080d0305041406011503052701020307020708061e10091b080c070f020f0d1a060906060703080a110f130501030606 67
    0x5009089010142c10242d1040044565000a1a0120003c040c620f082e14150705d07080503034401100e40141c103c036012003950003203141c0c42c031a001c140000d00524405d02c0070002d49003c41161903425005813600440d0813001481101c0b400744158401142d139042a2500c18904c4642d20720318851038000740018041e1011552a9000b030710003a142c08101511429072450108060902101680c90462150b0302d0110040d009148600e0080d02036401059941e44142d4840400b1200b0035070b0b200c2c1080c103000c0c00c54082c000994001c81c81c000d40032070b10740e110340720a400c88002c04068954511082543e00c0700e940d000c3d294680c081c8100348100e05102c01030351100d440c1c40803039000900c6887c3c24211540c09440b42c0d4204003910b50003034244401b111584104100180d019586140142640300008141d82452800c4600840e07040d96180c0e0f00e035581d04615001000b080140d982c0b1000c0402500182400c1040034004501e0103000301d0361483e2401d0300141c00c03544580e100005002c19207803070089168401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 150324856 1250 150323606 150323627
    0x30f010302030c330c01020304050718110d09080c0604050601030b010f12030c05030f0f0301031214071b0510020102130e06060d0e03071b0305010605092203140301270b01 75
    0x35914590341d41004c903c11540e02461503c00100c0d84044100070a0041c00150310049509101c5c4d694029a40b50540c942610b255009006110700d00304000414809107130310000d08140108280750038880c051100c10b050041c241d4040d10240d20850050044c07041100d140c03401084090890000795281140e0710510385050103000c2c0600c00e88440c41800e01c0310900888002d404054451b80d900c2040302c54a995541007030000345d0701f90f40f03250b1079080070602400c0d032400121030301c0140608241b004d03a10712041030911401c40c43c00200d005000176103070712100350542005501d90005a2903000c20500709522584a9001c0d09a8010b680c1c180520754540c44126111a040f41d2004503040010b00e0800d469881142c80c010100f400801d0b0000d0064203c10040007564407910091000c0ca5491081010014058400030100c0e0311105103103002c0c1c410b03075540801c01032190812054620752502e0888030b42c0c00907482a0004069102c03d081861500d070382c042d10969441d402080310b03001050000b801c55440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 150326106 1250 150324856 150324919
    0xa0e01021303030e0d0c080703110a05150d0e01050f040b06010c020907120e06040609050714010503010504180219080d090b1b1603030f030609090b1501050c03030f010302030c 77
    0x2a0381318882185c490542040c0c0381600100315100e02581c4c1c07000c8030381e900c843c1e20082e1010982c0408921031494410003130030032900010100e030b0300f01000301b41300c04035a800b80c0c006040d890307074070300124150030380a00803070384120647e4500480d40c0c9000d080a000c4d903240184840e04005200d03c0840061b501c081c80b55411030420325015140030202d0b030410b0020903e41e494400319100300350030881089090341210060703d02c1202030b16803040d0f483c0c081e0740f200c115030800315000c15001d0006120f68102030f0f00000b41803910408031110400c003174000c0303840c484040207034141e419030031038041c0103841c0c0c04c014801028a00b450030640722443c2c0080c2c00c090380100c411310381d402015109414030222080240301908110122841c1c0f0060352440d024204584000e40d04001c2802c00e00c00041000c40b40c0b02d83c5583daa0007480c05030b110791340c1c15014411024102d414606004003400b400325085410805144a0118610722414a5040d03004151902c908105841c3c460310207030640800702c0c100c0e0689007004a46 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 150327356 1250 150326106 150326117
    0x3030306010801090b190312020111120615070210030e0c03030405150304030905120304091a031507180f0906080c01051210030f060c1e02070e0411030a0b0a0e0102130303 75
    0x7404000100c40b03140c4555000c80c1c10340a0b207004018020f50700940c48e001c2d121a0004c000008800032544e03a54010307403d07916610440403000a115090020030040c030f450504422615000c0c0c551700180d12503040d2620000041e0303440d20f0090f44054200808803039008214011400c00c0d00d031000085d2030303c10300d03c900f16000e0f1010000c6802c150090303400501500d4000d002021144258440942d40d402c01d1180f03000e030728102000b03100310040d441d05c00c0c140d80502030042c0c024151002e4200108000207030280040100a81c090403104e01c440b8550310180103903160702e2040c2868040500c0c16120642c001074226040b174255035940b80c1e004001c69009045403110050107a4400d2281203000f846a4806407400c80103403120f0080003655484907402500c5c0380c441c022103c19080c41c2e07078515115100f1075000760380700c05002d00c0445c0c4080146a80301e84141c0b046100c2d04540e0021078100012480102c403140c05200610155605038001c0c0c01d07108041200031800c00b50b10316800080c00c411031002405020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 150328606 1250 150327356 150327371
    0xa020a0f12170f070b190506090f10080601060c0b010801020f09120a020312030115080610030b150a180e090304061b0f050c120615040e07030506091b0303030601080109 74
    0x140310b0040c0d80c02c4107480310546072201a141414216550308079405030a444401d504101d070f00c1c01510465010750005801030040d9540c1003510b6409000c081c016a5400c0051500012a840104000c41c081d02e081d90365203461801c2403410f20032180d8181c124030b0301a4010b005086190301c4071000d0b520450822100c03034007804800340e1403170b00740024a0b0002e034140c083e55011095007555280158103c0b0408181c0c8440544101402c456121041e2255079106200c0310390f00c00800d202c1d41041c1410f00d0010329002c0820642910100242c0c8082c071700501046074174820510f90711041c580840100107040002d82a858036072100c0ea204c0c41103014001c24460303080350341da95040812580100c0241d006502080c80d00c02420007560301d07016055441c2c0310710054440390310920303000f1821500403402417584040d002c0040c4200300c0644503c40000c4800d00c64614000003080702084580c0c09041014003030800b01c0c3d0300380c400035180e201c64003003a8082d900400900c03541e82d03440100c00b81100c2c2c1c080000240d44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 150329856 1250 150328606 150328643
    0x6010302071e0303060e0703090b0f06150c0d020706140409051b0c01090b130b060915090408090306070f0c02010e0a0503030c03190e0901120c03060204080a020a0f12 73
    0x3400d0700090b01241c21188030303000401da010381c440303c240c80c01e00913490010b6075488012000d498107038400a0042a000b00410821103030b0000c0d46030000402003100e00c40410401c02c82509030003050580710942d000b000511101501480540003920b010300c0c00a2440c0b00b0200101400d03c6540724a07a80f1a03601c0e000031340c01c41003c4d00b90020140e00681d82e0b0b0b6654002600c01400707014408402c2d5800052030010030b0704590103e030070304905a80324031690100d83d902802c1003030307012004214009800122110342c040d9500c00e90031a100e14800c03520540c0320043c80050505c1c0440c018030f0130052100501d0712884003074100140d520020b50902c0e0100310b00d001c1d0000306184c1c800d035a00c1643c1500c0042640c82c4c5516000c1301400d00c80782d091000300212048210212181c2c64a60b10b81604014100014080036105014403901d45000307100c1d40503201d94a41e1071900f00c0c1d026600c2079115400c206521340071854000000c1005250840f80202c0041c240b050b0010809204003000b080d1440b205612043e2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 150331106 1250 150329856 150329873
    0x20a0b0f0f030117010b040605130e010603080a02300706150305070b04090b15070210022a090906040506010603230406091e03090b03091009080c0f0102030c030601030207 75
    0x8050305401150b480b940d5410410414009295001c5802c0d42010f014280d0f505051158104035140204034038080c1211960100003007240d803c078081c1c81c0d506c841c1c0c08000b04071802e004005219860f4000e155082d10101505160300048a20289041300c006124049034050001e44243c141c000c40300040440d40c8541c1140500d00507032006015002d031803000a03514903e640030380202c07480ca1505000c056044410803044011644803c07050360000c0c0012805030420118036141da4600e40101c03010010000031500c002c40380c14408086401400d0300841076414803450054000314008000c20b06410b050307580d55100d00050007481300b00355944021030030f003803c03260410419400e00040325140c3e040c541403c002905c44400d095a01d10b4126030342d4182d140454650396031a50300f591b54025032a00f032400207811944003604860315840703444134101044015210782c03100381e40b10b203035250703682c00d8100c2d8494180f03290b84d81c44110b217034070520811400a0b184000c480d4024424a070050b941d500a1420700e00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 150332356 1250 150331106 150331117
    0x11a040e0601200a05010c090503060c04030b0c040306110a03062c0c2710020f0a0b04060b0319021516080f04082a0901030203031e0d090b040b070903020a0b0f 70
    0x140c52191184c10f1042c800190b00c50108403245586020f030701501c3c0d006045d0317600c0f4250742202c800c6000704010008121a05001034212001c450711302d1901e03550f604d82c0700030b582e440c9061304003a050004a1994998061143d04010f0406c60700000c86010741e2000803e0400401258601c152042000544c01c1920320048811644416079910b032808259241c1d001905151102e00f8050f4481032302d25402c403400003400515440c7e0690060a04604035921130032202c8020700101c2d034103610b40c80003003540c0ea07090142e030984000311004202c08865030300411049101d0107038074680541c0e04000c0002c842c0454a402d0060300d411503405a525880031000c84c80b944580e034055030b030381c0c0140d4040c20b45500081401d2103018165141200e00c1c0803019080009011082c48020760580c4100050700c965840c090400e035040c858100304c507062044030704951095038640201201c2548040040004002241000940008881c50105542030469021030044d0b041c5005035000c81401007814400107113070b04115074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 150333606 1250 150332356 150332417
    0x402040e1002030105090c070b070e010513034709100612260901030c090305070602011d0f0604140a02040c0905040518100c020a02030d08011a040e0601 67
    0x1040181c485400c00003e40007800b03254420121030001c1000d034280401681d84054001680d40001e03100d41d20242e8004c030b0280700d014144001800002d0000d860712920340010b5026000d6610026001a00410340b048010740002d0307034481a00218040c500707012803a501088031203507101840d0b01c07481d2105151001d8a0007009046040c07440200d801e40200c600203d445110381c2d84080c4d000c1c1c8a036282d0780701c40c026100c5c080110348280002d03c0c440d8402c0e005110303804000d0070201803c1d9160f4659a0601070b0b19044000580c0d101c070301100c590034120109110520745400038040000d40c4171051074503000080d0020b400103000c56003000b003581c802d000851503503600420801c003e1590850203000c0311071b0b51017510720a91400001a6100742450150616100c070540a88040e0500f14900401420840051411445000020001a00e08104c004030380e540e02d8440600941c903000740309041d048400c04602d800b590500082206064505410341c02c401309003000f003555043c003d601d040b04010f13030f000038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 150334856 1250 150333606 150333613
    0xd050715080a14160c02010c140c101b2409050f1002091509011e02100b030d02070501050318120d15030302070b031503030703080a150f090e0115030302070e012c0402040e 75
    0x41061080000d52003034609058070780580e18800241c05030360051012003d04814423300e03010030002101c4201004024140588160704404600e04083c126252120221800e60001514075401c2d60104484103c0c014012002c3d840c4c1610003000c900c4a1042d11401d0004500100740c1c2841c580c011041c051a80001680b4256031400d01c40000390760798000140380300000d00d03003a203500300d500700481da020100c02d0a0b0010641c00d80f603d0011035003640014010440013600300c51903650a20180038410304600d003030b0095612040880446000c8441883c2180d06101c0f2402c010000207401080c020111503410508a44940c2c032201081e508042d007004195050000003141c000709604009298080e600c044000c000080313a84d80120758180090090303840062402c03800300300860f82900004a100c8042001046586280352070b600b1041068100b180035801000050101500c0320007180c4c01410480140c074000d00800041c0c101c001e440c0c02c6084125812140003a0039500e95401494802c1c1d0b03044100c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 150336106 1250 150334856 150334883
    0x3010b030d050405010807080906071232010906081207080706020307020303100504021305060d0603051603060507030c0807050c07051c0b010b180d050715080a14160c02010c 76
    0x140a98442e004e100e002c00c5111021401007403080e1402882034035040b00919580d114228140d0784201c102c01c42e107501c035488807200c07462440101040c8901101d00025880300d4000407281d61020704050300103980c0989001c100b088800800900000180c0078640d03400c2da14025400e00c1301562050650107030000340000107005202e503000000310b2107185042540100c40f80c031038040209a12407405402516240c5403010b010b03610b840e400401165400000000b00e035507070381c0c1c6c6882c20700440f42551145000f0681d001c0080c03090a010715a407126140c58100816440100080c0080c18040c1c108000c01402080c102e400d00b9003041030307102820000340180120000c0000d070840030189602e0441e28612100b0002558140081c01c0d20444000e82c4071056001001c00d081c06140d855508040c1c075284201d20000412041600c0a140460b017180c1d58280149400d000b414155450301d0310700c0d8112008241004080035003244060303119181807a140d10ba0100c14001202c03408610b8602400711024030a1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 150337356 1250 150336106 150336133
    0x2310300b07121a10050c0111090111061b030408120901020a1206050a1202060d050a021312020a030303050912030a0b0a050922140303090a050105060d05100b03010b03 73
    0x44092044440b9501c02803848420031a91054076580d610a03980000610065031072807030901407100080000d072609034182008914198292141151303c2002c81600017101d2641e560700a00710b0140203400350081039039052540d50400118880c064280400b280400440d0400c8214822590b501ea420801660f450814490480c000e601c42c0d6049000704030301c02d04035000c2c9188c1c2c0c091441101d00051403100c1007441c4c183c00a0301c0071203000c000ca90180c82000021188211880b0301d9002e40050040146c0760303c9610f9804418140503046015041411001c2c0f1005a807882300c40f50a50354145800700306501c030070300142e01e081d08111034582d1141c800310800c13941a600d680240e0344408112070030903004da40c40040c4400072034140d07900c5e001d0036071250541002c1100d8401c00c2074561f226a1034810802d03100c090300c50951300190783e00f4020760400001602400800d0003080c0d0042d02c06c0300d40e0303510700b1420ba5500b5620003145290000d8540c44601c10106a41c081d80301c8000228054140d80d0a840700c900d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 150338606 1250 150337356 150337373
    0x50c013c0905010c0308011202030106080f0105060910230402090a1409010b0301080d031104050901090509060f07051605150c070501050106030207020609061e0d231030 74
    0x102240c005408510005542c1d88503e01840d48030341c15407515510b59082510200e07000b03d4003d02641c156413103150006800c00104008048400180000585820000100300d03d0110140a0058920b1601402d0120302c100c1c0080c0c05244181a105100200441300800e02900540c20042c0d0300811540001038a10600d5003112a09542110449800da072a5010091540000c4c021968140d10403200c201d4070600030340c82004200c001c00b001340d041c150754070700155403604260000050182c440c8180842c5010404c5090b0f000a46c0400010881c035215000500e140220a0446440c0980541103010301c6824007507110041d8101008c0c2d005458a0340c038841480d445540304403015840d19000140080c800e00c00d940300035034004d10740d40c600414081003001d56003051f0314034006500003400d4000440c0c82c0d50f0061512192000e404a0405402ca000c0e56006544210706c402407140c4004000403140c07800744100aa07504100c01c3c20038040505208000052068035042566520300080418010020f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 150339856 1250 150338606 150338717
    0x7150f230d0506101709070902031512070303021b150c010b030609010504030c0206030c0c0105090d23030a09030c0605040516080d080a0e0a0f150b0607050c01 70
    0xc56081c081511080f0600015500c525a02400580c9100310094203020840344260800005000c8520654681c0381c0300080743d00076030355031440da54a504401c4981c00c02007203d401c044414400381c4200c40c40c6803000394841d81c0e0320b0030014504e001b400324201940d9400c40b4140102e020807003030301e45030000100c9590090024031001c030311a109800001d17180200502407035100d141c4c599284141e0742c03d5542809100d80000c0c10940001c54144844044c0100900c01d540c0705400d03040090408070203006024100940010140c61007604601401141240210443c1c0d004101d1780c1002807121400d041c1207a0541820400400d0f103400c7c4401d01052000c00a20540c00d0700004607110300302c594900c1096581c040c5a1601404030b208200014215841a070041e1110f0600e4000d552320440165550040c0002040c0200d56403101c0300070300d60884141c3e02c01c41d140d60406551036481c0c200c80e0703116a5038506030846481c0c100b1602110003c00107040e00d00c10100e000f001440314151401055010545c00b400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 150341106 1250 150339856 150339877
    0x17090606040e0a0c0306050a0f0e0d091a04050f0a050a090e01051311041a0d1a09070807030602072409150b0d0624060f020f07150f23 59
    0x80c01c040b101e02c0d82010410f90007603a40700700d45031030a0b85103985034409010010708080345550b40320140441c0644500440f81006403000160607500127045014010700c90740c0c0c00142c20012103402c107202e9140c500040b6001c0d00c0e000c81d49040132840a030001000b08616400c02c6800480c10940082c403292603070400642c1d60000310081c4a25510b0501214a01101c0c040181401c07046050b801018103043c6d01c0340030118844400d5282401d2403c012409210207168101c0d40881c0403110340e040800303610a030070340090000025110725480c00c1131042d520040340c000944041d60024100d805c01c04600200079507200344e0481182100a440707400001421940004d5940d00c0b8a810118800f42d101d02c58100e01c1c402c0100342000c4402d203521194010a9089485245854503212010a804801d900741c002080a0340d03030308c419103149400003410701e413084000d61440d60260310103102140b40c030015551075090901d0040c290030310f00082107407244100e04840e0115030a842002d00035042c03c2006210f1401c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 150342356 1250 150341106 150341111
    0x1f020d0615030b18060d05100c050c010f0c0c2306070903060509062202151902120c070303050a03090f15060608040b04080307050f130302090a1a0906011709060604 72
    0x883c0c00f449a0101800310349502c80c14200009030051601e0448100c1042c024400c2325401040030448170220303403140386000e01040307001c60294541102401106402130418030180304505283d44060204569010002c03c40f090202419005030344451403000e0b8000c400c0115965810142e0340984102110302081c0e46c8182040c00040603940d002801d18081c044c0300003500244d6442206201741c41036900d84c12640202c00b1750303c403403629500350064600d40d540c00100a041c101c0e841c40191600c200f81c041e0507504107052006402462020408404898040c02c000c3c0e940c0e11140d09c11002008000c07401001a209624000c0078007542c0c12692401000ca1502040001e4940c241943c01305400c440042c0724400810000f000504080003035500705140381411414411b8444046a540d000419a0580310b0003602c410025441e2070800c850f04071031400d00400a60141e1310301140c0c960f034040c2041d4005c04844020444c264451540213014000700e100d4582a828280d00241c3c9403d4240e840741d11690 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 150343606 1250 150342356 150342371
    0x30f020f0a08091e0a0603021608070c0e220602070c2409080708030708071704090506030114130609140a050c03071502060a090305041203050304021002030a021f020d061503 76
    0x540207507013240000e10040c084000d403441e200c0120065401014042c408082d05007038a4000350304280900400361003150921803142c2864001030320404000c1c207050780550120003080444404650b10030055800c100e026a41e40e43c1410540788100da40c1d407003511200c4180d9080e061b0610650041040d8a2296490b220101e56440466564100382c1c000e00d440ca030020006200007a01d254010819075200c1c0c591600c0b8182f8100e041c00c41c0c0e030403a5201394a05034075041040072624081c8141511802210f004601030f0500c5c0819000d1040d40d044020030481d943c007035240501c14a592200c14a541c08400c494400c24945007a5843e4564000d00c94020700c070b2404080f4400d20624041903901d013055000742040e551341502500a07181c0b101c416000c1c000b04100100d041038034001105d004500339107801e90f40342418818000c500b07030b400c0310704404c40d00144594800300c1c2d40421001d01c480c12149111120b84061075400000388591505c0c041b105140810015802ea0606078122921525440800c00708 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 150344856 1250 150343606 150343639
    0x30b0907060f02070e15090405030711061204110301090b1003021e09041e02150901020d140a050f0c01050703050402130e060703020304051c081005060408030304030f020f0a0809 78
    0x120b02074618001507045444207024460100300344c903034003101d29a00700082021007000700c1d0005a0982d0180c56075000000c4040a103c402c2103540b0b800042502d40529004001600760504080030b08020100040815040b14558094020a8132207070005c8607420f260502034501990b41d040340c032080380562503001041c00c0760800380b041003540d4030000d020034481350b0b540d580d00d4801c050651520759840c116490000c002d038803035030300f0b02246032145291599640041070000e85051b82a50801d030070041c40313081e01034041400d1000d4810f0710b4280e08083d42c40c0c01107110036020340e004034460302c00e480d0320f842d08200d2074540c5231300224007c500a6681c0240640304e0004101514030784030308074107290b0000011070042d611075401181e0060190080d0b44c5a42c505c4180c6100480d07010b00b0401c000f4905105100070303645c1c28000e100082c00101c130440e02c0c1902d010315594403404014800f80c18400826a514149802442000d0908042c58140ca9134028545002d1070340d500300c92070442c02030300f0340c91014000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 150346106 1250 150344856 150344867
    0x14011b1b0b032703070b0601021f020310080607020a061109060f0301030b09030a05030f0408090d0309050a0602030c070e04030c050f0102070303050c210c13170c0603060a0e0a0204050a030b090706 86
    0x101d2800c18044c500c0d000300d6031600e140c0128080c3c40b160451007512300c0d0f0780c0310040700038502c102800403000259580c01d000e4a406000c844980021030145c014100f842103540d00050381041d050b5101001046050808000744050b010b2440d0b0325803c00e5000404009000e01030300111706032845000044440e8541409080d5a40110108000030640802c040f03542c100e00558042d910a11900c40c1c00e01d0030407d000410b8249040c50001c5003c00c0b42403800b40624a8034814000150041d44015400c07da00100000d960342501e1107101c40e445030940102e0103151190b554244415040000c6a248030001441c41e4002d50201c203003500001c2c5464085080390440000300e48101740c1081d0510030300c1e40b0701e126410305030402a0420700320000070460701d40c2003000220410b000305512007059034034860704400c06007040740100d125485000204204400d41d929026807505490401464007030b10382d280c902070002132280790407055101417030f10800810441040c40d51481401e550050b01d1f8070766514001581c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 150347356 1250 150346106 150346171
    0x50c0703080f250201090c06080601170a06030c060801030c0501030605101b140d021002040806070c14030f09041808030a0c09150f0914011b1b0b03 65
    0x41e2448010034004070800070295041424516000d070030854400306060003840000f252400b41c0d466081c05810b110321221f240008240d60b081c9a0854544540000c1c510302200e11850f100220b01c201050784602607500c504080c6a0102444807417030b0b158000501100d00901c8100c0350b5483c11100414a0351180c0202011904007420030104901a00405d540e002070000111550341500d81c00d131000700e0a05654010542e03030040103407c80c0c05d00d00344001d090100811494024900401c4100200980010550381c004450325004504000703601e40001050703030070300b0000d00a1202007a00140030010707074000d0400d207204440030411420381d8108421a48440315019081300c10030310000e16200c1d113980021110106500c1c10810313868a65041101415946e000c20740080e10400580704502d07004607280016124951040103992a5580000d05900200d0b2080b030141c4540050441085125801d00d500e284850080b0207202d61a80800501ca400854010b44090000d44051100740c001382c19048 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 150348606 1250 150347356 150347363
    0x3011e0902160b0402030307020a030c0f080f071a16050309120c090115050f0d060302030c0a032103020706020a020a05120f040509060303040f06020a05011a03032b0204030f0501050c07 81
    0x1400880d41d80c9881c0e0f1400401071041c0e03050300040202a0050b40d4145040340a54402c980f810341e0141000c8184203ca040f41d00106400c0c0d0000c0000c801c000d00c001008812114000080945500d5881c04000e40303014611940400301e05020480c810003070084064460100103440307809407800d02d00601551b80540085030f5030400d100cac0c0011711042e105610f270070b001502c0a040c4076203014050092407409a20080082164030355502e824011403a040c0100c01680300300716140c1c007200303003551141141c040c0054540810010590308643c0c40c80d00a8056031200c0e40c01040441d1503c0442c5400381d225800500c084505000c2c082c5060707042a10703101514000c000180c0c0c060f0030030341800b081c41400ba40240010360b03d48002c0c04005005581843c0318030240c0a103a01510909550340b5040c3d0949034200d43c4401c0161810301e0751111074400005444059023903401c00f000003002d080c450301d0550303988078281c041c01b400041c010080c499a03007000003286204e003000304180d540c3c041030300384680141d04006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 150349856 1250 150348606 150348637
    0x40b0a0b03070311160b06030d08040213051914061201050c0904150b0c16150f0e0111121b0325050106080a0c080c0a1a0d09050303011e0902 62
    0x242e0000c0c030980c0002c0c121021074128170720708050107030708a00c80305045800701d0308060034034100300b040d04007070003038080c2a110750130056a541455400076550b008810b224580b0695100f0000d00d080001d04a0100201a910030400030101b180200f180386003011200707a0300991001c140320013042014810940b06044c203d407014104542c4004120252243c3c05401080440408020030200011001810030301003803801080340740c80d016614003058200398070500f0001591342d19041e0194002c14241d071703031454510b0141c294180020050380d00e181071102c0544640300f41e0100200f42c07a509001007000f249002c0c1800400030030314625907580d1045558100300b00078078031203010391180b8041500c050342780729000103e0140d455040140c81c20f04185c0d4107803016420400d00b040014401e0044810340102075490002a034202081e00c48080ca42400b180883d24001501c80386100c400d502481c0c0150f0b101007500d40d0303546d54500300361034408191031007012401c0000d0001a40812031007290050074000108 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 150351106 1250 150349856 150349861
    0x20f0a020109060c0219090c0f0516080a03091407060e0409020a030305030403020f030c0c10030e06041401060512030a0207060903050a081c0f09110402040f03300e040b0a0b03 77
    0x1255038003442030003203170014015803141c00c24010415009007d0034076401700250318140000c00401c03200c60070b5299000d0001c20081112140e02c0f501d071a02c2034076000740d02d082e41e56507007440c11030080c22464005004051000c50034160304401040e050101c800b150766040c2e0240191040200310380c40d2820007940712010038410000640200b000d1540035010b030056645509020300c9060840e07201c1c02c1d03852810742010b09035901e1407810b24a0701c079101089207007c00035805200000c039030f54503024001410842d106000103405441c01d420880c00392a02074920b10300352036400c0019a40e81c00ca0300b400409802200d001084481c8204820821260040010184600c0d16114454254098844050180100001c044840c13059024071920240350100000b1095240e080038200c1e240b4a50b112441107004010801100b00d0700d003040c80507241c01083c1e02510b61a102003101c0f6150201c0c40003207041d00498000c4500d242c209070340200c03c180983d4180801d09000007000f900f00024058481c3c030140030b101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 150352356 1250 150351106 150351119
    0x30605031906090206030403020a260306220c09090617030d0c0201060f060203070303060b03150105090301020d05040f06050105030a02010c1101020a1401060314030304050309060a23030403020f0a020109 89
    0xd9003801d01d0240d500010126082c0c1c01240d607545c011901580541d0012801c1800c024041410602035411400d1900000b001d02560404511000d04060302c14070034011812240f40140015030017441d50040e04120000c0021005080c0341003c1c440d40b08424a0b0440004484000010b622040b19249019624081460003403034014542c3e070046904541d0390b50408a40c8215400540000c2c10303898000f19101c4105140080980d2025040303a07a201030240f0178400d40002c564001c18841200b400c00d00c0e1140428008640240162609a000e141c01d00341400301b80009a10700d0780c00d4074000c200034040caa132074809141d80c0307203100c0000038001151401d074880030611906107548103540500c180e400520f481c3e2291802c0110291810803181d544a100700100000d10312600010740861300a50709600e0107403580da031240610b9401d503010724000503807070a140c0c6c41030b007491f8000410b0800c81d038910702c21545101c00542080b50110058411803403042c00d03d20700042c0c480010b641c140e603584106410402d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 150353606 1250 150352356 150352393
    0x1150806060d09050604030305180c010806060a02100501120c08030c0d1101090f050d1706060301030204020705070906091b0203070b06130b130207020a0b0c15060f030307030f030c03060503 83
    0xb6031120711036882000000141007401468000ca000e564042080e040c4220b84143c95031071598024410b0740900c4050110b83d812109a981c0501c040700c585032503d44142080c4d041100006c0c00903c00c502d820000b0a00d10004c40c18111864011078000e82c0301d9442d03020f41940c034456030fa41c01080707520100c441c1600f00d110360050200b8410400c00880e4004c00c5603200c40582c0c9112404442070f80003c25010b8000703074440c0314100c0d0b10301180310806e01400d03c44046203a911042c0006805541c001504205008003000100000c0c11030503010800a070392200058002c142c45004a0401ba4425004001603480041502c02c030642090400d500c13070b19200d00f00200218813212482549444000d0b40740f40d40e9038004200c101984020000d40e48005c1c92041020082c120740000750288000d010402c081c0400086920720309110f5408840c40c0d403240e074000303900c01e0100e450040d49484005842800c259205c0c0d0010011001510244120140024180d05039041d501a194241d44200509800c40c0900b4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 150354856 1250 150353606 150353617
    0x40207021206040302070e10120623010b070b0a0c120b040e0a140708010903020a11180a1406010801060f0503040f06060b0c10020711100e030601080f060115080606 72
    0x401215540140e003400d40d0402d001250b00b500580c014034010010390000070502640b0659035600c900c40c4500704810340c444407241da180984540d0b80c1d016000f4580c0078411905002c8098118a1110b0f50394507002d0b90350a9210100403107400d2000030118081410b103001d031092042d442d80b21000c100c200c500d591402084100641540151240c80c81d1203085028010b00000900038981500c10254003080249044480c0c1e000c441c0580c9810301c010040307513020a0502b8076580c0b10f00054103650b2040001951001c42c3c0303a03000015101441440b40000340c5500084c0005e40780051400503075111801551801403d10504004c10311114100081300c1c8510000d5621031300c40d468a0071016000d860311801c540498008960303000e400285100f03840c504001e09040010300400039490000140c1e5200b2200a02d401c05a01030550a60741004050190350942c050311000f0f401c41e1030070f41e5103e100555030381c1e1410307080c0d000780101d00000c14280551074027040c85600680799502641c07a02c0040c040c169000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 150356106 1250 150354856 150354859
    0xd020c19060f0c061a0f0f030307030c0507150c020103050912040501050c0f01020a03020912070303140306180f0114060c0d08090f100204031713030201110a080c0d02071a0904020702 80
    0x3e40e90352000503d45105510400c0d6a8406400205600c18148815914802d1001e485100400d40c0c00c800c9a4002080b514413660503d400380700906a858000d181c0103c0740c0240d003c2c260800140e05d81da0b50320004102246000340d900344240d8541c40e007090740b240110314615881c07a00c20030092000b0f501480c010b2201181c1d0350304940c29646080582e6089810425050740020b40028261085260941a070010303583c007600500f14192030b41d540906000032034984409030950100c00a0b400d9641c0c0900355100309561404030540d403030003c1c40e001c2c1c210700900940c41504d80c0000601c0042c105002a202202402001000400c0341400c0a031240c0034020264203041c07081c2445a0401e034000d200780ca40c0d840700400b01603103480c20351400320f10441e9002d442400f0801301b442170050f90607100484034201c84d02824030034810040104014200341e01d00b0809061550300040c008055400010340701040411503081d500120b448100600c030f0750541980140403007100b402501203500d050703802000c12510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 150357356 1250 150356106 150356117
    0x90705031003020406030f020108010b121b07020306190608070501050d1d03070309030c090209031504080d1a1201020309061506130806072007031518050d020c19060f 73
    0x20b503030340000e0943d039060300b00311841031007040300e20304550f0070400c003d001d80802c600490074008202c00402c2c1e402d400030204545028003c00303044002d050304040304c010540103001d607105854541c01121421038800d100d402c0e994075140c40010380070004940481076980503035034149006440030700d0b000075290340c5d01c0b001c0c0010500d22071020410b500304010b00782184240c803003000b036920750b04081207100a150b2000220f54010005402e0700d55011503e91030820b400a0120300076140c40c100305c1410302481d0301610482c0e1414440c0e889aa40d28a059075010f04200c034003200000c0e00c010b07503c0c20f07800203441500c0907601410210b07200005c502028048160050442c90508604d10046020350b0340c1540001c1b001d03000041030000700c95200011541d00d8603034408800130103040c0b106240d41e0703042034030015003019910b5038034550400750742e0004095261070380f01503440300b00c160610588609403a1703072060140c81141c40c51440c6050508031003148000c007010f079800c0a490100240d0702d40000c21540070400c82c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 150358606 1250 150357356 150357359
    0x10210303020304060f1404030206010801140f0711010e07140315010513020f030703020304021c03020d14040f08010c180807060c081b0c130e061f080f01050a060e060907050310 77
    0x240d00340300f400249031b803225920325a8141802c01a04140d41a00100d031140d041241c2220801daa0499968004026040b000788658803c4000c56010315904400c01c019400c243c440020480005420b81c15900c42c0308002400600750381c00c159407860381200e0f41070405600e0004001d43d01c2e00d40d40101d6402c030203010242c0ba00c08001c0982d60581c0c4125119000700c0d03804410f020660030b20300384a410315491500340501c3e0170303000c1c1c0b0080d5036802c3c0320428200b044185c001301c5025100c4c0c141590300400001c035a0400705500d90150501800303124203003100048103000c140035005034160581e0300702ca2559000d0002c06040c030404035030010040c101504d100c0c2041022888517000c4525100822882c0009024000c0f102c00402440100c1c0390560b068242c00c10324082c0e5908008540c868026400305d0480c03901c1c8001e000c40340560301d0580c3c031101203402070f04120030b542d80040d0807091143c40380b910100609910b03403131003603074403201603680a42000c1000d00060841d4012402150080015121200a903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 150359712 1106 150358606 150358631
    0x309030b0f0f06090703110c03120f2517090105180a1e0302070302091e0615070b0a020c030c03041a040509070c0303110f031021030302030406 63
    0x29195500402c05c114040d03440145503c5296080076294030801d00b9445c0c50740c000f040400354401c500310000c0c29045034110310130b02c41c14400c81d0b0a00741c2409441c0001551807814400c00500107018407400d9640299880540718844c680000700e06840c11031010124000c4018a00446030310180802c400900c05046011038058111401d14034010642000ca1400c461948044e40103c440d8007401100f82c0c640c1902d0902c03034140040c1c144262540d41c240007911500348240c0d41044030600c6002c00040d41084103581041d035402015081040f142c107100c0c1507034450f05c5100410342c800182000201b00401c0f0000c41452005211402d20b4548404600c108070014489000c1000da6074039070080500a500481c05c100c0503261060b100d90b04440c080403154010ba92004814a034480c0004111005008140710b40400d0b666403042040c00b50b60550203074201810440701c094030380340d480184 = true := by decide +kernel

theorem cover : BRFrame.Cov 150179856 150359712 := by
  have h0 := BRFrame.cov_init 150179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 150179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 150179856 ≤ n) (h2 : n < 150359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
