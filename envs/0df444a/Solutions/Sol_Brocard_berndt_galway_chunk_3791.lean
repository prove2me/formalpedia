-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3791
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:41:08.894471+00:00
-- url     : https://prove2.me/submissions/71ca0d09-cf18-403b-9d4f-059da63138e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 681654676 ≤ n < 681834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 681655926 1250 681654676 681654689
    0xa030f02060c01110d060e070809030d090f0606170f030703020c0d050c09041101030c1412330f040506010f0f0c0c15022e09020d0501021c05130309 65
    0xd844480340b0707071001c3c050300e0505150004400003141800032289240d000c14212004161043c040b0b44841a06032034410040d100e600440c0c00802029804040301c0d00301125042c81030900c2c03840c180603a02d9a02c116809034001e000c42540d01040000c2080003000810360768041440914641011a178029507500310b4003140500981ca1408035005204c41031001c54903c120180c08940c2614282c0b8191220003180b4407243e010a16014102030b045102c0d180a1414100100b8102d20740615010819044034004092005410040c2c2100012400c407d20800746503600040d45c2102030710400400c00046004083c0380c0c0950311341b81c100f003030300da80c015a1101e0740041130801c034050442c107400403607805640c1140a03113107000d4150005054040400d681a0381c1d200355099071541325618101585e00300c10740a52000040c50441140b00c00790181d030103e8040d510091120305060720395922282607811401010803e020001c034500300b100003900809920002c410344030700301405180c3d0301402851aa00550 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 681657176 1250 681655926 681655939
    0x603070507060b130c0f03051315200d140f190c1115010302090901090c090e0717010207020f03010501060f0e0a050a0f090c05040609030201050c011413050c0a030f02 73
    0xd070400c1d02c43c6103088a00309130640c014030003030003140c0c005840f100720409140d000900c0d01000600c0038a0b0951954075159014482d00020100b03411120094180e106030341d11001d40700b401e0032011144110041800429844021600141c0800d132811081c1d0000c14035107400c4410005c106001c002010b0b0021441d0040340c0002d09205003038022549142c403070350030f10018801c44402101c961001d009840c12640701300c136070343c3c020b5540b48106803c3e140316103002884800414014040d5070580c0e08a260460351080c22660160355504121101803000100c0c60703100c1c7d6000a002096040ca0741c14908044810b400910841d450050010850300079003e09008001203c2c0381c00c042c2d640c89461002c0145401031030307038607425228002e0300041c030304611500400a14000c3c144010602071429101201d40d20340307944451501d10780041d40c8961181e01920741c1c4e550b8401c0c5000c500412050300601412810081004d41207070f42c509107140423078014095100b0001c3c1c28040001071640a803085040c1da0540303d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 681658426 1250 681657176 681657191
    0x50306130b1f0b0d050603010b0108160203090303030a1a1207140609090709080609060411010f020a21030f0e030a0507020a0305150a0605010c030e12031201030c060e060307050706 79
    0x324101c031054101e000c2e0403400d01da40004052007624094030041103856800c0003183c6901c010035088807128074a45010079010000582004904c000b03405a165440c01540e00c0d2041100000f415640300300c807440c0700b1564550000014405140790000038400945603203002005801d6255610031561040300401e4040c140340c01c42c02c1d11610f080c2c41d04064050701c00082c81c2420613002d46410194014186148a000c0010700c00b80c400141c0d450140d6082815891000c0e12000112844210000c11409510071061803d002603044034003080040e86407000341070541c5085c00c004041e10b00840080c14407500304a038401c19100d02004540210b111810001e40c1d07042d443c40400d94003110b41c0c0c00a089402144510000786041021007031041c260701c00f04226058032500151040800340c80c01800041650360b07280003074203180c819030224440140c100c2e420f00e0078410b009070000e00c0c2600f04507684c52944008021081e0003c0200c141228102ca0603411403400200003001c50107941e0307000c2e10080d101e116 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 681659676 1250 681658426 681658441
    0xf0a0803090a140a05060f0121030c080d050405070504140a050a0905061e010b030702030a0c0c0f080a0501050705093709020c07051e01110c0d0c0609050306130b 71
    0x1080c2c4203034442d001c800a496107051680d292449188203035803902405000400e41c29a85581074181c0f40c6081090000c1101420000c000e1400800114144001d0210713200118041d08083c00700381e14041d80100380c61525150803401d02d002d03948203600560901802030540c1c0d400c12407481c0d0100e51000006016640c007d0110064488800040c065004090620004003100c440c1d8609411140080c00d0b000d0740d07940625601340c4801c40e00a00141c00901c42185204d100b0010b0310002402200d4500c141074942c00340c55410107050344500019403201c3c40d080b003085028003989501041605100e4103098014001c0750120742c0c06941c481486a407210030580044008541d8100c5800443d0034125054854000c0d2009501000c0281140e104090380028140f81400c0c00b5540e200c5800d02a10a03515820010f40e0300a9017040101e00c64021441e43c0011511402000b06105014404881c551843c00d040581f0a80142d00040e01a811520401141c2c000c000024000c440e84081303040d07101d40e10b690 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 681660926 1250 681659676 681659683
    0x90b01080d0201200a0318020402070b0a050709050d06020a0e060a02030a0e060304120f03020c03120a0e06011a09030c060f090112060b07080708090a03050f0d181703040b0c0616020f0a080309 84
    0x1f10000c0d4024400710f00c8006020503516038522440d007846040180e901d41c1c01c400c2c1c4810020b8425103600c081c800030958001602500589603502c014148136aa0103c07406c0010315075042007003c000140c1c0007080201c0a9580400d001d0145030301541c10f5455418540c45649524443d02c0c449803d001000d04818025840b07541241d1101181100b9241c4421004164921102d8260368480c007040c280b0400c440f1714003000c04e006040f90141c179080501d10200104040c8a03030440b840c6690b15005104200b02d40d902c2d0f01d8010034081d000d502c0155503400c802c10000d82950000e0141e007005c50303e000c0050140d801030a086424a03500080103546404881c94103010a20850803030715000414424000204900020203444014902c0c0907580c0d11094842c044902031424262251a003590700b10411800c0e84180c6140c0c0e48e960f4050540e86403035254122201c2c10b0f80055106c1000764042400c1128080d401d04001d444442c2d54406401c180601300b6640303940c0c1351000e2020b040400000301050030500c080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 681662176 1250 681660926 681660971
    0x190e180c043003020c011e02061f0e010b03010e1608010306020702120f06040c060e01050d0f09021e0301060f180f0b0a0801060e0106020f030715090b01080d0201200a03 74
    0x951241100561510f4025101c041d00c0342c010340800e00c0404c2c41501915904102031014005c0d82c01030030903035200000c0c2d40c541c6440020720b102c0040d0703650300868400030345c402d0103000e402503070201d590729407619000401c0ba041c0208541002c40d15554020112a0301c0048581120b40004000d62500e41c0741c00002c4440e14142d01d40ea0f0240b18401e04401880310128545100341d006440c3d64402990f130350320550b04c0c201c1490480340022802c10450005c000d0350340c0aa6411000c1000025400c0e207298041440c1c08000c402241c0844242c1034124050301d000d00825000e4011382d00140080c0740741031401e10820f01d0302200f840b207a58890011901a8181c2c0d0b003c7c9240c002c0040180c0045980c0303074050341c000c0500c3c0c041c02e15040c020000104665000144980605c0c820000451508071191620758202028007461100b03e43c45094042c00f04110002980c003a2a081c07010b071000604c0f0042c00b13800c44d42620b0b400c0301c3c4044284024a00702110078241ca201901a082c0840e54200c4452840c41d1031000c07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 681663426 1250 681662176 681662249
    0x50c04090c0c0212010c0f050d09060c050418270f060c11160b0f030c04051519080106141b251d150105190e180c04 51
    0x422200105840e400360b18949414001d544485146030641441402e0716200c41d100c00116821030601c00c44248100014100380204540024056242d40d43e0401600d00e0400c61400040c4081401d0002c1052203030100403440c8407030301c20030280110854010b04008103008540354903a5452030748040c002e00d105801019a40844c00f004450301c101c0c40504070f40880c000001844c0b203240741610600c1042c405403402c0d1051107152500300201c42c40c440700035610080240881c40030901000800351100101e10601200c110306854691100031100c105201c207450001c020401c084004110480c0c002c4841c69104126803d113650b903032881c51000520840004003600340d88200c0202c01b00c680d01ca01c4200406586c07606c000c0c0100390b6100340001480b004000d15804c2285808041010b01c071848021034400308060404138202508a40c0c1140c5084088070440042034191041c00341628018443c129200c2d00d0200040d09c1e4101009185503500941c01210031503282c11000c400308544a18204402842 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 681664676 1250 681663426 681663431
    0x1090e031903050106030f02130e0618011203080f070e100e0607140106080a0308060d020f060309010510330207030212100522170d06030b090c06040b0d050c0409 71
    0x220301c900107000b450240b00d0000000d182450609a603041d50080784c00d0317841080a03c052050816410010250380a0300196014240c5080020349000c2004214020225000712503840c03101428040c0a01c60000c10800f4280c3c0c4220412504513002001d50501d01029541e03101c4082c0b1101c2c040c1c03511004204a079511180100c9c80381d081000301d0601b00c8440e6880e400a01002d9546e1408555440c1500d4000300810044400580d203030078030496840c10300b400100114040508507020070390b5030740251148401c0c3e035110403c01c00c070780303402002e4440202100f00d40b44d486e101141c0743d85500c024044140b511070307400e1003d0604001d8801c0111202454000301494502103101c2c642982d16844070507200c15082c284000914000901c0c0700c05a001c00c28080f10340c41d81c0700913036103843d11800c41402041c00304006120755411500e1f140f18400155205424080c154101050101e10f08003150083c10321519003080140808031000064803209806079102140d140c5611106450901441d00f02960051 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 681665926 1250 681664676 681664717
    0x1e09130303021c0b0406090213090e030421030801050f0f010c1a0c0a0e010305010e0c090111060c0703020f07120b09010204050d030306031a04050c15090603010602151e01090e03 78
    0x880984c0908980307442264200500ba9032043c01e00243d004480d044115041a9001001100c51540015103080100c1e01030b01c1c0b80ca916901a5403100c020810201c0030102101d106a08164110407039501400342200c2300c080d02d445007000100c0e540507e03d461410007880102c003c04000076180911440107044c3c6403401c85150a0200103c0c907086510f0060019400b61880d4800d9400780c801e03641620304880d00d8003e2940d0b45802c50340d041c2e100d80003560401400e1044840c401d881846018011000b01903582d075a107115040c02850441600c10307080481c2c025050402a82a6500d801d685031544803c2009490351000100d50090059500c40d5801c12442182d5108142d4558040810b40784130f101c4500c84503032100000c1c005d03850200e900801036800003280300b00b20300c1c0c04244c000720104405d48291401c81840c011030100d03042a03000c0d2001d648840f01c1d001c400710584031055072001d180c0c9641a8621980221080d030790a06205540802d990760303c0e98030070501d0910440c3c0307446148914415504 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 681667176 1250 681665926 681665977
    0x90f030a030c021503070f1b0c030b01051e09060405060102120c1f050402031e0102130e090c1504060f270602070f050619090e01060305061e0913030302 67
    0x8080b81e00c0403481a003020f408000c1c100c2c00201900c1c040d03d06039031421111003038280e050f1540454440c460701c08a1039a00c4280002d503035040414040c51107084800c03c0342d4900401d00c0382000c0e1804802d0b01c0d500d0258040046902d071420b2199020400b181c0211b2039444400041c3e04140d2040301c0c981132842c0008101283c40c1c0001042403403400e22146140c030a15075495000c04440060b070f002941038001c3d0721062440c0c41801a5011008443e0000500d000e020a0011242c0c0880798010041e2102040800020340320502600380c21040555840d04c02034008142e43d120380c4a035005000601828001c2c500d01103100d000800c030b10303034114501030340d501e440c032410544001024800c0707400501c40d1240c00b0a6039246103003000c0440b08040c002c5030402d030600031814035078441420384004200c1020780020302c1ca5540e1110f40d0007490103450000ba0b5062203000d0000d210016040320400001181680106403902d940082d031003100640301e52808901854120301a1040781c2031810752800c44054002c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 681668426 1250 681667176 681667187
    0x60a0201090c051008040b04170a090e1308040e0c0d020f0c010b03160e091c1707050405101d040f060807050904080909070207050301060b030402191406090f030a03 72
    0x88900034410741e418680d0300c00401000c80498a5040c001800b82000f1400141c84034404c0c0360440d00c100b000400401520f6000100e92b00400002c10000b000722004000441d03890f1505038201d80e0b81329281b00c00302c9564a4080c064492442a10541c80b03c54000800c00803044c815540055940e440c259a10080c0d4414031249070403a10608d102d80d440d001c5144242c2c9000610f142440c2d09110005641c2882c1c180740c040080310040c144003a501901c5030161103890f1100d1b404854405a03210364010304012141100d92600c01421340080c4641040223204540d664010910107880624044801140d0b0b000c6440202017074044080d085030900d00080d15038001c58004d0000c0e0b4a60004440c07405903201c0810018a00580740a0b0106500f0480c150031800d1210480d0380c006d126004440c440340d1340d40042030841d8400da0158240341000310508c421498481c03c40c9440b000d100c04884070850422000c40340700c4441d141200d110b60f00c0010003000a458801054450100003800d80e0a07529882c10003a21 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 681669676 1250 681668426 681668441
    0xf0203030f070605070e010e040c0309152403110d08090d0506091908030f04020315011d0c092b05120a08070908252303011a0d0204110405060a0201 65
    0x84813802c05000400242c0304150003400240c05070341d00d1480c2803041081c08024090f8241150030107486400b52404100c086d0107400412520010000e500c216016500d00784162820070100320b0a51140d040003c665456510650310000700c48034650103410b490f0a851034803481ca029074002d401e2050810901c180852050b119030441410780300704c0c0244800369140310030b8400c4000c005003000d00205129503003198110754040e00c082c003106d48558008400e11203122007644030503141d03034940019083c0514038800150f0414204402c5605110b2030303000040c1e08a090074021100728407064045056050400c04600d9081e80000590ba05203151601c4070015500072095200415100800710390407038890641d40048580c0600546420324800d500b2800081c0501c01580f048201200041819942001c90507100102c90700e0000c007600464081c54203450342c10002d40c00c203400400c40f040158481e07254051103203904440c005100c1800702c40c07c44880c000c40d009142c0188020079050500380d0158000b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 681670926 1250 681669676 681669683
    0x50d02070503070308180109031703060f18041103070f090504061a09160216080c0a30020312070503030a060504020307090905041119050109090b060702010c0f0203030f07 75
    0x595868507042816543d90081c44002c208030300030001e03440380312800548030001c0c0c08145000b104103642c0381c13249450b0f101400d0b40701425400000600a90b45412031000e0703680c4400755000f0300d001c070204010400c0303098000c001070044a084007144119641c2441040c1c054249ca220f00c4607081e8131090f03000024a0115400c4441724070b0b081c600b9084205048110184903401840d034002c41c0c1e10003028440e4501c10346d0b2400258441c980131340c2c00b20084e8807000400341251034010700f0391502140c200700981405074030080b07818a080014658401d880b9100907a400c40f9002a25150600ca102003490040e03503e00c44103071044c000c542c035410004040002d50150036034103014800f0981381e42c01c2104038441600d021001c02c51000d001c018401c4d058100681c464015041048120f0a42e00030907a1958202c4034014a85200c42c011300007580c205901101804003d482004010200e00225280748034442002c0c0c14005002d500300200103980c0d1230711817a1980907096070f840b5032000107090610703009000e045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 681672176 1250 681670926 681670933
    0x1020705150103120518220b041b030c0c0807060c020d0e010e101101090804060f020a021e120f0307170a021005090c120303070314010f0308030a0612050d02 69
    0x140c03001d00680e075414103981d000b103070100d1504004c00b42902c42e580100c0124440c0c192804024030540d5a1030728407510700503000b4100307c03440c0307002ca12a8100c07030180c44804d1299141000e00210380381507601c1a515032096040c0014014a401c1068861001c40f0700005e0010708005040d0b020803525411004100e40300e5001c8030007c94402c071090f914442400b00544c00180d501c2400d61442c6407e01812007020684d00744507032000c41c0c50f2002802d4400d0090240c0711203100080412a10ba4480700179400c0240304e10182c10301c02580d5000442092440b8080c0a60042074000c011b40da990b041c910f40113068111040b155002c403e4805035489400c01042584e20f403001e00c20b04554030f0a000101c1d80e100803e0f0b800303803002d00d503800c11060080001070044200c900ca01c0040341c00c20b4499075080c004c080b030b00c0b40c02035490b0300d840c81005003690600203500400d50030140042140d031000d601c000b07081e42e5200042c2600c0740c1e40d006d0500300070b0403650700000c207000e601c1b2145805c0c05070118010f01e14001540c00d6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 681673426 1250 681672176 681672193
    0x6091c0207031713050d03030e100b03101109060d0605010915020c010c060b030f06040c0b0903030a08040501140103230705101b06050c220b1603090506030901020705 73
    0x40e078440029110150544074007860710007a803800c0304001c180075141c10b555041c0c0d15440e42c01080d40d007080010118042a611014441138540c20844410441d220b06014021010b00740cbc0031a0b00c5401a000c402615a101c4a16002c110005000e8524204000d03010a449404013607545010305200d118160102e80c0341080442c861481203108403100d05a40c000300601c450210044494400780c03d07058410036619078188206a80074040c150a0074019001005141043d0818003482030300b88d40300a8414404200705203440d02e0200c140c6240c110340e41070083e419560340c10186d0150080c1c2c015280c803000700c280040100400e01c41d4001180c2c0340420b5491000e681000110340d41d51650007a96402055040701b0f1192920030f410359030702d100e4a80e51442008500d40d9860060380c006a401c102c40039404580000b41c142640d0603c11485521000c0340940d51506004102d584650340820040b507214481010500d800f546034000248030203807009980f171800341d900324000d4000020072074060280d00d04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 681674676 1250 681673426 681673483
    0x1e0c0e0a090f030804031e090503100204060207210c09020304051b031207022202030115050a050a03051f06082202061b0f2b03090c050f0604080609 65
    0x10340d0881d103900070401181d0240c151001d03540800c004008a0404c90515503101e9a0040965101d00d14043d6850703450840703040004141c10208a1068104004c0c030610040285a50001d072034021103a080c0c2a0444462824540070700810550401070303c6014294400604411107500540c4543e008409548100d40948e061112501e48620003603415407040304901c645900c400020400310740f0041c000002d42842c40100c08070b0700d50400d000301c00341340d0101c010802214660480e00c003201e03203803908500d000c6010201070564020120b00c08101541e0308005090422401d88040310300101542e6606090380d60180101100012604040b0f5503114a10740a00e60000c1d00c13071040d5640c0d00600b09800c00d000c0c0e41016412060110070039100d4482c7c00c0c540c6090b02e07001c1c080c111301c2010781905040010000d03d115510505000c1030241014940000c04020440304103901d4242c4804407079400a5601100c0080c0b514007c40d0000c3c4401e010354003e014142800083c240c00c221070800c1c0007415504100c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 681675926 1250 681674676 681674681
    0x7230a18170d08070201020c060f070f050403051b0d02040f061418131109072d0203031303030f1d0c09060d0f02150c030d0e0705030a0b041e0c0e0a 65
    0x8290500903440821401c2d07400d4001e5800300d5100c00c46200060400c040074a600d450148240d442c3c140c251545400d00211036800791001c201e2140ca070400a20b41461651104d54032540b080c0030341c07040328035000d81001a940d8548503000c01c81d0000e100b030107103080081c4440d0092010b441003404e03038410b4247e010301500344866030b5040c290b800940d0f500302da6944401d01403520200c0d1821184450081d11380320290760b03452000f038003070025540c9035043c19400154004180c00045a030341b40c03491401c02003100841d800001c0700d603c49003142d41030b03100c1c0038146816009030401140241c111424071807803d61600c001c070442260b021401084800c400c0c0350005005c08000181e07800307500442100360500c00304007118261000d161015002401440031502071030340c1a089901c0304031140d0000100071921901900418489440100143c085180341000099a5607148280144030714240d03000241804480041550300980640340000104018030f0146562101401102ca0010a03240032541c4d40a061 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 681677176 1250 681675926 681675959
    0x6090b060907140f0702060d0501080304090c0813020d050f030c010b1f0c02240a3f0f06090e03090a09090209040f02030a021302040512060f07230a18 66
    0x15043d440c07038822000c16403919035000300002c1c0e0700300703100308640e03901403010b4030420b4003c042001c091500c45051912450a40e0035844400c010860034105009000704c0e01081089103076812079000c0601641403404508003c2a80c0540d5a5800041a0b44014030300c1034000b09000d0408a4219031865004604422000030740e00400e00042d48001001c401030404420100034154900da484035581081c050341c00303195009102c0000025020034000039103040312031020079000b86514418840a20604034031641c52134102031030488c01d44400f942014990945d1202024204444c13003881303420100c034003444e541c1d840681c0b90f5024004001d0000f401811906c610702c051a0700400ca0207080d12103032500c950705045001c0070399040c09407a42000060351412100281884100000340c1c50714900710800114884103507440030b840d00180100300031104982c46565020803103080c421100e022800d80c0c0742c00300e200220580101100050200500744c0c00c06489600c0c401d15415408200340c55a0841e0700c0303490740 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 681678426 1250 681677176 681677207
    0x180904140f0601080d0c050322030201140306010c02010302090a0f1401260c0901260a0c0905090402091e010e0a050601050913050c16061e053106090b060907 69
    0x2170303540489618032034900d00c3c0c0c0f054005c50840342002c0c138036803061a4040f10103c0300a00000c0c10751040045580041c055401c518000d40690308501d80354002814415100000034101640090058416959481604003500d8000309440645444d603808003c2d44044000107030109036000c08030b8010030703080b44c43c1031620001c01e28401c00c00d440340d0700e142e0040d4001001c20b0341032110b840c01d0112f01000100c8a50229900d1055003007190038000d80c001708a40360f130f401c0d0404105640310300340a80d80320602d0590b0041d034191520b8020f03a540c44c1110491404400600d00c3c5169100b00004403080711048160041150380d10800550b210030006441070f11030442c001e50494591544204600b001c0c0d40030300c0c0e0015159a00c0c501d0b040207210b44400c90200560102e1f00b160307803119801102c0d04204034000c40b03515503000820140c1000c0c3e41d0041c44d402c190f20444201800c01003609440a404040d6080c810350000d420b010801c1e5074070f0f04d059003280846195006024641c0000c2080c0d10482d20030003c01d10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 681679676 1250 681678426 681678433
    0xf1a130e1b0415052202210a0c08070507021302070b0c0703090806100303030c0e130204060e0f09010b030a1107030804020f031204090218131401060305100b180904140f060108 77
    0x10030340110f03c0d001524039403407050603424050351880c030012a948280ca00b441f24108041460040c0d4010200c4030901601c00401588000300324215070402c088485042c0c04461418a05060007103c0001c3c0c49890401010302e2022400e11151040300d001410b1290310945030450001d031200c40c81a500c3c60120742280c62a20001010001700c0d0095105040c42d040c2da01d0506604108100400c0d52603c0300d01c4000c9140381c0c0007900304000c0354450901c2d4041c8004850350002840301100003201c9940c10b020360001d443c0008003040390003115500181400300c0705c1c0003081d1601c8603402c0c082e183e10001c4806a0042c003081c5210001c41ca004955074000e608082540f0b030410341818060402908510701c045040301002844c110789980b0100300701010b02c00300002040070076941e41403669010040c1d01c00d4041c14207000c00c0c080074030801505c074410f030360072180d0702a12044201c80350b2011884008415400200c6032040c002882440c0180c0042c0ca00c01c0412520340c401c60f25007190b036600007481902d000c0d41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 681680926 1250 681679676 681679699
    0x30c03021807051219141b03010f15020a050a0b0f0a020705060f1308031305010c0f05071104020d05040b06040b010c11280609090f1a130e1b041505 65
    0x403031414080c0d080f845074071000c4140d02e94102c03950200c8110040e0340019940c4d0381c01f0001d0341c224074180440079540c0c100c041070455142a02c8142203000c107006420030092540e45400c4118800c1003440102d60b00071048580e06030342401d0440e4400c2c420b42d4030340146c0b002003000980d082ca15000301c8010b154014000d04d415a0782d00042c009116000d08182c4010f03a480d10b565004c01c000d000a903008030421004682400c80b240385c40e41c00c4a46154401c2d050104051184c99016004410340311070070b400200600544003201c00040080c854000c0c3e146400d031909050105026811071024800c1d01d065808015140c0c001005665a0501803401020391a4000d029189801c10103190900001300000003450b00000c4400203241005a40140c000180d1140307042100c0c1c0c5030343c06800c0082004041c10420741c50064000304480004200041c010010a111a201c403056a40082041001d4a082c1c401414002910340040f03100125824460f0f4186001510b5200000e0151012180020060501d0b82e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 681682176 1250 681680926 681680947
    0xb09011502120a210c1b02041b110705011701060f170c0a08011e0512030706110a09060c03050307050c0a02030708010b0411030f010e1902280903030e04110c07030c0302180705 77
    0x280e080400413a0009e840c0c11a84010303842005004120300741a84540c0c001d6a003540c14079281c40e1707465002c541000140400010a501c0315507085054030800d14120600248140c42501c5032101d0407030301c20040a4040800030307001e03004e8015145d05010350740e6100469130703184d0818104151412220155555400e01004180343ca1541c0c0960710246805590401c0350b5915401d0840700340e414040300002d0001780c280310b120b0303000f507007800030340b03032a09040c450f2402546008040c1c2c0401044001484000140c1000000d001c21096075841e50003821545626120342c4014042e001c5880c01c14000c5040c0258504000c50500c20340b4400c5c43e441c2032040d402e85c64040241c00e084030143c404080d082c00a501c441c249050350008060324106028400b03003000c10304510bd020300e400b02e150302c0208050345800b400000d500400b1b00c0b549010490300800c0350f41c0c2a100d43c40701c0344030f644908429071042c007200004000c45c0821800c1180c1c02250005000307106044d00108205003121058001401040811800c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 681683426 1250 681682176 681682217
    0x2f090310050f0117061306090f14030d0f0902100c0f17030105091f0e18010f0c020d090f0603020d060b0a0e0906040b09011502120a210c 60
    0x1114402411200100124800030302140c200341d40c00ca0008144000610114000c00746003c11401010002c00203803a10303990102401c17640b10401862a921101d0307640034048001d03400091281c1090700c80c0c1c040342c40a4441e40c1c0c1d80d030100000d01250f07170074610489003d070a10701c20040c201d0f401501d86140c003c0f00d00000c9030500d085490403500d10076400044e0002c50020400c0d000034010400d0860f541c0c1d410101003000c181d8001748111031b400c41405003a001500315001000841e161802a60402d46600314075001d04011000c50306415882c0242d5030000c800c9076017000100d0245502035541e211802c503412103601009003c1e2070319801c0480c400b0810144646c1c0208440f2403c0c24001a0f85070703d17060308209030740c0280b480c80e00142404542c1e51140c544a21190b40003c811941000864400c2c2d000c40c140107014480e4000070342c544540f03440114002c0c402c012444940d03c10095840c401c682014084854044407000301c04000040d041c403840007807123403c45c07010076901d42801d40d01c41c182c0203d05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 681684676 1250 681683426 681683437
    0x703020d021005040e07020c090a33080118060b0109030302150601020307061a04062408060d080a080f1b0405040218130c2c060703021615032f 63
    0x10000104000101045d0358070300c0324001e0682d031780079200351a200810041c00c4180940141c00301846c00d81d40c00d05a480c03101c0d0206038050500e20a10310118010413402e510819540300c1d00703507942000c011000c90307030803900b4400c2402d2003264200319115885004562050080c00000c016030301401040701c1241c4a5002ca5521201c148126132400e4620341e2200196003801c649154414000e4400940d24a000d002da240546052074103882420408644490380c04c2c511582d0106000609010905a407608400c698220350010603241c0c2c0e0750318040005101040407a0200c5141c0d25440200300f851a082030300c103c00501d60082c25080900b07000401009600005481d1685070399102202081d1b1243d40740d2080142d42400b0005000450702c0010b44a91310b2803040c1c1c000c0f60803000c91400340c107002d01c843c40c501301800e50b241612030103a89000c1e45041000c80407282c202000440c005105070018022000c11300c3c4556080c081c501d03035142088040c003080121881c0d08100d51140d80320328041c050103085d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 681685926 1250 681684676 681684709
    0xd020904060b03120703120903020c01050906040e0c040f15022a04090605100b0f071e080d1a030d02120310180218090c03062403070c140703020d02 65
    0xa00d41402e580000e15102138003009545141c40854400700341a00a80140c614100300035060241c84042c0c1c1c0c00035200d41601c0300381418484042072840d0282c50f07000640b0080c00e003d40002c080c50600101a140e42d030494850707141050303005180401c440d0591075560707032a510141c00500b4408082000d02042e410441c40303503040342c500081d003044a66a5401445407080c00b4590008540c1800c0001580050b6540c0007540420701c01c10007040a845414110f80c0115048080b07105a420141c10200a51100c94005400a0000710350a64039045607403110000801001d2110140c046010a0640b01c500c8000e40c6805038210740342c80b41036008044021a403180d0109400c03109075031a5400301800214010301000d015502084140c1d41e180501c500d511409400c4070307207420520300405007440511004200c0d90040f68072034026800e4200352101405a80d8030b1645158883c6031248005110b481c3d4540141c44140b101c42900d07184660100c0c0101c1a690060210039801606400388409240c014291a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 681687176 1250 681685926 681685931
    0xf030a052a0109110a0f06020616090b0f030a060f24140c0114060105032202040b060307030506150313110616050708060c041206150509010f1a090d02090406 69
    0x1448810000e1080f080720301c0c4a03400748010201c84405214a505041e00510f42d0b40040301014001d032a00001c1b060f920003000f00b0031824044c403402c801c503000900e60b8000720301d00c07801058103031302c400102003d9032003448540805c10809a46807410f00644140703205040c50308440203094106000c0c41041c4480004060402c140c4580c000100c41c805640b00b0f14445105940d07500289015004005505030491400d00e000d60940c10070081180c030b084036000c038030760b54000e041640d0790840d00c2e0360304020044427000300311035124070b4082d00180c043d1004481040c800c03915078441031003c0815809580c000d4101c6000d00c0f9551596030703141d480010007006259404082840280308800d001d106c20a039282c0f04030050a00c2c01d01e00104180b41c16405841040c5a4009002c2030149204042c21610156044680450002a0950082c61400c600d402c6181c020000740b001080b4580400c94210455909801101c0d1420002090980d94090490881e0744030b48400c2c22034016191005250790060302a4000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 681688426 1250 681687176 681687247
    0x21c05010b0901140102011b0f0f0207030c0f150f09120c030501020705070e0a091a0c0d0c200114040b062e0e030a020f100e030f030405030f030a05 65
    0x7981d03100c1c2603109803900300c211500130b2030701d50f03080c0078807050710b88541a502c0f014070701c01c24054200440d4100348030400545800340414a8400c00c2088000d5401c00c44000307002e600c1c0e1607210b04688041c01000386007040e00c0c028404081c070509400020170050390352528001c0c10b02c0303600440803403a00800c0d60401c1400d0381c0440811000e100902029100c0c134018240b003031800400c2c80240340010302c080785040c50000c404000c03903112890f10000c0310300722404050300d94a08405004601818010640707461400114882c0c06400400e58010841041000c480061071102c91901b80d82c50480490a040085808540003840000c44070350401e100810786116031185103416600305100c3c0001079011f08000d074410103920381001c0c440548030402e8000c1d09280c0001c1e00800c0306010300304441ca0254908411849030340b4480e28280c19a00340040c15a992810581115503a0380c0003401094824082c8241742e50040200104480d4402855115182058500f805421811039040e40034080c0c1d044c00c240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 681689676 1250 681688426 681688429
    0x603072105031204030923060a0507061a0909010c050d090507081002251e33060f180b040b130207060605040608100213030b04030c03031404021c05010b 67
    0x500f030041800480708419161a08004125400c00d6100c410743d89600c190818003100200340303100e07541100b0f540c00c2c0c0c0d0316004842c0c00c03190b9210705da40107010701e0702e80503402c01000b0301051481c03c008011180c128103501c1d0b240340705080303800b010003240c0403078010040300449141540050321258050000e80b540d86503640802410210440f0311100303620f0f80080c0508510034801e40f0f8110b031842c803040c1c20070107208995600e492150245a01011140a80d085030100050101e21102080c0000042e450f401008512010f2240c04000321518080c20004045040000c9024000031582180300b4100b00740a0500c045001f0041d00c1103a41d0442d4540140031030548400c0d0f8503044031b0000400040c0d4440303c1e41401403c0740c180740c1203144030f17070b09100040048280c0020444810300080a006a0350102d4040c4e0f610703022a07640c801041240094200000d154003c11464030032402901c091080c161501541100d01c1c1c0c007101d0082d80104111a5000002020040c40592034850710001074913008160 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 681690926 1250 681689676 681689683
    0x90206070b07110f01060e0f100b1b0111031612020c01020f19090e0c0c030909010902030405190b270604050708010e0a0206070b0408190309020a0602060603072105 72
    0x80b80100030400c2810f92030300c0301804126105240c0b414100070042c180c1003012808419101500360303800500c010000c20360190401d4040001070810444e0155120100301e02c070502c0c15920071203503a555180510f64003c0403401030450384200325080e000c2c9070403d8810b04c1540c0101500c1c52400340707640e0034001d0303190b1141d00b44010310b1020240088280c9a06500a0307405102c00800201010800c5000080014560003025183c000e6450700c2919100c07100030882d1451070040c1c00d402031344520b10300000a0440c0d1142d0085001d18011800e5445104c1180030540710440b13518030007003c8208001c00994010344501103d080d900c0082c911031070115141000320300d800016078040e1030380d402c807513820410210240302c1c500704121030f5405010f020f01c091f000285079004084c0701a003003c41050001d0100003e1400300d5011082c80000f1080043c00b9010080091500000c2280107004440c0003003403942c0009005485450003e0007002c40d81e040403100035001c0c011080c1540d50062411b0000000360052 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 681692176 1250 681690926 681690931
    0x8090d0311120a09020906030f120c030d02030103060b0f030708070e1008010905062505030c0912060c0717032205160b2110060c02220516140706090206070b 69
    0x480c3c007080c2c9013102e0040140350ba0001c0d01d258400e038406880e51a088101280c080f41241c0c04151082c0c032001e44104490661040c0b41100b0070700e6100000100c204115680843e10308031042d190491544001000d16580711080c0c05411310560115100700a81800640b5080d4841d00600000c2055941d410409007500c410060458203030f04503404200c10500d0399040f040115071000c44441e00105021005440da200113010071010300c1c0c000980c101c4540310504030f41000b5140908681d0380e490035104010842c2c000420856207561040440d0784418898003c0da4007603071215042000c4078980420b0702000030302000044685015001c214034031110b13142002802400140d023140d80c0c4031b074138800180c58600c00700b100d60030488014042c0000309075081059010f48011741440303000c402c103a000060a02d8507035a000303404180e920780c00340040c0341541c1110703000300003071102c00e8900c0c000302c4400d035410001c114000c2c1c03100c41f05019001c0802c0480d080b80424500280c03203103103428440e45880d00b4801c0c4c04c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 681693426 1250 681692176 681692191
    0x503071505120a0209010210150e040524070f17010e0907081b09010e0403090e0c091003060311031b060706110c2410090c032c010c08090d031112 64
    0x5c43d4034007080d60184900c0030900b602d80d10401080100f070225051207400d0340160701c002c218080026041100030490b0440d5803100703280c81c1101e003442808807001e0030011550040091035400554a0903802040030503c115028040c00d4043d17800d100714500800e10090081446d4032070301000041401c030034400c41302d1134407150200c040c0350b8460700c1c14030101c040e0691091030b20746040310401c000300b5804040b05064032700c1c018210409449000b0090f079076010341011517900081410381900402d404d0b07480b00080f80c0c400c01c0182c4114105400b016101c0845203904060016100e00440903481c06000821010740310390030002d042c0303602e5596140b42d604804603000c807075400340b01414145c07100c5991000c100d86040300510010320300b441216000300c1103441038094142c0c4908501540c54001d4012440d1399404644102c4407424480d40c040ac60001104154415407078540c42d6402d50b4841e5005900c59a48140208007244074480101c00505c11144241440c2200384003055405040c1c00301d1134001c0d181c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 681694676 1250 681693426 681693431
    0x12010b09210d1106090a02040c0909060b040603140613020c15100905010b0c1c2601030308160203270604082b020d1112130f0504060503071505120a 65
    0xd00c0000501102c5803c1000700071070f0300c03e00c100004002e0002e0003801040d13054030042031074903090a065454120b903801600d05103092520200d9071918503c0070380121915070303805204141c020314550208503170a554043d0080032000e20840c441c41146c0003060440410000c031154042c18019003090f00710b087c0c649094098804004009103401402480e026200d1084168980f075000021944e41e80703006180030400d02e600001401c411030080441b0389844404025020000000448804105000b4003003200441c503424042070b840c00040c040070f0103441154000310700c0e0102003c5d03040507c114400c1c02503000003041d003e1050320703103994001d000286001c00c0241059840e0300060b00600e03030146690b42c842d00204412180c5e040d030000f501907442c003440c200740106441030001541048500c84011035071940c0050080003000f080300c2440102d94281c01c43d0200a0345400401065500c0e9204240d4164404482440f1043c0622180c008040d0f080c1011443d00da04050325600400742140e1140d500c0f607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 681695926 1250 681694676 681694693
    0xf0c041a2214060a06050c101e09050606031509030a030f06120309030308070f0e0907090e0c0408070510090b1b100923190203010906150503100212010b0921 69
    0x145901e007400500f001703081c01c90415171f1007520507a88100b0412008105600c50303000d00c0680c031900450500b0b041e500c0200f030280003031a007070450f41d40e00b007903908600030710400c02030310701003142000c0300c1c1c0c003601540c000303140780c4a201c0c2402c40141c005103207600c01040d91003000095941200208181080c800c1d20b502540301d00e5804c4c003610781ca200070004028032401d003e90f01806070b8000094a01c1070000c03200300410340c4900c4402c5501c050b494000d000460744120900061140300005482144c620f101243d00031a03d520a00140708d0305100d07e94040b45100c5400c2c82004003400107090f0400039400f9900c01400480304251030101d00038042036101e030340d44019805108415036504807000200d081c42d254206011301e6a640d821035810050030f0b0042d58049242159020740182401d07a03002681407205c560700c545400c0c006009441141c2c440e11401d170700303107d50003024001d60b010301380200390301807880e803038210750444a500c05110f89501646a032680ca070001c038030070000780712802400010500340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 681697176 1250 681695926 681695929
    0x1030e0c091f08030903060a0207050a0606090608100204150c03020a0b01030b100602011509020a03020708040b09030d0809030d0b060c01020a02100509150610031104080f0c041a221406 81
    0x2e042e500403240e40d4000b0030a28111380c03000549607420150401300165a5012424000d007087e089031001005541080c0b00010a403101d03030007213410f5800c5c000955a03a4525070451804901c40da229000007814070307903e0812254095082c44220320b0181c01950001d00381d0b0b84e0f58202406090304102c65100d842000c0c06011015910704001803c101e0000b04007002480004048821a902c0f51640454000405400c954425016100301e50303480b01c002500e540e25118400965001400f03c58040d200e6942c0c90058507100301ca0b098040c407200c001440c60701240001d503030f016040c6191400e4101070200404900a0000d00c0209030001d510ba003e0840302f43c25040000a840000e09440300ca50710802c0c0e018a400c40703001649030001e0f4215800c3c82c0c0030841d0385003a80070340715020000d01070050110300022034200c04034203010006604030540794502141000c000441d1040c029040707540b200c11403900c880b8104414000850300085c42c03504907510710300d04941d06030b4101554800d5000444014040503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 681698426 1250 681697176 681697231
    0x301030b0a0c09081507140c0f12120135210f120a200406020601060801030f0305030717090a0b090304080d12061517150f01030e0c09 59
    0x520b40c1c500d01a0f03029440d1618641d940e00d031040411014a101d030700892501c41c0151946a0703c2000d606189499901b001d104540360804e80e0310040441c0120640030224500e032400302c0e0001001d024213510543d00b0f02e44181c800500c1d48594079954041c240d200901ca0028030f009401441110000b03090004c00d000c120703141c4400c10040202496002c2c0160b900c50401c3c04165551030080c40e901c1400c960380c0070680c0d00500803410b03201c0c0a2082c140c668001c00c3c603d820083c416103406801f200d0191342e039894100d860703800911000e00750020303220042d000a8491001140c005019243c2003048000f100c004840e451790076140e00c2a44c0d400004c65504020500740c0544d80810000081c60a103807034480500c0d04c40d130080386400200100b8240500c5d82420542c012402790800400e21a08074000700005860107803c1a517858000381c004000501c155505101800300c03420160801e42d501182800560240286440c10142c0c0e0180070b21041450b01c07400d14040c4104000c4500000e4402e003900d43d83d01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 681699676 1250 681698426 681698441
    0x60f0105040b0a030305190903080a03060f0b0403080f0702031e014a1905010b0109051f140f27030a110f1f020f070f080a08070501110301030b0a 64
    0x150800120130030119400c80d083da40c0e504401c0402c1c103c7d1003851310080b62103100a40004160090118642c4041c5034160312140176184a9000381e051a522094024198092031200503c041d0b4204402c441c04110780b00a848203a1010741100d04010180745c000d2040c0948c84015160303a9900d0756072584201225840a440c04520801c0950a00a411200031130750201602c80c13540c100303000f540344800780080020840ca00c42d00c0250486126041c40d010307002c2c0441609a0740020750440010441745030103071084004015441c0c8a07140042e20075000d44031480d0010710a83c000d6401d00010010040c11001020703c0d81014240c0da8031009110f10b4070360f070035409198540c065844140460000340d407400414585640c1112045002207030000002e2861030302c05450445000c0e005043c04005800291940320096078205031026280c80d11b18083d0300089501c240e00481e4400200c5c1c4010a01910040a4550103400045134003034010400000350740c001c0e48101e4006403100104003040c00f25205010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 681700926 1250 681699676 681699679
    0x60801021c15060e0d170d090b18030703120b06280e030a11042304020307090e0c370905250807030b040e0304030506010f0503120f0c060f0105040b 65
    0x121a04002008080d80c03881440744c2e0103007568110510030301013207a40030412820100780711580e503c02040c64034090401c5110803502d01030a0004201140c2020000c20800c010310390045080c0750240e02c0880380c119941c280c3e00b0301b55541c0c80c02c408da26221200104071100c2c41c0682803100084c02031002c800d905046415104004041c4e404800c541d03400b042c02e00e1202d421003480d600001e11840001d004141a4008082c0c09020b204400200045904941e200394000c41c1940c200340c2d5902000c8081c1c1e40307a80c1041045401002803018070340b515900010403202e50b20b803071142214149101c002400c024041d04982d100705014108040341a9000da107511501c4550060150400d04001011061140812009109507100010b22082c440da03c0342000c50f030010030030b000c5126424281c3c1d490398424003080c0c40c18016100003040000304000f035202180c42c064010031030a650450001590342040c9815140002d04001030030100303004101c6c1c1800b601c1400d094401079490102008202e510008229 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 681702176 1250 681700926 681700961
    0xc100501060f051e1207020609062509180506120714060d0f06030c08100204050f060309030c0d1d090f06060903030c060a0207110117010303050d060801021c 69
    0x14031060b580400d9030910a51141441e50b183e064104520f8100141d49561524046000c0b50346a03214100161450080300103030280d802c2c039150a081c00344c40e5081103e0100311224028660078000e41181e65903142805a868098101600c41030702005582c1178410583d4001d4440f41800f0192070b00b106040e0100d402c0c14002c00e84a454441d490044030210351441d4403802010a613201202c42e02e130070400104407140c20810206860b883e0404616995010303001700d610543c0003440c1400c3c01c920840302074540007450380c40745d039030720904000e1941d2005106144a00003803040202440d410040d591000e1403035200d038840201180d031007020741c00c072142c80544105040c00c103210580e81c0c180402d03600208140c2e04907984035150400710b45540320700700900f0140c1c072804041004d0b14003aa406803045901c0b51035460145a524401101d09441c11402c84a600100100400008e80624002c14002d01103a00101e00950743d07003001400c980208180340d03c48411441e86012019a07403080421181c410b4202 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 681703426 1250 681702176 681702179
    0xa0204150f080703020a050702030f06240d020f0103110703020d121413031b0b010e061210020c01090609050c0a090e1b0a030c030f151e05070908030406050c100501 72
    0x1000820050501e1044c1640043c9004600703102c0c0085038200c58020301120500440e00304c0043c0d03200000c882803a91141c4845941c005900080b026501c000001060100f00e20440d808009140c4082c07510b00d814959a40c04d0116003809807006400118029005008103844902015100002a440d1400703032602d000c1c5110003400121059980101401280030054080c40c681030315012b4110040c4003161842400482c20840440071040c1602d001c003d420399252150700501050860707419070308106030030442142443d2486a8090400119810008142c0b0095916003204582031000c0645085d00b100300c0705102070821814880091000d14400c2010758101038001d034a034001000389218160384010b5445207662007100c5c08000c0e6401801b1522215520704d4824840040403a04403482c40420303025484140722440340c1a40310303801c1030b4440c841d101d016881c0401060b0060041d014820101400f00d640d030b030304001a1018081c0f82d00c0399941d6040165120780707800c0e04140b204002500b400b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 681704676 1250 681703426 681703457
    0x8070c0c12050c150d0f090b011e0302100504030203011404020f010c08221d090303010b090301020705060403030e010b150f130915060e270613050a020415 68
    0x65801c592111501800302040c519020342008803462001d40e02440703490042004542000040004082d0030744100001c21440040d00292210042c000c0c3c2000d200800402100a0302040751404c440440e003024085922507000400c40c0c0c04e01d4075182c000440200c0d00b80304604091140c3c020490701ea801d005160702e410b500003020580c030340c2c25950400c1307441c007101d204021003042540d00c0c08070a0f0b944408000042070303040301c01a801c2d00c144070b04960032500e0300c4007150f03181104c40d00a00d074030005180340d0380c20980fa0104543c4914909138040d0f40c00c008160114200b0710034540a00e203c1d9402080c03810801f03402a0030f40d0850000c403823051014070b800501d00d098007000c69002c2101d03000039644850f00c0c0000d080303060000d81c4c00352071501c1c280303900340c580710b60740b4007404c0c080d240035449143d01492074600703018042d902c1c20201640009076900045500e02100c0107580d2201005003181400c10800d6020f0b0107860066901c8651550081014043c41300c41c040407098501076460500c0d146044101d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 681705926 1250 681704676 681704693
    0x50f0106030e0a110f0409060e120307120b0a090e01060512011104151704050d17011809060b0a030b041a161107050604030f05060705090102100506210a0308070c 71
    0x20014030b02022001318000d103445851030603180c040d00400802c0100381c903003081800382ca410410000a4020310302054003002c408000d6034018415603980210f81101c0050200c0104034140c1c081303034044190355000800c401c4500030180d9a0000c4000071454030302c1e1270140a0407d10711031040d00300e64104100c214101e0302d80400d45d411a11003e90039032000c4441c0c1c030300f80c40120180007415659440c3c9030400050080000e100c3c1502440366070f507a07001c0004403424491219080c0038940e125910760300343c1070100f4600d401100c5018082c4030001012001100011000d039000d500403a40c1000080802080c0000383d40a8138122008510110306443d1040da400f02820030304181800b800441d00001c10103007010003121000e050082d18065070b070740e00c0782006c111000c8407200c103c41501c41c1c0800100c00b50310410680f111142c041e0010704d20103180148007405000c000b004590400c00409140222440d40704082601c4440070002d410014214100104900d000515800500042c810a0b600103240c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 681707176 1250 681705926 681705943
    0x302041202010c110303070b16050304020f010c0510050114130902010926010c0314060307030b01091e1d12040f300506010f08120f09120d03050f0106030e 68
    0x2403030f11014010480c90404140c2c40300310401074040c403010030454100442070000600941d00111070f010207000c0d603a82201c2c584400c41b00250016100304030218154050081c003043c0c1d40c4550251000040c05881000845100b64461668501032114458082c2066000694070380158907040c0000e450a40000e000401580319a0340c8a141c43d4002c140048038000d410009012690001d02c01118803400003009400700341070303407500800c1800100d0320314980000c01c5000c036a40040104c1a6078030b010111002000c00700c01c4040a03101a0002c030550211602c1007900d44001c049003503090012004610780780c03401c100c98103e0008820041440035070b00b803242c0c0c1030031030b040100581e600500c0c1c1a1030361062348291249480c48008e0007144010040301194050503a0080300502250076914070429a482008070014000c0020400102d0b1400150100900074117802501ca0350300010920758151400d00800d42d8079000990701c406010304030300d0a56425004014500d0140a0044e00000c51030700d9441a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 681708426 1250 681707176 681707179
    0x7230d090504111905041707090b0d0506041b0306050f0405120f0301050d080403231218100908030301080d02060a0b10030c0e0a0806010e07080903040303180e07120c0302041202 78
    0x1001200580135100d081250040c12005000d00e8646100c80303c225034030825070180c86c03080c0742032900c188101d050124800408a401000500e20794031280c0b501e105403a0040074200701109402c82c0072001c2985801650302a01c28464900c0c1945024100a81040d120316050710312400f08000e244480660b00c02542d040d02c00886100d036003170600e813410b07110910840d4001443d45c00000b80c0c8440c084540d8400307101011441c826a00f11401da0713210580d580c071842d441c0b113149c2560124040e00600345406244130404450400c001d9080e1901802455508241d020b000035a00ca214440d1440b9810301c0400d07007000010400f40070480c5088000b0310315003950217100d803c150707640d01e10200951003859001003c1901030049103919450390315003500c0b03000034080c04907103416030300c08112042d20883c42540301e181c10314050740c141421503a0444080c00340d95142145030b40001c00c04a020408242c05a000b8402034495007035079015014a80217868440d03550714185072060101300402071030703541900081e650 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 681709676 1250 681708426 681708457
    0xc150e19050d0b060d0b0109020307090f18180204090b1f050d0201030911041a24030f040f060203181b031c0c0503040e1b0f0d0207230d09050411 64
    0x81389000300e4409014000701500500403032000040c2c0d051650300960044d00b00783d03244000151501341e0015007504512400c20750b0300e00740d008414000d42d180d211461410b4162001c884c0c1000300c2c0c0000e01500c130090016600c2000c802c050107003024801d885c0310440380100741c02c501c0d041d10303090010b43d4519102d200a4149501c403442501040003040a980804030014010400c82900c040858000c0e104215400d0140540300c0342c13600025103052014100c0070141d4101c6203140d60701803400001d400054012648602c7d0700388a4030010780f50b400910311440b04241c64090f205000341c1d60383d141900c0c801d81442100f00c205044511500c0c0415040c520030460345403003101c040c000c401150401c0500e5400b910340d000115010a80461402c600b6006076841a1a404460b0004031340140310f01c20380d8043c290a840401c143c100f8180b20303402501255018030246145981c2d036076030440030b42011040740011504100d030200150b81d0030100c80d40140c6400c2d502004400070191030b03c6040d2060f040e81035101c24 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 681710926 1250 681709676 681709681
    0x20705060d05071706090a0c021914251509080a06020d321b120702010509030307091202010e0616020a172512030302030a0b010518010c0c150e19050d0b 67
    0x107002b08103010200425100c03140c1c5104039400c006621028008842c181348c058402210388101900c44403829107140504110305207403401c662011021200500310060002c1d4420004840c0014032294200300c0c0920009640da05080340c40004541c07800a02d1029003a0a82a440c0703039080f010724490b8805c408000784505030b2540c0d64902c1101c1c1c242001300d62403500000380c14031444070505100303010700c04540080c060307620351081e41a124082201c1c0900000e031800c81c00c020302d00030f40c1605002140103041c900000d912060206500303601a0441c00102c00350002400110b04080e40500000d11403c9140300b0313000d1604805076204d1800b11078180510507100c00018a140f83d0307490f120700402c0c130420103100300c2200d4600a8040d400c1100c1501400d4039041c03000907194040c0702166482140e0391071807412400301000646181e180540182c840c201040d5010070942c0d410a440c4506480d0b549030000c10203212130810181c1c403800060703803551024440c1304206a480d648450f02c06150300403140300899 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 681712176 1250 681710926 681710951
    0x1b03050d0509010f02040303210c170403031e1406040203150f031c0f0e01080403080a0c0e21061005030d080c0c06131101090b0d0b01020705060d05071706090a 70
    0x42c8241c41301c2c4000c81d44009000800c043d0440c6c181b1341d4110b00301c01580f80034040c001c0b01d241150b8074021900082170194404518074407444c0e050350760091290400044100130030801c88401c20300081d55452407660303a43d02044880b040301c0e95aa00c0034044800358613501c3c001c03007061044441c44d02c14a0007403100c030341c40105075070707040c480d61010307116643d0103000f00c41016000800d9610301e52500c1c0d010038400a2141c0181d40f040010a22540c1c00d5190307240c182d140c40c2411001016010001c5d01007000740c080b90b10b103d5441c410f000c0384000315550f0701800d00030442880d6081c114050300405c01c40c03d400c0d00c10811514049500d25444141e4100920b1641d10450030b06128851400003180f1802039404000e40c01807010315140007180101c2c5903c145000074001960400480d0066091282042c00480030006d003580040031040c0c01072050301c136180e955501098003508403c242002c4180c5074000c1080159004400074809000111840d03000c2c103090b400300c1c040c0e400103091488c0090722a03c184500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 681713426 1250 681712176 681712181
    0x91605040f0917070c060306030305091c050d050301060e0409021509032509050f060108010302100c08030a1d030a091206060510020a030206061915030e0f0703031b03050d050901 78
    0x11600080000c500209100031481d075031303101501c00c4448010449011810520034030926003500e074036840705890701144000b04161101400815103140344a4641079002070300510a4401038401a11a280c580d410901c01030031991075003001c1400340349002411800b594a20300240c03150042c0890b2240d4680c03070200403e080c981807402c07610070000450140b1101c0c4070301114400440d00b03c54800c03c010313164900f40951041e01aa070341800204100014030140c5405882114000c1d4941801440640a40ea414000c0c0d001201e0300c5120640d2414240c0444010f01c40200707040d208040a50f1038121404006030001c0c406020312140701403042820020042180d000030b000d0f00d070040c90b000c000c01a0040003580c410300d150088005000c3e040102c0e220741845040c200c46039554000d480703900c0e410140c9050700945903000c1c1038105512204103010300201844007a013401130030030280070b5042c11810040e00710171411803c01894180c603003454000c00e50020a440c151007118a000c12141c5904000e038bc01b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 681714676 1250 681713426 681713441
    0x1504050316120f03090317090304180209030d0905060703030506061c0b030114101206180b07140a120c03060b040605120c030403020c15160b010905091605040f 70
    0x80d403201080d903800034003200c65111030151402c0e03036520410214004041341900c84140c070003400728201680c8806031800a201843e8084855400ca03400c0c195070356012007611010f60b90140019a00045440d510b0500b0302c042d030b80503012030405008491400c40400d032148034060000c0d00b055541c2000c600c070340e5a054129195030500c0d6505482111500781d6a000806c00d12829a01c07a628001c0d092013030380201400144900c100a0101d803040d071408568814980c222101100c50540d034041d402c0010030b1070400e0a070118020744141407149490a40074000d942051000000b82c0b409001c44100a64170503195950080d2000380815004002001175015203031b181c01245602c0b0000c507001c908070f684000a0607504803c413130f07070840c1515211080e04107032105a038060016005003414a620b41808035403616030031600136440389000c0c240d6542030391507041a035003180c0031600040100400e0b0442c1c00350795040114200a440bd910000351200c80701c1074140f06042c000c3da2980c60406d058100c0364403610 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 681715926 1250 681714676 681714697
    0x14060307170709081b01021e07090518150402060306100c02090c0307091703091c0606240503091b032103010501030c05040f062d020c09011715040503 66
    0x50404160207043c03c00d01d8015214a8450008004220402d8034100e061200041e00900040010442011420045c2c0407110315544181d0724001420700352407241c140f0803200154041e21402503103600f13604101c0341c007030908024000c0c07006000160703803840c0031240c102d81304a54907207002d81c56240075140001c0e405c0020750701800c81c4007004400700003c00258491042c681c4c0b40050b0703507210001410810840000800c0c290f00134082103540c0d08200d1424100070030364401800ba40505907494405540c1c031604010b210741801c403006108000c8044880140c1c0311142000e506526090030b50030360f41d51031000c1484180d901c02c0c402d03c0c0c194506001c08210a18041201c62a0007681c07004584194004c3c4070781800a40340001c003598491054003602c2c244c80c240440056500d2a00c00104c1c1d240c444040c290309200e0290304000c40e00c1b005103030354160354070003600906400d08080d0204030b076042c4142e0181102000c2600707107082507034000c12400450b0040409522003a122414118507502a1003820b2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 681717176 1250 681715926 681715967
    0x12c0402092e110708060a0e0c060c0f0129090627010f0504050f13030311030a0f0b2407050307050106060203130906120f0203010f0519060f14060307 66
    0x102942c14030150010200c1c1d80c661200d80d050110054907941d28a0b980c0b0602000c0d030809408610040942d40145c160038007018101c5100c0002400080c90941c0a0003c0c2d0500ba8840401c21b501e80c282070107004a180050040c0200c0c0041154203c4442012411000d203d02c980c480055120f941d000c4580081341030841310000d083c200c05031481c00820003801014150001004002041d150a00502d841140c00c41844103039912250940314441414a1049013032684500d19800d0000300100514411134201c40d01161320640c01c5401001c8070360341c1558500a80b042c100032154009820180566900710340407559480c03546051003400c0d80100304001b40076508000c000208140c2c000003404403054000c29400c0865521840c05045980610841004280401345503000c40c801410641d41d050020b0004a000c6041c00c030000125002190b6140405403003590f83c2460515a1081002410402942540c02e600b440d034101c60942004d1003452203058004001000c00c1d00c1141401165003810400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 681718426 1250 681717176 681717229
    0xc0510020a150e06010503191e0807030906030b030f210f13050102100c09050904080d06080102130e04021507051002040815090a0c090e0102042102012c040209 70
    0x7040160041e9004950f5a20580001080b28540030485440e0040207655540c1c00b071845a48003800714042124200c040c0d0030048009010a45450003070501a1090f41c1d03202b000345c1000f1001d0100d0300710b0001180a980f01c1c05040d000e1080000318030080352051121030702c00199800e45e07aa224030030000700701202c800115038603500c910740300c2c8250f050303032000d0302a1518041c1700100312003140d60700c41c90304000071020342080000d400d010a00c541c00c203009581d1300c2d1800380120307405415a9450382c45580e1030382d400101000b01e00c0d01d820405006d1b01240f8107111286c00e2030380007e00c2809880c0c007a0020780c0b000003181c90800ca4100110310700c01c1d513640740c107545465483c0d80007501d42c1190000423840c041000300242c048800403078400c0615071b206500302042030900d00315600805000004030042e660811006c941d43c40205031046803088000c03007014a401080c0300050040d288013480c801c1528412400c0386060742e011074101e01d207410039600161912411400120030f2503c40e0140885501d0f4401c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 681719676 1250 681718426 681718463
    0x6101821060612050105060d170f0702030303040c0f06090602071a04050a030804030314040b0a0309060f09150c0311030c0f040911070611031e04023d0c0c0510020a 72
    0x401a0f0030b004100801055407007074284200d03454811320080c5403900594141c0f150540e5603002d80855400d070a074060401d10564046803656005440c19224056811400c119a00712400e52901030b10143c941031207850301c0e018000e980d61860340100e000310404844142c0142da1795400751001000d004200e00002d40d52420719400c5031707005000c2940003420819591000c42483c0c0129400c54848014041c946140c0c06c01c100d00500316280101c89040d01e402c02007004032201d00892400502458a0f4003d51010702060070441d10142c00720800d05080c10950f5141c40020f2090b81da101600240c0555074660805054a00e44030301e80061801d1494403151030300303101c419030140c07000c036110785410803040081602409050104560030030205a0400000344d000010865a5410510103450441c0f00e140041d020110360803422002000280b801d030580c4074802903550403031040e00e145c0c01d10820000c46034030382c4500d030000b07400740c9401031850200e4040c9003031013000400e4046800660b80c1d441c4404064 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 681720926 1250 681719676 681719699
    0x380a0b0406080a0212130f05010e01022a0a030c080f030106051c14010915090609091214030a02030c161b06031a0f130504030503061018210606 63
    0x504030004034502c001600c001a00e20864030315014110b03111001350b8403210384003140b09841004640c2001c0c2080714200184e824050a0200607134000096212070044c42e604400e0f00c07110914080e04113908408043c0d9080219005540e140c00d0b00d040009001035040440c1da034800d501c18080c0001002000240c142d90040260540858000b141045540e900d4000343c140c40c00301030140044001c00c40108001000e542c001c00d086000020900d6889580e08030032021035044d64003000c8003a8460303040604000c8213008510408215041c130308003003000c49266104500004240302400c80d800004a8412002c41007554280d4070220112120905a0f20b0850300400501749a401c03404144040410618001d001d0350702040d114038907003560341900e00701b0041d6461808010f142c121a10071030710709011003140101d920660080e16a16564103141007400305009030f00c142c0300100b00010740341e0071900300002548003c49030300b00d50b0710440d030345840d03403142c83d18103523a0340207016a2170242c0001d4600d4140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 681722176 1250 681720926 681720929
    0x40e22050a0201080a290112050108070501090e0f160903021f09090c02030f0d0e03160215070201021c020f071206060b0307140c150a0b090a380a0b04 66
    0x3a80e44c5081c030b488803c5124161420201070440c00350103080c0490a840c074100006220300e0381450048152210103002d042169000c0c2c20281c0260480d0300180f00558002c00180010500d08070074800b40c0c42c0c030f0100ba00c080c0a025019803640180c0346c4c00b505460b40308021141c050741d001000d0200354000e441400d00a410707610000c0c0c0100c0c3c180740000039003d25a01c60141d0358000c0b48c014610300040b01903503400e0783d480301051713807112a034400d01d00c0e0110404102800c0301c0c1d1000100303040d8418680c01044550300188403010540d190030080c0741c00617640462012180000300801d40b0700000c071844181d080c643c42d55541c404074070903108c0008546480000d0ae2620a008080410025888440400c0c2c0c500c003c49661010a160140f403000842040004240c1158030809540e90305282641602c02d58100f40d44114441d5180c5038102001d00e41000d0b46500b00400d6407080049603032103400c004010f001c0204000012021500d10110b8140c3e00d40750206062000f40103400d0240c0700c00d440d25032030300300c3d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 681723426 1250 681722176 681722179
    0x703020c010c020d0e0607210206040302010b03120403150b060d24030305040501081012110301050603010c0e060a0509030330191e1d160b040e22050a02 67
    0x7442d5a0085080c00030418844e40300d019900d422085e85072034117010742a44042002c8a40700b444015280c10085092907800c904120741d405411907061a00b0020309407070060107064402e41003890008070900c070300703011138003120360022450650303404400c408001409140211504030360001100c00e0b580000b13910040700300c0f40d100343c8808104c0340a030044400000303c0c007004012601c20081032000d9070040e0f50039540003079040e8180c1c240945a203010b007138085461000b19204015120f03081920f16081c0aa542e001c58284c1c000c00003500800e40c024201d188090800d4046c90002803050300442c420422502d60704405009c0f2942c1d001059103002d281d03503c0c030840c1c0c40300c00b42401c0302e044540002501140504105601140c0740310b00040c1810082031002d030980c40c00e00803110400700342803080c06030341180f0341c4070070300c410300e40a5040007603040454900e080c12081035008001c0c003100c5200c3c001d403410740e0000b003c010100d603a40c47c40090592482014250906503d10503601001000907012080510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 681724676 1250 681723426 681723431
    0x601212105090406091a040e070f15030c1b020402090f1924141312060504150204032109030803010e041e020d060e0c180a1a0a03080a050904050703020c01 68
    0x107445040008803400c0700c2c011b0006204140c4220120724058100550f035039002c90941d40040d9a40101d01011203650b4080002e41010300c40050340541c00d032191368004c44150400c40240540e0410030b040510680d10000d100d6a4042014045a1101c07607445510035405042111007080140455503c02910f00c13a04000080582190210720006460f030461090300d80c5a041c4508203450700c281258000644038041440989000640008032000c0b40107024000c6e080014142028289090b5800c846a0051900d0307004020400c005010205c01c1326908480180e480709844100e003040321380c81c07070340e51024108820200010403003d2071030820354007961144003100c08160042c18280c4912a480c00040d6002403034010f81d502150700c64010f650b0b42d21f420015100300070071503c00100c0c0100d5600a51270100b441e042003002040c0a8407404403400101400004003658001c0064544090303030200074071a000204401030601d00800c140c60b2001e00040043c8014035100100030000c0d0042c100142080d030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 681725926 1250 681724676 681724679
    0x1202030d0f060828151e02030402090a0e0d030905070f0f060806040c14070204060305100f0b03120a1404030609111e060405060705030f04030606170601212105090406 73
    0x7602041c505681505405038001413240c0d42c07580c803040d002c000c41146260351580c503c0041c02c2c001d145401c080f640704920058490401c0e0061050205c4000e00210301341c0c0c503050402c0c101d00f00014076400818880d25000c2070300301c114a001d0781418070f00d030b03c00c0034201000000410040c0b010100c11083d0b4120303a9402403281c3c0c13218100000d58070042c04840100d5800c00480000c0c5a00c0c5004205003030001c5e00100c1c0d0b140e41d9941e031900e40035900264001581d83c030151401c1442d014010b0b0f100303414084000b4078183c042c00d120400c0da0300c2014681d4041c0008e1000d040035000d0b1407000d690086400c1f84040206a00c0c60808010140d036020516100340840c0000200d50703028207840c5407001300060310710f030308044c100001e005a80e8403a480665031403100384202510740210320010409103224180200b1180d1416024541c490304901f100d1015810032801071110b00c0010303c815070001e841d4441c095402c2d00909090080054900c01d07001d240086250411246401500900520400761020412103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 681727176 1250 681725926 681725953
    0x906090c150e0d150b0d0b09190209060f15030906180a110609010c020402130515190305100803030f070f05040b0f0306060c0304140405180a1202030d0f0608 69
    0x854042d0041644070403002480008280c8041c0300403403020400d800081c4071052403001070098011088101c0d000c40100f4100703c01c412050003c4685a20b00f02d9089141c41c1590380001c070a0f505c001c01c0707030340507114020b400b42c0c41c1d54641d0001240210240c51003581d070b00344251165100e01c0112240d0040c0744640c4840711018900055051599401c001c08420825490040004a91100c01c5c40c03810440c800c21680302503078581c03000703081c25020082d04070405464102404085d500c03100c8002e076202c0c0d0030700c080c1411030810003d801109030549400600384c0d5441e125412100030707681113005544004001c01c0f1868105001d014011019901c840c050650046001c942600c218082c50f003040c10240030070001030307494101441d04000d0041c541350800a100c004281b843d0450790020036600303807030ba80b01001130926209180d00040490310130304d01852003507202940c0c3d0710b42c00c4005000031010203007018560320034429168091810700061040702e401035014000f40c45e0501894550b03000f60010328010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 681728426 1250 681727176 681727187
    0x150a0b0f1c02040c21020d0e0625121a0922031103090d080d0b04090c03140c04050a0b19030b06100309051c180506030c09040906090c15 60
    0x90404514820740c0080c126800d10010781550000340d010b205103035100340c507040d0030551030100d00b0814000043e201c0807518101c4040c2c41114500e00c4241d0492818050b1a0542c5c11318100b0074040c074903000e4401245030b0700032291589040321389070304070f85480b203841034918003c50b000c000d035a000c4401112a8880c600100300c040211419202e401d0205600070300000e0254040721a0a0b4545041d20b05140d07030031005c504240940481107558410007e800b04003013800d4815881090820345080001203400d903039865140145020240c0006090102c01950007020001a4011040070340140498200445890003070141c80b441e65100c1d0f00f03100280c840f03840180c0d0700a01203030341042200d08152502014041c1000c003080c800810942c580c50041e0201b081041030f0f1056000c000040007090084101c01003024490b102840c030522403940c01008565100030a403900503110201d4240e891141400041c010b18883e007005001c81c0c10700340140284864010104210343e503001c0b4420b00307400302101c100c0d40c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 681729676 1250 681728426 681728449
    0x50103060c03050c0d0c020c1f080c0405060d0908091806040608010b100804020307030f0323210604090f0c050f0105120f040305070b0f07030605030106030f0204020c150a0b0f 77
    0x4030300140007118141c801a00b040c1489a114016104024200303008a0011189c148603030700c5001039100810107407540122070700d501c03078401c101076401c0c1070510700000e1480c401c140750b2050340c0f9104c044680c01d02816408032010300b8001003e20441502c1e1030720100700c014040340d04610613480e100c2c0018142d041030140300c403c01d1008210008000e01d001095551080181060303805128800b000302c00581c04a24480c1c44a001380c0741e00500c2c4000c0d862640c24540380d0038144035503250500a141c245c5d008804600600d00145030310101c030b0381d01e5001040003051408405040e041e0f200b0100300c05c0c0181000042c080c0c441c140da4a0540c100b002006580901c110380c00b20703003411400c0700013032010b18590241b00e4106100e843c1c0103150608907107a062140405440d01c411420010041c0000c0c150035214003801464290024031491b46541c0b1583c0d4120f21101010307000701d400003284054031409004024291001c800c90f00b42604041c10244010014448500d00030b205030106a2100d2401c180c0c4c81c01c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 681730926 1250 681729676 681729691
    0x1802030c011d120708030c030306030d3b0d0813141e01031112060f0102070b12060a051203030a0b09160f090f0b091e100c030e030709050103060c0305 66
    0x802c821010500c05880f001034404041c5014542c40410300030310520052801d8500240190303200d007030001c101414801908800014082034100001c44014000c401060003035000501100a18000140c0043c0b0b91200078a140c0c0000484c00d0380c400c000d000c00c05000c005566011000c41d241d101c50340c4020030b12013100795591001603d8090b0300c1d81c10400252105081040c5008120113106844800e940e030010009132040c0c000b018200700030b506004c240781034400401d01c0182402c5240800c80c40c15485072210280314130f0f010100040c0c0c4c41c0c40c2d410040c0700401010f445011074200d550300a548940041c2e501d100c41c00e0914503440b0082c50030442c00d900070901d854120082400385107041e5400298a90303000e0502203d51000202c01d00a22441340c02012884401661032050390100420400f900d008000c48100e0500c0050164031002000403c0140c030303083c01d070301c900301d00c0c02c1c183e901151a403500e036450710035104085080001500103038101c9101e1002848082c07016181a0141d03003045440c0d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 681732176 1250 681730926 681730967
    0x1206050411070f0804050a09060303030c021b1203090a03051e0106030c0905071e090617010e0708040812090304150e0f0f040b06040314250510121802030c01 69
    0xc00d0001d41c200f021540301d41d00e41464a1307a0350b00450b60029040d440f105d8407681d036000402c03c1c99014002d06c08280030901c090305402c02c02c80d0710f1a098034400c1c054540280c604801d1011105d4040089030304004005060b200340c0750340c03031605030f50300d560000d81041c03840d0945070b01a01d44c8405011320780c11342e5030041058403428104005036004000080489080194000030005585540f44003004403003540e50303031103060505102c005401c2c041800c2028410015910040000640b10b031403881d08000f840c90080c0082e00d85c1d00340303543c05000d0403510400c1c0303010010604c500550000010000c44d041000b118400e161058004d44a0b0041c5100581e0060405441003000313140000d00c510443e03000810014a1015020102e4119001b5400844050070314a051141d202410091200c0318010581080d98202040185013140301d801e20886004107000e40318258414003500c444e5010140701c103002c00804a40d03e0b501d10b070322144940140d000380544801d061302940700c1d4650030200100454031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 681733426 1250 681732176 681732187
    0x30f1506020f0a030f14070609061505010c0209160c1202150709030305030601080a0e010207050a0c05030c0a0303111005130209070201060b071403040b0a2102031b03040c0f061206050411 82
    0x646002d000c0d0a40100e81b16020091940004d07124804c140509004060002e007210400050303510010094002c1811321005200403c016070b60048010781c0b002c3e11003e85481309604040c151081e10101400070a141a4120a00030080e80055000280702c6407908880b986c1d10781000985001301c05010180009a0070000181c181d4021800c05402c8076007401d00107010503040101c035003284c019690844140e008155402d0900c00041c90b801d02419085010f010810714040010b1001c00c10b9100040500480800450350070609008444042d00066402d1006240c0120042142e440c0210102e00c9003103190085581207105108110540318007035013891425406407180b51814000901540d21072000300800719100c1e10420140207040061340756540e000800040340c804848070151080340c22441882040344003a170340c5d05248105034183c4078595503600d0743c0c1098130004406030070031662000c8008000400c1a403001e0b6900c1175040750001080340341c0d102c80c2040240d03999407000c2810004103022 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 681734676 1250 681733426 681733457
    0xd050a08150d06110405030f010e07060c060b041107121701060c170d02040513200d0e060411040b040905060408032208070c270c030f1506020f0a03 65
    0x540480000005080210004881c0d0f00d04041c1e0350003e02038401030a0108042119042c10443c40d00806100d00c000c0c403200c4440800d00e03541e05800e02c0382400708041d41e4441c1051081540c4211821000500140040d004080814440364080102106c0c080300007282d141c00c843c030603078a42a9050300368110200c42d9103061801c998042c0007080c01da501407159203074107c00e0b1041d00c00400c0c05070b26040001d0780300c600d00420094442d844500360350240d800c200405030b0428000691900b00e41d244901ca80c0c07101210300000b401042e01e500c00d81c480348158018007042c0300c41c440c000d0413040c000711014008082c4c1c0509000581c3c080c00c0000b8020790000001c82e0004d4680b00145038020f0b06418800e120341103128855003802e49004007640c100c0400502d81c000e0040084d0880701400340c418091541032588514140d800c0c84500c01011402c1e515000708034602e01ca40c1200700040c0011409000407294058400380800e038500c5044054070a41c4440e0741c0b03040e4041100c62178182c040d194069890040344 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 681735926 1250 681734676 681734701
    0xc0b0309030c010203010306090b0f0103080d050c0c0118110a031a06031912021203010522061a03090705150a05070c03022d01050414040b0d080301080f0d050a08 71
    0x1009112107000500065110010034405140218050000416000400d0030b0003200c03490040c0c8841004071030100180082032680040340c05a0003295030000307484d5100181018a402400003050742c0d1350802d403010030940c02440912028a0080d5425815091604100710404545110081010b0520303204608035001182c00705502040107030981e203056080c034880c558100d10964044450b5030384550b00c080e990b94104189429046080d600a00e13650510700080c5001c480c0019140b00912083d07258941c01c0c3c03098220000510248a450341251502d4552140c2c0d0b8104a414401e21b1040810010b05450002c40031b9075844640c030062071416444000c2100e482d8042c41060b1039a0505c44e100100580352200c03017260f15540c0b008852041c01d50b4200c42907c0c4400040701c0c0341004801d0200788840b0081c0b011900e50140c0443c0c0c005420079142c40420901d04103490081d002c0c0d0000f0000140c05035000c41c017030300b0204650098030906800e158083d501c44c011841040005070078240010340120900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 681737176 1250 681735926 681735931
    0x1b0a12020f0d0504030f020c0f0904080304050a063227010e101b090303092c0705090307080613060b0d120906020706080c120c0708070b040314070c0b03 67
    0x312841e442c0c0300c1c00c400307614240e5200740c8084001135030041044002c0e9505110407480100d0445440c011918290005004104c001d0006044904004041000c001c81007000d030550f10360102d0305111502ca030801800300f50000e90a0b070030740c024590703941d1940310001b2a005ea10442103040c200c0249401741c03400c4400b80c03260303c1804a03699600e0f40ca009500c0003c20007a182400b00000202c2c107074035a0b2102c05900111841e9003c10302235031800900009801031030344c1c001c0d213010010100d240080e400f084991039818440350201440c41d60203012003290312800400d0a40300980407500d0080e80c545605541c0c11048412010b95950500e8070340026051b038000c030039a90301c0103000200075030f281c2c0c41d403600d514060840d000104407508010440180c05010b5031006000078105203699203061204160244a070308007500d0012404d900246594941005a40c2ca00b6040b07041242c8400b03d92402005200050741c00343d0100e0517110500e104545000c0441d80c2ca01d0748501d014a60510f8a080006142c101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 681738426 1250 681737176 681737197
    0x408060a022b020301030201030b06120a0209030316080a0809061003030c082101050a0611060a02160b01060302031014031902040f1415040b01021c050912061b0a1202 73
    0x114050b0b2080c5801e550a407180099403040c0143e4075455031001608440c09441000d010320341c01e1005a41c184040041c160b0310040401c1c000da81d403010600007d04510400810703520000100341d01105000302040a0440f5030720341c0d1150b43d500c0e1a004071451751040304907404112001c50a90900010380b01d80400d100345882410030030305091404419440d4040171550780c6010f0600781004106520f45000102d00501c0d1504008019901d402d03107a940310000209864143c0e5000900c8070012899a11800740c1c9640140c1c80c805a0750f100d050080295000f510480d03d07403591460b02244165041c2100c8546400090082240740c0c049000350420070220321050f40d1180d0350716200c00698409025807404c0910105180f00c2034070303228184005074500c0100250041d0300d480e0030f00c55145d07000101c1140b182007004e024014034059150807981e500c0f440d021290000383c018401e0343d42035000503140703000c1c406448800c00945401000001030b4010140ba500c000340c603070b12006011b18076542c020015906c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 681739676 1250 681738426 681738457
    0x80c0604081221090c03011422150212040c0e1302220204081e16050603190218030105150112150803040e0709060306080a140f1509120408060a02 64
    0xf40344054000c5200b040b034020001c0d07002031210010310318082c443c000701000b00300e0320040c1ca0300b031011110f1a8040ca010700c030420242c84100d820b0500c090411001520701344880190b6403940c0c0c00c800d03020038180c2500e00f152810b01d84031002c203410094844040c0324100b4003100d05411400c6408020880c0c1c40c0361000103106000103083c10801d01d0300d0000740040d11340382005042010010840c0d0310110010b40d00d400c402c1c0c0005d02510070030100d4845110494008883c4140c503034803900629002d44100115807003400d80300081d14a0b002078824003134541781ea4110001c0246075180241740c80740154030020580012030306032010101d4010f9a00002400304690084074bc4541c0300c840c481e15560094002c1c000b400d94040030041515400444040904424541401624504442207135244a141d5000700a000308400300203142808000d8092490f00740c0c81195000d030781112f0216440708040c0c506482d94000c02c4000180501100100e4080b01d548000400e05a611070850000035003000714040301c00d50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 681740926 1250 681739676 681739717
    0xc120312050a0f05010b0a020f010e0c01031d012a03021603120917030a11040b07060b010309061b021b0105030a0c1e02010203070206010515031b0c16080c06040812 72
    0x8860781300301030181c0f141e400e916583c2d1070301e441c020b07160100e0400111110b80c10000c1841c1101c5020400105150081c01e0200f82c0c40c21842c0e5a03948045855800d011a6103001084044600c1d00c481200801b403800c501600d03074102d40801101640715804d0050400c281e60700400e00040d1185c0d00407070205003e030100042600c0f040d0b40350100020744811568a242e004024018250041c0c03003030564a21544d10224500383c50300d02c030740087c1c2c090000c024107415035034201040316900a4200542e4698880000c0000c1080c0038201c1d1040c0244c41441c0006110708800f044200b1a2018240c4080005031145070070760343c41d8814030020301418040002008401e809612a00d10382c82c014005c60b1031681c00260b01ea16010070002e1410b50142d1042c0d01c0b1340c0d10503102c0c01552203004202da800c004d201340c0c00155811841c4c1d40e0142071042d60201503030b501c110406840c460580c00c040e442965661403d40d00c518211004100f0346000350f001c0c0710515000000c1d04220111054001c01c50b0380080c242801014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 681742176 1250 681740926 681740951
    0xd08180706020604051009030807050d0b060f0c0d03110909061503040f2112020309070b13210507120302010902031b0111070b0406110c04020304030302070c120312050a 74
    0x1100e5445100540d01100c14402044002d0241100c400b1141100704095040da0300c001f01201c03005002d800034001e00081c00c100345601500b003d5903100303016020b6550307804400c12a5407107501000c0c2e01007143c003400312b40440f000d100303024a080c0042004182c07818240c00034100094490083c001d0340d0301030301000c04502050b0000c80594800ca000d507001c600c5209442c2042a0307000b510072541d002e0048600404014650880f0ba40d00c000405600300585995a10215610780079080d0441488400082107002c03c4900102c05001610508013880000200d005030031205165a044c0041007034000072000d201c222141480c20a1040c02440046010305882c0c01190514450032201e81d02c1e00e01e10a445242541c00c556103481c0c3c14007250003407814501d03006500286014078000e842c1002101540013044007030800100f408400300900865072400e240c031b0094001e5128610441d106000b4410001d4500c40c0c101e91400d001f60140c50f00750b40303501074050200c018040100406440c0e5920403000301b07079 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 681743426 1250 681742176 681742183
    0x2030409181403030601020d0507020103090b180c0102240627040c0e040f0b09031308030c0601050d03211d0f010b0604290418020d0c09080d0818 64
    0x44001c500303001400c0001504105074030129940389011036601c200306000c0a030741d0000c0e4500c0075410900d0f0982d1207504620048010b45104007002d0041c40002e4144080b00c83c0950a85000c10315990884440c4d003801001680c0700d0100329440040c103803050300c017219010440b007411648810000d01c11a0074004075000941c1006200c1c1e46614104014401c0000308448410181d0143c2040700c0c1e02095481d10707540e640385001020070024004c442102c08501462010000d913120040f901074015540303900d410b102581c941260111200512402000090a050404609900a80503902e0b94003201041c0c005000c801c09000d000404160303a0300c0075030311107000c44100d0108903074642d01421502c208540414251280c09485078071402c400c010030003608014061615040100c1800c1d400d07441da05081c0c0099601444c4d04c40520300c4d5400d01c034025402041e40c02131010812500c0c080181034440d000c200d4401b00c40e03001d0401c040c0c0c400c24a60010a019102c81607104241e0110520b03c0d40e0300c1420b10b1304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 681744676 1250 681743426 681743441
    0x4230304140f06070809040f020c0f010203100e0603101812081501030b0d02010e040b090f07091509140301090c1d060402131701020c01051801050702060606030a0b0102030409 77
    0x1000c0040c07080c58106140000541c40d40c4802200e4103820b06465072500415031081921442c8100e507569034585000d5010b4040d500d90750040c40a9500ca60100c01446020b54802c883d0360213030000323100000c46c0d10901e00b85c0c440c0c041d078806002844080d00c2200800014032400a00e0340c1d041c0000490381c0005440e0080028010a6039030341d02d40305050001c0d0b004064213440c0a06414141442c0422840d070f19041801e5500c1502440c100c1301447c00080400c0c001c014042203075412810000400c445c00b00903814441c0180400d0396014403075036403490034010b140a952044000030f001311108001e4040c90500a4176100402400051074003110b988480700c0070750590100c90f0071320200c6940254218030411455000c0d4003554150314040101208200c100302a0003000811003894001001080d82541901c004245c030f035000700490309200e9420950501481041d43d00ca60030140051511440829070901070b01e0040c00441c111340310507040002900c2280441c60440c48184000600005240907101c2c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 681745926 1250 681744676 681744689
    0x60d02040303020c040c020c01030207021c0b071d211009060522050601052812020f0d2d051b030c01051c0504141c1b050604230304 58
    0x1a40c6920714640a400e0225480002c1d100707034a00610b0808040e004141d12454030720034a0010f03a00c42061000410402450545840c1c2d00c0c1d84a0901007084440244a40204101d40f0b0f0b09103000d50084244000c180620f0500e50007000340c44009001c0a04440b4001c034001100c815108401a11100402182e80f200e1040d2480342d00c58040c8001d400680042c4416154a2282c0d1100d11280340c48885c0c0d00c000620681e03009130121309242403424440e810301204040f045061100050760703084400310a02240c6020b9101d18594407020009140ca1003813142202c0d440041d1a000b0f0f011441101da0200401506c0945440103010000005106110070300340701042c2c5000040c240c0e441c000349440c0c008003480b41414482c04200080c404010014980142a03030140e0200b0643d81b280390050141d600101c004042d441240c81c18082d5011125103020004820750300d50b920400c482e010b00a000d0400c1c603000c1e00b281c201c100418080703a00c102c401213003c1d01482c07140440010600e00d0a2441c4d0240d400712 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 681747176 1250 681745926 681745931
    0x2090406050a11120f1003050d0c030e090f0a050402190602150f040302030d0906021c050a0e2a040204080a0803040501051609090c0e0406140a050307060f110c060d 72
    0x1c006152184500c0342d490fa00d00161500300f0054104629071058007a14055040c2030680000311500918250100550b5004080d01d90700741c0e000c40c02800da042d1a01d0b044020801050f0301003075604005134214461280c0c04514450f84c5c0340d0f01040c0000b010701510aa8201c2c00c01351000303112911006c0664014682c41d070040515001c500c1d0380d44010b0720041c0c91044042c503900d00b444042a03000042e00d00d1002401d10000d81c03285a0b240000c001c1c4580c00c90240032141b1345581d10401003403548840d10403024110b0a0000a014940c016142d50410b031003e1380b04000300302e4014050704001040d203540c5030086c000610341a1a01d0f802d91800c02044021100003000104001c00c01c4800c1c007906800074000145040002c81076030010300500010b000d201c00f1182d640c0d03c00501d8034413620002c401303088050710030024035468001040e10043e501d070b80d0038040d01c824400007480741000145001101d44a42e1040407014810108569500040e0000380e000e100b40d140c503419503610100203000145009600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 681748426 1250 681747176 681747181
    0x60308040f0602060109140105090702070f0b09031009081c02040302060c0a031704030f0f022109031e0d03020906070816031e0f050c100e010f06080d09050904020402070209040605 79
    0x2450840160401b0b070381141060030312550381303000c90281c506489080b00d8911507552080727400c038030303040d002d90120a01c0300d5243c00029080c0b9085005185011040c0d080e55a07030849001303140255030344500300400d0f86800b003045c000d0f5541d2004d0440c1003c00c0340c10025151965a030002260b680242c1a210115040b6044c02c00c101038100490014521640002c900d0b40d180c81d48019203140c10800f50101401410034524851600c00e0001c40c600c001c0521840100000c42c0662414a401c000004d500a1180803001c0c6070807072840c22003080c5080e640004080023042214114041c2d0041c03201c2d181c000c0ca0500802c00012940c0f40500304607001140c00c0103614410381030041c100344408001c02926060341c2c0b131040d0043c0d80013100000f41034075420401e65841074900c0702403808241110b8000c2542c5040c0c1003460307544041d00400c0003c8600c4105104880c1c4480905031141842c0c009140400c02d150320820840c14003200c1c00341e200340003c0006040c0121900030840804044030100c0d042a0f0354405c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 681749676 1250 681748426 681748439
    0x2030a0f1a090f010f0e0c0f0c010e07050d05120703051e0304061a09041106090a03050a02091521030f210106020d0507030809010e0a1506060f0c080d060308040f 71
    0x41c141d480110b030001e0405130f502d002c1c03207420180b0140c080e840009001e00d00282c0c140e0349000c2169146000ca15859036104c48500c06280200752102c0b0a840f10f00a4900004503031038136000d04280700750020007826042d84000c04100035a40290412002d000d024480013001e808a20200c4102c0d0400034001503403031410b0300c2c4c0701086a41d142007060b2800c140416090715070b00c5a01034194019444400040c554050400083c0b442c0a1600c2d51a440180200e0200801c0340115911001e94401d90340900c00d0348960f0701c02c0d0b0039541c3c03c60b6600e40101102858240c40804c00802c41403000801064134a4031151141c207458982c41500300c020040c6a104a403005c2144408004e4010501c0b0300c090045406044c20040c800c0c4180140502004403800200794401002c0d03210009081c0b180c011228031410030b14062100019994402a0315441c040000950a008000700185070b54940e450070b00452540c0e0721406660000000d507100160f0320800440007a680800400191584c080d00060311443c014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 681750926 1250 681749676 681749689
    0x9050c04021b0c150a0309031403130b090a051504030909060f05030c040606140c01110316080a090305160503090a06180906181d060f0103060b01020d09030602030a0f1a 74
    0x4803e40074004480c4184100c9840c00705560400c0014a0081500042d03400e0459001a0408154013001000403d2200c0c681141000780383d003034400c040800060b03951030a065100c40c0880303c05000e513000550003e0b4035801c40344034140c0c09442418000320440c1c5510b4071504032034080e049120b200404030b50a000c54941002510201682101e0502880d1f090000007050040c2c044001c4100090114419003160f0081d00024400840d1809943d204e00d0a02038a0341c80e4a203110440c5c011542c4070011540021260007242070494064841514100741040061f542c815051030a90b01da00041c001d0340c140e41e540318499002003210b540c0c0c0503000340e40c0e0500d1480788000d40d8040700c5114540700081082c1c409007070301000c801418540c0003503d100070b031710600000448a00c0340301c594011a02000485d440e01c0308074906aa000750070030011541c8603030040e43c1d01c0a0704500c49021903080401000002c48503001160710010501011495000f030706180d0042d6850584900030703810038503030030954a05000c4c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 681752176 1250 681750926 681750943
    0x1060f0509070f0809070314030a03060e0705070f1a070e040c021b060d0b130e0d05030606031611120706111c1802060301030605250504050409050c04021b 68
    0x2140c8508035420711000180010718000c40308000d001c1400300040c5c042000f4000d4034010f5411901c0c69034030590f00d100642d12940232100000210b07181c031501256010b809464240300340740c141c840500d070403515121040c0024010070101d80b0352101001c4a07101c0181034591038061040c648030395094900030810001070744d0b0544843e030b086520520b00401c0042c003440034071404483c00c0d520140d450304c64180010180c90400c1c00c42e038100828149041d400e44099019000b0300d546007058501c1f0113840a0300302d0310ba01c070507203030705034400d1041c2302250307441c001c0c015241011410781c10710204545055900504181201801e1103405c01c02148107800d1006d140100c003420040986001d281c85a50300c69003920140c0d411460b40c286a03144101150130400d00240b5800d50f8004180584941c1c0d00d1900c50041c2000b2a02c2003a503007032100b1607141601c89240c1d09050306130183c60710f50601d41000148802410103131000e86561207410080c01d4152618801070a041170781e4541015100720410782e052822054 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 681753426 1250 681752176 681752179
    0x20c01110c1902031507050d060e040b01060e0d05190201090801060f0e04142a0405150d1e081b030a1e03020c1005060f0a050a09020a17070201060f05 66
    0x4001090702000082100c0c00450941e580090301c119031800400d14040390080c0d54408103044800f44002c150b04031000d071882001c001c90511203207444031803030504c0031020380e402032040310444018802c0c903015010005048602074000c80c001c4495480306450410000300342100000071584450665a0108401d005408490028080301c0e1401f00100e85440ca184a0300304000c03040400704080098441041c02640040d0b0110b400e0714145084035400041c07034040384015840001141c2d50700d400c0c140030b407a02c100c0030b03002c84010010100e81409011600c20703200b1580240002309548000d84094501508140201645e030b84403030f41d1031000100d003038000d080c81e803159200748038054486a202e541000e03c03410804100c40b00343c40e2140d045d4080c0c050b062400440e0302511a00e281d12884980c4014810001112245d0b080d030040c4080c00400340040c0101c81d040568580144001c03012074004110600d0b1600c0e041e88950450100d03445110001c0e518100140d44915007000b5501101e103080024100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 681754676 1250 681753426 681753461
    0x50604110f04061406090a0f0806160f090314010b090a09020306010614031609031e0302072709330b090708040314090604030809040f0e120304111201020c01 69
    0x8004d4000403403401500c000b4818503000a000001da02c031140e05800500122a5100c02151900009a190001120b1300790510802051a455492148149040300c96403174660700702e110309540760000000d2403102c01c00340664032140131110781c3d16200341035031043d2102e40001540c83d0b55841003604020042e4440c00400900340408405841d005045a0f0000c05100b160340301c0e0041600c068a50940b80d900c05400070482904910320020309080061400744280d00781c82d403080c1c50700c4400c0400c1521000c41c000b025041030003510b079050203a00029185d4000c464072104007003513040401685040c011700006113226002e038904c05031680d004282c9120000c84a03240140340402004241b400020409800c10104442181d108001c0500300c5e1a60100606159541c545a082080c841e50014620740d00a5180214034440e040d110700c20700316604c1402c0064040c024896424119035000603105866010381950142c1c0e81d0355407000a10380d440036503030001d6107d4200080300c0342120142c4005886110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 681755926 1250 681754676 681754679
    0xf0d20221e1419110a020a060501090509030409020c03040902030403020f0d0201020306090c070f0b090a210c0b0a0e0102070c0510140d0905010f0c180611060a0b0607050604110f0406 80
    0x210005016980418a0244001a0b030b80c0849060b0103403030704c4604001450030000e905e0404550110380400307050b015103024070280e640c580001040326000c48420f0138941041c04180056181070300100f5070202c0c035030308503401c2c65201e00100040b030b8410f9500b04d000da0702541400c00c1040c8248881c50160841e07000031401c62410202182c1d1903c130051450b00030b807800041d920304004c0e82c0d12a414542d500138180c01428a40943c410785c3c0e03400380038000c2d2800d1810381d017082e80e46044411522102101551178100c1501251f0321903000313010150440040d0307074032006010300c0c1c0c00092000e0940ca900807848242c101d0310300418041d0541400c480803040000c1503031024103039200c080417a01c0c0704056040c005408503017820714500424076810901b0b411806d00711003a40140d4070510070310b610001d00b18920ba410742d0f9108141c8901e10b4441e0034040d00c0d085403001403021036072603006950341c1102420484c500380380b6a0f906030400c10b0456003240c503090f241c0000581400d01002c140b003c000e041c0d40401c01c96 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 681757176 1250 681755926 681755951
    0xa0915030303090218070e030f0a150b0d08070f031106102106090b01090b0603100e28050106080907050609040203130c140f0d20221e 59
    0x4540400340601d520750100d20f0840d2030300e1149403422100308030840001d0070328400003420b08000a000c0c0d8030910440d40c54034101040444e80c0b0020580c1300e0282940e681c0c1c46001c10010b403d10984103030340000c07603041610104480300d0040ca5014400c90504440c00018075000d04054464200605070340d00a008021091500290101c1a00c000e0f000984120714102110084404201c00003003c0d9803d00d0001820070909040c1d49050f02c2241405120090900044c440c003400111001d589154208404014441f0000d54298100003960390003c030001091045061200041c0818203d0940d203e004210703030360b804669190880c0b50742d0003800c2c016260900145442c080d10000f188a00c0d400404980b11595031513106090907800001041442e543e050035103d41000080800c1c0030703a1000700d08000524061503ca16503e6202c403816402d0040f20301510300e0f400184c2d80c010f03000b9861b80141d0815080c1d80300100040b1180070000b04071400f0807607d62803001440316095400c141000090b081a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 681758426 1250 681757176 681757211
    0xf1b012304080102070602120a0207031209020d020402030f0a0b0619180504140f060103090b16030b120717070e1801060513060920040501050c03120c090a09 69
    0x18111080c08400340c0c01000d158060451003540e00c0580c85620020300603041003070b560060040200070900a1a6640d5000d041e0341c207134400e0744001000100742e0801e92103102c90341ea100842c61390003d019002c03900859404902240c0c010384101c20808248010800e80603224090203000042c00c0da98607061001d0a00080791035802d812001d4140840f40388000908040141414004c1500510a11201c00140b003014130400381918001c580d1f80554000800799406402034242140e880810f03444503545a94401c02c480000f50090f200b0942c82d001211003603a40c950b030337241c0501c695902800b412482c01092658080c49584241c659401c100703010407078074078104442e580c861500d40150b51243c41d04024140101110380109a0040491486803810701469114505446021408102001d02448800f10f0f100c4100012400900d0130481841654421409031908415080499080049420206041d0301040f5250500100d01244000e000e140401940c40100300090b004c10410f0000c580300c002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 681759676 1250 681758426 681758447
    0x251a0601140a0e030f0706080f130314030406150e15010809060a0902010c0c0b0409230106121e1b090f05090717090a050c010201150e15030f0f1b01 65
    0x388503102211600b070f5102444100c04911445d01a074a51139203850000d86a09025545280c1c0e00b856507000030b0710719010311900350565401d900d413400e02012010f41c41c04182c0c0000c10440d0050740301e800500c000840d10030610050481240012034038a482040c40c0540d110b030b400074a0400c00f85009104001e0404200c1d81d0700f05804e8203021070202a42c1c0016140d400c01003400428004601a0024400340201c018005036000301c1d6040c00400400400c0100c000740c410100006101084010031105008034000c856050019001161424003641139548500000c503902d070803140c41c2e680e02d42c03020003000e481080176001d905110012604020320518020000d0044a0048110402103004a40101140318802c000101100014601441001d03202e50006100311100e1051052092440d8010b002c0d08541110052081c4c010a16105042c00f683d40040e00310581c120300701429180381e440a00003182c403500908000c10325401d4103600e080c03501c0c001c50150034000c00700340725881440c1c0e48000d4011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 681760926 1250 681759676 681759697
    0xd1812261821090901050a0b0d0e10090804030b2d150a15090f1505033d0f0b07110a0e100501080c0a020c06251a060114 53
    0x14980c500103505140703800e10854040c16841002c0c55000000c90b400e000420f144841036422010707503641c400c24461150707840c4c02034540030401440074024241c1298000710140c1040b03402c940d240440a83e51804580c2e1601c01030348c00400004040c41404030300210640c1040f20000d4000b101040400c44461101001c0f0321601c6071066440810124803042003880b1001600900c0020322684d01e00560f0704003002e000048010501c40340001070381300c0e00000401c0c221880510718020449100b00100c0b0243d000401180a04000c100c0c04074603407020b8411440e001600480600d0320201d04100c01800c0314940c0d00010641c0c8400a090040c0c80b020030980301c80c6944448d601500c003e00c4400220603c0f403940080101000385c600300419080882074800c200c82084e2980789081d240d070100c2040307621030004d0003009607010440e0002c0c2c1d8202240108a0703007440c12400e011030448510070444000d00710300143c90303a40000074411a14854105043d0b0843c400f400d0200703240441d00a006020b004088400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 681762176 1250 681760926 681760951
    0x503070b0a0c080f03010e0a141503150901060f12080d0b0d020306091e030306091302030a1b032f0f060409061d010f0f09020d181226 59
    0x40041d600580c446040c55a000c25516110605000c01d11101c0d04248200aa01c1e400c0401040d03141025118480000040503030102d910b54840346045011880088010781520a8080c03412100e008240094080c0e4103140c008210a40791424001c0b03010600c0d0007030804260640c0480c000210004200c96400101985c007107090700c840400181c1007801d0320406501800f584e001c1111600c40400d00c2c1c07503403007542c0741041d8041d4400b01c40d0594130f00048407100c0d040300d04a408503881c3c0b0854402e2107131a0f44024111020402c1c5070341e40d240d5104200c1c001d0440420280e10510801504551120600b02081d050402081d19003160303502c0030070340400c032a00a18000b20800c40540742c5030201c5010701a00c0909100c1140d0b50200180008480000c1c001d0401481001148411b15010f403402102d00c0000d08a0352070341080d1201c1c00940c4074400d1048101c0c0d607444510040c051050071416020700680f0b0802c80340c0082d082c090050002881c100b80c40203028804102e500008440c225000a10403224 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 681763426 1250 681762176 681762187
    0x3051605030a050a0b060a0c03080c0408072603071b05010305190c020f1501090b0d02010203040306180b07050904060819080705070b12190627090b01061101150503070b 74
    0x413400100700c076400d07858210000242d280081c2e40c1211511401a2081d903480305030323130b85e4640000c10710301803401660402e40102c07500304040554050001141c1600740d200f80c600e203040140b940e00c2c640c01044222900c240808050040905401d03510008007003c1c2001d1140d454060f8201c01150035204544804982d540003e0034070a100708401322012806108440c2d520941803510f1443d000d09200b043d2040c1e0804502c54540d0920020b03942042d039045c0c0080d4140390a60703031540043c05584010700703070300c0c00f501802c11b011034070f200b00c0f081c02100344d03899443d92044418240025214903030400003180d445140150800d00e10078a05a5500360001600b0383ca8980350f181c041d003801c100c0c1e44007a0105101007034100c03110511002a03401a0680340080e000511b06603a010141c4102d842940030082040352070205140701844203403802c001045000038900c034150381e40b00c0b055100381c04c0781c030000c1c08040108035083c0c02480790000c408402c4c407010030301c46d251000099072154540101000100c02086 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 681764676 1250 681763426 681763441
    0x2010b010c3315050d02030a0807030516140d02010624141b1516050706020d1a18040c030f0c0f060314061c20031c03051605030a05 58
    0x20240b5002c0c034410060b0502c0c030010052080600b00c012080100000802e000050b036103003400c0e00001e03103079010700600050141c54507500e80a4214602c10f4040c00710820640c0c02680d0b207020162075440c81030510002002c1078420740707071819108488200c1960324201c400c0c00403605914151590b003070300180c140c06808652000319641c0881d0190042c419902150310034080b48062514110f03211000f0440b400503024041d01c0e44100701c1038070000510314090640382d240d20b201c0c80092160f01e002e01f40c0036243c0081c5a40c4a0304646000c0b40404040c44000380380410b0f440e00844010701741300354250627002800c140c2c55000500c225880b00912081e1400184010001d00d201004020710b040380343c1411b1741c0d9072500054058042030042c03101d582e840300f002490a00d49100702019031409806031518a0000e0795452050516442007100602c101100c40383e060343c0c08200161117080c1c06004a10280c003101030240945a001e001d0b03071501500030b00c3d07034001580e0190541c1d50000c110308010541e070306d40d0780 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 681765926 1250 681764676 681764723
    0x2130b07020f10200106170d09050108270c0a08150a150f0b03010905070504060f0e04020c120712020109080d0b0f060d1b020105010503100b03030d0e07030c0602010b010c 75
    0x3110000300700c1070004e000d10031a07040d449501145e00350311303220740100d0070038403d00d0726041204032240204101c844141300039486607034100c0d404421828001098a1840740e1000782c3c0d400d400b00c2120726400740d001003459003002140c20000346501c0e0020b082400b50201451442c8200900f50140c403075603001c90001500016240000510b02c3d6601c0e03070122600ca00000c0555802400b0b208603190a040101c6c20180c4a032080f2403c07948079940d40141c8242403042250315035160542594425000d1025074140d035824001c08142d603a40098860b070f54102c0b440d054440900f074402c0501564903100012010403800001c498805040060010710f1040d0308001400703074140042e11540059002c105a64030f089140c0c0b000c800b250032101e4103411038021401c12401c4c0c0300240502d41e01a009010070032001d2002d50010929100000d06803810003031091841c030f040b90000420b02001d0750100710100148501e03407986c54098030f00b41c4000e000103160540003030880c03c1050001401082e8054042c0070444522 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 681767176 1250 681765926 681765947
    0x6060f050a05130302090c0a0314070e01050306130203360a03080c0d110307080f040c1e05040e15011d150102010f050c041d04020d031808030a020102130b07020f10 72
    0x14202c240c0e0b414003510310071590f040060184040791806d00f69040e409680d8440500c10320080d45c400333048011207001120680c0000e8401608000c50750880f031080d0000340091442000b221520103a001c102245441c0d48903a0240e42e00104420801343d03500809002c1150b150907601420440f40c25180c0a624211600c00c52104401c00b610b040480007404040c01d0041d80294000c0d91802c04070385424618006c0402e05950003454000000070401c00344030703003c0001c1d601580c400f0020a0555656020406603248058a21a0f40c2c100600843e603c0307408541041c0500002c0708410f0408050b039050000050300a0300c0e076030002c400700b0303d0b50070aa8403d4010030843c007840441804981805554046d50340c00c00d006401d054030711107040c00100b5040300c07a01e41c8a140c00918000550955850a0f40c41548000070b480403503c0700900801d0421041006040002c802e60005a171241040f4072646446816041103c68840800852015a403020322091500300e080300c08450301c07422407200340d5404904 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 681768426 1250 681767176 681767179
    0x9020a020703084608060103090515070f020d020a06150b0a08090f01020a17070915050c01110702030a11010e0d1a0606030412110c040212070306060f050a05130302 72
    0x60503402d81004101a580b081d82e1400703410248821a071855180b5550f81c002a441d0213024503403103035650300c103100154021300113040001d054055500c4960502092a074654001345090f010b010a4661100d081711552001d4800382c03244224a0400070b4940c2d01c500001b500761500c414007100b0f07809814084c0001400c5051034a0303030700c6980316070107012a50110b95018060180c2e45a20079910418021107000800750b59850044000e41d40c40b00802d035801410400401c40144808144000c40203c0e404400f21540c8648c2d4031640b14140302c5007544d0b018681010842d109220303040050b100081c9400425500070a0030080b1000000104c1d82c401100501ca6030160880c04a078052180c0c4010060305a880140b05100c247c4d0f402c804d00070940310581f030042503030b10b120034108034540c802d0144042262040c3c00b907450703030602d860004040e40c12803694212100e9030b55051000c3c090b01441440d00a208505200400b0b00c82c085000e010303801010711010034002c0015103440b050b403401c0c041c00003542d030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 681769676 1250 681768426 681768443
    0xb03121309060612110c071e09180c0501210c030e01060b0a030609021e030907090911191a1e0c0102070b1f0614070b0a0b0f0d0c09020a020703 63
    0x66818000b40b81c101300402040001e8a4450095146003904c02282e084a44010080482c00e1402c009440190303032a04402408201340340005c5400c19450107001003c2d82c20030018510031207070341820b80707580010b5400103040c070a406503081800b00c0712030801081d4080350800060300040750b500543c043c00c035056452029510300500812410070010191149510302d42d0304114680e00c841140040344106486c504c2c0e1f207905090300c5c0710080560070003107501c01400b50076146400c0d0350700301d10802d0b1070199070211410724040e0340851490400c0800344082c401200c964550552404c003d040140b504580303450340405000501d400345c94102c1c11115030040c013003600c1540c1d411160084034000d401034103040351030940c0b0341c000c9082440c5005060100004042c090a030940c41c214054800b402c0c0304885400020003800200003051450858a120b1080d0220104180825100b0480c42d10343c030070071180c441c15030820804045030114506c507050391840394005aa030021950243c0c5001c138a0b0303000901016 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 681770926 1250 681769676 681769679
    0x8031215030109122303010b0304120c050d121a1813020d0605070e011d01031503080706050601090801090309030b090304030f03020c090a0c05071101051306020f0d030b0312130906 79
    0x50344030b01e07420301c52812580c0302c4281031a03100807085c0e10721003882942c00302c4109002003000f05940880c07503006101d007402d101e40c1c2d00f07840d562203c4c20031000c0e82828001c1385821003458204007003406020100001d41c001c6064100071030000410303403000001c0800c44030340c99000140101c017445088150f078580080c0172882c900700e549000c001504080712010000f99011440f0552035000f0b0320400c04c2000f488800104000c60f200c0110003c0078054001146c6110352403001021844650003001c0041c01040041200d1803c0400503001d07000da40d000368150fa2500000d0b00120354400c0d1640d0650f6444840d001c1d07203440c3c50203420300c0c44c020b5803c05481c80403a601003c0400d60005800c920019040d03035200780d965078005014086594201c1c840e00483c400b04202c800091000343c0381b241a03441414804c0c20040508032150880d5000d03082240540e01881c00d07944001820448003103c1042d51500b170191929107800b0070380303e0705050801000e0001c081200000c2c1b103805110301d40a0300048200b080703010f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 681772176 1250 681770926 681770963
    0x40c0b090319150e100f0504021f140703030b03060f1b03091e16080604020d030305060d0804090609050c0f0702061c020d2403030e0105070809060d0c0908031215030109 74
    0x170101100314120032484c1c60802e00888049006442c80f55800800103044001040130f09483c4001140840c1d04100d40300f106d12880d911500050a0300b240290740c0080e002c0c0d0860240341c5410400352080d0303117101c500300422041a10031400356000400701000180c0329102c2c521075500d089074400100d1206403c1c000103191304180080c02030507082000b081c0020f4542d42e42120746c0c443d0020350740a0340240d88941c804002c05d010b60026500001d018008001040c11a04d80a40c15000741c1c0000c6a695202c2404019180d0300d4060186c214442265903840d05001c20b07d072810910078014000d008080205100c00302124200c1071100689440105551356050001100700401c0881411048090304080c0a070f807140ca12102d4600b66545919820050740c4000015241030300f1110781121070400411040150b51034500151030000c0502d42c1c0400d8001c0030403006450703510140c002040caa401448000903214000e0703422904500000e0703800c6200d850413000b1038007400d01c0503030291404100301c542c2c1203117 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 681773426 1250 681772176 681772183
    0x150e130f110f0c061311120a050708100b06160209061c0c15020d020606042705071a070b160c210809070e0610050c07090203040c0b090319150e 63
    0x4003040609540c0c29580b501c281d5031000040503409001280c8000707060f4858107140862107c60707140c1743c00719511059296101490440550040d03200c5070002e00319505010f1060241c2d84c8180c804a03421400d0550500d40964012042e0201902c01d4101d07a0115036a0384641c0c01c1c0050300c00600002e0340c4001c0c00c90400c60000000307480b0b51641c504582510012991010501188010f0303140c0c0501010384035070003000b002d0294001c4502d1102001002c001c15000c404a400507040d219802a0100500d49038883c166907603220f4510b0407410b01002074100280102c800294000400e4001c00e00343d1b17607a04802c8441101c09640101183d5080405c039080751007801072641c00310000e0351600915070342c000071503468248922032014001c1021010402c9031410704540b000c0c0101030302d082070411801101562803c2c016500c1405142d90005c00e01042c0407140c04a075002d440c0c240c05051806c1281c1c00130a658040c00c15000d1250316511503007100308100380181c0405000140c20907c170f44507098407040e45 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 681774676 1250 681773426 681773437
    0x50c030403030207030218190e01020903030a091509080601060f05160305070213020c070902160602041502060606180f040e030a0207060e0f0904120c0b07050301150e130f110f 77
    0xc1181c0c0c840d0a8000c00d282000c02c10b1003040c0d03001d000103145690484040107443c9030310486012b55000d0210101646003003016200c1120280e4034160041e1a0004140064840c2523542c1c0c100441210705105103000000c403103044078480d2034501c7c9130608002c4100c94500459903218540d11900d04540c1c18142e211019106090080703e680c840030781d000c0220b404911502100d4441070b00010010401c50305140d003c2c040c0030413402d0304801c4103103060352140100e0744990001010a224503882118242c2d040105035070142c41528035600d4019070ba05038821303501d1a000114841c0c0e62940100c3d0b850307103c03900600a626200000c80f61641c40c1000065222540d80c080c0c80c0005440c102e10700309500e00900400d0010341c0c0900840344984840c0c03280c0c82140d07800302c03080051211041242000601085003948030342c00070796825880754104907034008036441c0180242c0c1004480301d10141540e0b251071040c1c00d19607d2000020f0840754036204c01014080034001d842c40d4102c04a00b4044c0000d80c0c000514 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 681775926 1250 681774676 681774679
    0x309060b032b0302120c071401020f0405041d100e101b052808070314060a1401110312070905030303070c0f14010c0e1f1e050c0304030302070302 64
    0x48884503680600d41e0325402c51950808101002c40d41d0b0340318003445000b042c81e5285a107005031420307001004050340d0300b0303094030549000d29000940ca414082205c1422035500300d40c1c00250710b000400d41c451400c034003ea0003864490f81d9111a001c1101410000083d0100c1034001502c01c0780d110508000010540003070b5807003450055501d2a54444040e100340d681000380105200c8421840382001ca40030f41084402e02500d000c0101c50401c0e101104001650070040c56894806501d0326001c010151142d18542000d0909444144602907076a1251202070346d203021007190800b480c3d034004031070070302180c0d46008060100161a60f811070202c01c00600c00e52442d250001a140d8a41c14180d8a00c4119070010004403080d03142000640d10180795101d41d0f000c0c4540311500700e4004180c5007155406070441021a8084100c4841802c01500141204014442c0d00e00442d01d071441c06440b0f03060b001c5100e0b0f40411000c189404407030254007500c5065000340d0490744c481c0d84900c0c1c0030355500481d000c1607 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 681777176 1250 681775926 681775931
    0x20f01090308250b1e010b090112050702030c07141302070827100e030705060301030c0e130204020a1206080c0307181b0807020f03091c050c0919050f01122010030906 73
    0x100d0031f83d0b968011140388031010b03510307948071100c0940000005d01c4064010401c6000400c8a211041010480700016001000090555007802d80800c004542c0d90b1514121186c0184640d10201d0801c0d003d545900b81d924807a03081420045420144401850a44030303403080450f4000c49046520a414000020082d012194150384480c1086810301007448000e01100c5039038400e00100340c1101010b900601581070228691010754001b07810398000242d690000380011907900c800030054020300005084540240c43c0c411001070110340c4a144d14010560b5030186854244c602001c40d502009042010f14030b8036071840301d0004003c0c03442100782c0d03041c1c0041c8a00c800c15200084048121307020007800030048500f034408840c0c103203800c01c144002680c1c40c1c040e6504e182a25261020200d10500a40111600300300114241e4422500054060389642c20f80304e0060041d07002190310b5450186d0050700400072800c00766440119640c0b1504410781120350015040800c9030135400c1004014811a0306 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 681778426 1250 681777176 681777179
    0x402030c1f031d0c010f020f0a080306010305060f010f0513090c02070816121103100f060501140c0d0513090609050f090a261312020f01090308250b1e01 67
    0x600801004554403083e5400c00c5007041c29544c000c840c0017140446d240140c880468414102c641411902c107001e1b1500e40d00002000a07079070b0f042c4115944440211800211800c00600080c0800b9981d4000800c6c420000b0341c1881122030080e068000b03011204007800144400c103402034480c0c285104205641c0310701552100c004003011b0000040d00d19004d0a29811000d075207d10005080504420f90140200c54409101b95098003c86161294120000c10598980b5000500341984c84582e00f1000c502800305504001d8041a2646240303050311301181c80710011141403011009a5000d10f030660700e460000189030101d900014810a0141d480c1452070341c540f0a115200d0340301e070342c00400c00c5030440322102030050800d60500071458002c114600f410f003d074441030f0b84800542c0141e1683c0e602c04501d1811071602d029018100300c3c0a1070403000c80c0f880c5580703281d128010081d00c5400740100d1811541d20801c601d0040083c0303038010f48e0036440c13402d1100d504011081c01003002c0c24607101f505c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 681779676 1250 681778426 681778451
    0x7050c1905010b2d060a0c021008011505040803030105040b0109150207061d100f0e0307060203070203100c050313020319030e04050106030507020c0904060e150f0f0114090402030c1f03 81
    0x2c038072990000300c150200a801c0d000300001130340421140320031f001005105a003da1602028021501c4c0f0319201c0e007150794144525960185074106543c42049020001800314600c0401681d0448000390760101e100c102110041c1c41610b101c0d00f0100c80812070202041d101c2c0d40c00034490742185c2c40c03600c5040f0b91341e008103031044918020340500354105007041c0f0701801c00c0f441013910300c07800da0a034039200705140c0303060300024200056039200400503400030440d6010340c41c0c28000100d01481442c0100100e200d00d00014042d0b00000301003510494041c5400e005644080c441000d802604003c8400321000c0c41c6009065802e044004501a514000011a44502a1040601a11898004148101c542030030801d500314001d100301c582e01e880344452400740e04100f040c042c03031018000303040c03126140c030100b07212700325a0013050303000c0c29003840e40104812401059441001c4405071000303401540c0d41d002081c58101044c0708a504003003000d4a50b04c500c1d400c01d401c280100350b1984d05020840d00c000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 681780926 1250 681779676 681779719
    0x801060609050904021906270501020c1c30080907120519290c03060d2303040f0608150907021203070206040c05030d0807050c1905010b 60
    0x204400314820709818000c501e8011220396009200030032103004143c42e21103201000c0b07429070041005c649000c02051010040800320100700c00c4c0e1819400d5920301d0400000e643ea80d40d260350900900326600c0c064030055602c48032181b46a08103131800702048071202c2c4100d1004d60758a04640c580c1c51440a90741880c13154003a20b020701a040000c1c2800b609200311002589840c0c03008851900c1180c410a190800c484400750b030700c50199035036160701e0a5030300d031400b0180000c03104441c0030280c0b41c08003c440014138050720380219090301d6400b024040c40c0752808152040c80c0d100d030601000510035019800300000108140c0c0d4a103005504100d81d2468103643c4c0e41c000b0340d41c10084649a80b2224414248801443da0081c402d00c100c40d0607910814207008107500940b010801178101400300024000001c013444010702c5c0c107030010864116802d030300030020807020700000c080110010342c859001c24100020407080c00242410306e400503e61070800c0c020b110000b0f10b540200c1c1e03000e00e801e02c000b4080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 681782176 1250 681780926 681780929
    0x20a12150c1e0329061b01050a11040e0c07060209040e0c01120b150901050f0d0e061b0304020f1909020c0607091d06030325020102010b0301020a0c020f06070605090303010f080106 79
    0x40000c0da54082800802080d00d41010134107034004070140403940c02400c010040c403080201c0700b4000106801c01c0c22491047d00c1100381130102c07504040008000031511040d07038aa110321715040b9542c5800b03d926104c0041e1140e440c406a010f410210700800c20301c400300b109664200d0076203a440307503240903440391004d4901030300001c2e0380440c3d54210882840c003410000d0800760014500300d85031075070780820090260402800440c80c1a900c40c1c02c040d03182ea01300030b8a90401c9111880700740c020741242aa59003848000c000a0080f444d03440301140340d889189040794180cc15400e607500c0c1a4991800c80025006140c001c0c18038812500440d00c0d0b60b006464102c2030380c441c461003a1585400d00780e80c4000540241108c1d401d440f082000941188400000b6104074507052070301e540c003240038000282507a00305054140708e40d2041042852440e0400081d2204580c1980c941d0038003400c8070b001804901402d107001c1c0c0054141400c1204184000c002141661740140540c142c03140c60313001150072103019 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 681783426 1250 681782176 681782201
    0xf062c06120a0b09160b0a0e091005060d0f110705010b040e06040b07090b070c0501030506220b030124060206070e0d20030a0c080d0804020a12150c1e03 67
    0x81100c00045000c803486280c0c07006100c0b0441c2e60706107041c001c0701071581705a4080c802c0f50b04045040d040080d1b00018200303051200b114100040d0808002c0c0c3d80c000f4815200d01d502c9207100255220104125411009801800d84010009000f402000c1680c542c411070381114554a08480b24459103458410716450400c40c20040000c2d80c0ca56171001e444a40150001080c0981c0e0301002031041c81d00c40c020122a445050303924a01031901001500f034035001b400321480340e44c50038600540c0381e40510080c1d0202008180101d441c0100801090041c005c541c1c0e803065800d51901800c901d020581d000800b100c500e54211012641c0701c0500710b4401c88503e5140e58010000000c034030101e0030302c82200407503015100300c5801c1c080d00140001e00d8801d14800c00c9407514607003c0c04000280c010300c50000000200c0c101a4424030f001c1d030000704100e40c5d502801d01c4403011a038091044c8261039102000c00a5011030411200b0f010032000703880030410707000990344a50003840101540d4400e02130315450242 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 681784676 1250 681783426 681783433
    0x90d110102070f030f11011a10020c011211040f0906050f09010308031302040b03160e01080106050d26040305060f161e0e04020403060209030f0708030d0f062c0612 72
    0x703030380c0d40855075211720310455000c2141d400408504010300b03109507079450540650040c0c41c035a6120a20404100c4c0300c1e20042550000e013010025643c102e610324900342e41148000860900049204005000b280c0221a84502044012900842d50342c4042c09849048881041d44148002007111449090200400180c0f082c00442c0704141015401e452442c4010000f041e07200450000c0b03403414622a02a441e91407013180d040010708100c010b414050140d4a000f402020700340804140d030824400c070010000b03004000f81e030140240090710380c00c81c000c207800d109075516034a00f00702341d88a1003601c041c608400e456003c624510100d00200e010b4041c00e484000080039200e103c1703c82d40311300382d5491090244401041c1c8283d87c40d403001f40050751054100507244c83c05401031600d804110200343d416a442103a080c40340510002c1034402050480d507001c180c010003410040042c1800f0303441003c03d00d0b100200c031056416203101d4440c07000003807649880b60f5a02c00d81000b01c01c400d944644d4034030340c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 681785926 1250 681784676 681784703
    0x8030316030e010f020d0207060c021b190f030302070306050106180308030414030d02040e090a030503010b03190924110a0c02030c0a0806181c030e0c09090d11010207 73
    0x50280c0c109091a4010328000508400385240d00344c01d980c0240c0f000680c00d40c2c00604001081483d101e4005c0260040c030050508001c0c4800d0390001e040524030540c07161042402d40901e2140c1119940c025151170b040c0803054903620300c0c0180d510661400200e9229003003000200b5008e1240812411880d00804407100c000d10b1600c9810160b4400381c400c1e2081a10740c1c4034510001000c0001745440100a000182d40c2d51400c83c00d2000c4003400790803c0b0041d0010740120020907480801d613415500080c4c5000e070f60792034002011050081c982090400641407049c0103040c00403180b00b0140c03030034507104030607504840400c14108076428920b08000c540d109200ca000f070b061040d030b048500e0a101400729866010103400051400216074010070382d1380c0c069002c01085a0360346600c1c2e4849401c2c20010211908402c051070507001c8007039410010142d440d6840d20310180c1c03c100d10485d200c401b4040005e5405d000091544403110411201e01142007003508070202c01052003180c01c1d40b900800310b0924032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 681787176 1250 681785926 681785971
    0x19230a150201020d0507050405030c01030e030904022a030304031205070915021014160f050304060b0a24080618190b030607090501030516170603030c030c0610080303 73
    0x824110000046641c04d00102d040d40c400e510549000d0207594644980780e91030002010700d003000d0800c00030704045c24100d000d0710114000040e216421821503003d84c988000f16005030301d81c1c1c6503110401041c2c60400f90903441402c0071000310701450081e074503000c07001070404010043e070314151b07241c0f0001a80140c0401021030035002d00e0440760044d2044d12400c81030140c203003040e21610f640e42d03c0e40d1840e4030240003115009210b200380b841054107086000740d25182001d04280401003010307003100e4948188510980e07491803c44090502c0503c501480d01000141000310084002c01e100482c9030000030422610340f0341005030410940800c3c0d0f018680d0340c070f245111803503012403200410b2603d1f80c0240c55540d03000c4c0007a52048000ba9102072030349142034001020348002501440151009596140226034810405210304020340005c10558882502281c42e611030020b00c03886500000c280f2090041001c40c64034003401c560300c0d102500740c1d11403100743d48906c4103a43d100d01da030310305584220f02c0d0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 681788426 1250 681787176 681787199
    0x303020d0b0a1d0a24080c01020a020d080c1507020312101a0c10060b030a0b090f04140f0106091d12091e03010207030818070506250219230a 62
    0xc554a50800700790707620b84d144601c1000901175801c503d0300322143c00c244240801048a410303510f03170910052007080f060741c01040114440003006050801d001881c0c01c44480100302c0744148844c2e55510f0001ca20b40b03110001d40325045410235851012445c00400d050174080c00c0044152703100c034580503900e4195080c1c0092550f004142d5403865018410301007240304064403500004026018403660380e881c04000d2007040b9403030b403809188200c1c4240c0500299042c00c0701c0705030380b10b580994001c21804044008614001a8080d250180c2d03080490201c1c3c05107142c2c00000850007960307001101c0f12601160b540d103943c40c541d21a641c15101f44102e00c110324100002c04120a20806c841484000081c003203400e80e84210010b90104408006111410410182130180c80818201070f02d0064200300000f1b200344104882c1d091030040c1e10030650301840c2c4d644401c0d181654010018107041ca441081c1c40d6040e14184109e0071411800d420071480850718140e01210748200501c41c10300c075030400000740b96 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 681789676 1250 681788426 681788431
    0x1b03090f0c1707060f02030f160b0a020c010b060c100c0512040b0f01050d020a05040203061201050f0103050c030636010f0e2503020f1c0303020d0b0a1d 67
    0x30a1840e00c000c80020030700da00c800078050301c440540341045541446007940740005503070040082107001c10300c03501055400700540f8100303030784034414543d5140d2244220b0f405060954000e0160454402403021080095005103454000440240b03d40c0c01020700700030290144150f41c104541110590b0404500c6660044584a486062280c182207c201c1181c2c000c2d4011602114442c4800d000e00150380002d01090380108800c90b403c0c001450309601042403840c1b20300c00c1901994000c00807409980d80d00c400040c840c100840200040e1425020300c6000620a00c0203481c0760250161000e85800c001c41c15030b105136221840743c1c41d15402d012800600320101e1004038a0506481c4c20310b0340110702800b45c442003906400000c80d800f24400c03081400c0c01580ca00000c002e10510311400f0510849008480480c0d404445400c403c0c916040420084507a42090b1507100d1421f9a0b00010190903030701038481c081d2099000c100381600300c1c0502c0030f0078119001e00e0aa140c0e80c41240042c012030804d80c0f59 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 681790926 1250 681789676 681789683
    0xf0e03160b130b0a0204051c23190b01030b0f010308030c07061e05070f031b0e0607020a0b130914011230030e0606060a18050a14040f1b0309 62
    0x1c20800c501d45400c07451007801c0c0d444240765500080d08020038500054610034502385001550003c14a641c0c44280040743c5058180c1104520020100302c16800c1c44200e61850b0f200d10b03041a015010b14044100b01c0c000d00040303401215410118480115080c8000d059035800b4411a02e181c40d80040e10250f40c004034001c548283c1ca8100c01c0780c443d8480031525101c46c803000800318240c100800080c14640039a00d27036400b00b61070b1500081149001e92400c1c00b41e0300d100c1c00c00074401180440814200d00c80c0e0000650042005000003c0c1c2c0d500350001400c0a80110000308032164682404d4420399098003441c41c84500ca0b10f0041c009464039140a03620315108085d80300780c0c126522200c840000c1c166040084e6400705503c50420160180103099442c80344202503c980c0c600040000c0f11405031960340d0040043c44510303011240c040c112a0805000001d101c0280c2c266030b8560003540019102059000b60306040c00c904400b05103002d00500c07007500360744031021240074110440090403420004da = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 681792176 1250 681790926 681790951
    0x2030c0a050313020411040303020d02010e030901271e0602010204030302060105010e060c0d0914010801030c0e060621190e10020d0b0d0b10080a03080c030a0f0c030f0e03160b 77
    0x590042c0e446100d00906c10307440900041c1c0341c92035400c002e4100010350b101e41c1c0669040004c0c18402e01c80120490740303c01c5007400c1c060f00280140c1c2d148134102200c111140c8a01c1d83c1c543c8042861004800103040001d10300e01c42411003920703464220b00b03078010b0f440014056801500140b016600075141010500d001400880c1001041504030340f40800b01048013010545130001130180210b1598202020a000e091540542d403540e9a036490f0b89400c0e2240040861181c0082810ba54034a03080319030b10580c448402900c40f54030400d4100382041a030340d10001411a640c0d80f02c450301f190082c40d2100c00700f0405044c841004004c00c40c06980300c0e603140f80300c450b500c0140d07890555400b901c2d121401e0042100c40c10601d48040b02000c07070f10464000507a030b540701c0b4a00783c000035401803603e90700040d5050705c40d40307d031a9640c0302800340620782ca454207241c2c02c19200c41c080076495072200307007015482c0c0e00c140860803024030420b8032840307140c9000400614044000000c1342c0303840d00c41da402c07400b0040720 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 681793426 1250 681792176 681792211
    0xb0d0506270703080915070c0303030f060f141206281109090603070909060b0918031e04050a0b070203060f06010c0314120106090e0109020a12090f080a02010e0f0102030c0a0503 78
    0x1b8006558858441202d900d03001c0e15081c028103a040c1704409404403400d00810901d420b02600d80c0c2d100b040380c0308100c40c01c00c60f02e018111940340d005403d00101d17225070444583d400d1420321010308000005101079018034041c412803454245000c1d00c0036403240754943c0340c5460089030611a0b44000107006542601c0748040025904250348121890103007e4540050510f0b141810480146000340c00e000480c0703681800004848008011568100e03c00341c07405200018443d440d40c0b40f4011540074541c0708849540c00108080340354000c02000748200c00382d620a0b95118085003101805460190005221030962400a070003070310600c101c500414005030400341040c0f0811417140e001d03003000c0005043e01000700a840503112042d8050b02018205605040320b08900824a040c00303003440c2e440c0e60300c40001c40c00b0320014001d001d482030703003000345141c0d5800d492030084d0181100c00440050783c4a06200f080c6001e9061096038010003504135800e03d00580301c031084406400c0500040304420400c0c2e00c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 681794676 1250 681793426 681793459
    0x190b010e04030c051b1302120c03070c06021206100f0806060a03141302031203060d0b0411130b01090503070e0105060c0f070612060b120a0f0b0d05062707030809 71
    0x6180291000d0901c04982c00024400340300c0a4607071050410000f5006000c1c503200408c62074102c507480b654405c24162a5902c191085410001c00d042c040d0510b4030024400050004440102c0c0c481c900540340d80c20032944011003280c0c91000c555100d00002c0f010340102d590b51618000a110048840c0780105180e0a1004c0441e0080001d0b030b075071614502e00341c1c006c0d03046083c144410915440e130500500d055181403000301c0d560040001c4010305680307640c40010704004c810081005940e074054003102d05c002040480304010032a28145602041c40b14500080c3c42c6030015280d8203a074259050079400d0b0740f8240511000303030419035a4281c68000d005100104500400030003008045540e07612074514104040c8034103c4406421804640000b000b420b01000003100c50070b908002540400620039214482c001d0091000740030003540940d41d0f199070f0041c410300107004d030f004000940c2e01003a034295004c00c04d6080c5072000c0c4041890b4011070381c100042010b00f80505122100039121510007a00d00030b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 681795926 1250 681794676 681794683
    0x624050f0f0c1b010f08010b07080c16091a0307030209090a0b07090306051503030304021011010f1512020d082a1609050105060f090301060b0f0a02190b010e04030c05 73
    0x100c521456070701c107a260202d5504000a150f012000a00305080c4085000c0300040c94140c05014821240348001070010401800740203c0b500c0c007620b501030755961005124096021007142c07054245007820201102c0242000c4090090703502c000400520030145994240702c0603100013061807000d802070304c0d441c2c00440e403104440d40c401d56040e035440c0300240c2580340035005c40c1c0000c1e00a008070303203141009905a03140041100d0704903404907496003803003290480803074160340030700340e500c00a50801c040e0041d0617055030084185120320b800000e030500e48500a00310407840c8100069400710203100000c010034400c00c01003194034051040c0b0a0191310881c8900903011013200da40c030456000101c212005904414024040c3c42c004100307101e6949000009811401604210308a100f40055651500e607000d51141d80180300e107011281d1a840e500d154014030340c108034410805400b0340740c0011410300c0c0850302c42e0394290740059000056402c0c070108800c107000040017101402043c0303200700c01140b07040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 681797176 1250 681795926 681795937
    0x203060708040312090f140109060e010e1209060f0c01090b0124080c030105040f021606021308012a0203090d0b090f0c0904062406020105010302040624050f0f 70
    0x25107400005003881c1c40c0050946056448680030903140c0b040c2c280000301c0706000c070104103410806d10502e1243c0d4000c1680101b006010080840e0b14201110185e00b006400840c80340300c4001c1070310340706158100c104003140b18680321340c2d50144d0204005843c00e030040018115240401c000000c80b00c241c0d9440c031443c0c1000f03800250414440d0341d8030941c03c00d610343d01e017a10003855142846050038a00e03080306144c003040c00342c140f245444580c00f0b10021416030541c2c1c044880106005241c0e10503041500095003c0072000140080c10100030601a805000340f000020100c2c03410f140f40085e10f58680c580800f8036415800b140410072428500ea95180c034003680941c051079280d00281420450140741802100341c030f102940190720741c00b0b419680e5504c1d080c1e003d40c005031302040002c40300b05140c1c4482d214144c0c203014800410008180940c0c158011410b903442514100032058481550100007400c441c1e520008214204955640c1c521550103080d400d06120001c80c20b00028000c042640e4012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 681798426 1250 681797176 681797191
    0x1020c010501260d08060d0204051f081906090c0e04202b17040305061b0306030a110a050402042403020705070911070209010915060518010804020d020306 68
    0x1104018405104426180b000c0f21072040079403100c2e416060412501e032111050200240014503002038040e4031000010a8599401401000030f803904140303104109800c5540070080c2c610300c0902240490340000c071508101480e03c80d42c2030820981c1d503140d024081c2034200719803181038500005990b241d040c1c2058001c512031250751070a450600e0340c242c8804413a41c000c61040c51405c50703c089040075415010030769101406004000c00c054140300c0d0301c010743c030907174400040000500001070241c0415210b000301d002e07944c14015010303405c01e803800a000c143d45441c4e05401021440700000c0c0d8039404000700700e8015201d48035482d5118002800c90f08a984440366034004440003000c1d003a02c2d09000d0202210a04085091141c00e4603200d50356031680c01000c0c100c0c0d50340c0026511100c0030078117662000750b00603c800c825685a1318010b0240003102c0c8a0f02c5211000703000445d4090049007641c50310030032543ea4407a042039001c01151184000703001039070070090714000307023004d07071014030819115106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 681799676 1250 681798426 681798431
    0x30111120405150618150d140115030803060405191d0c0603011a1c0c0509190501021b040603080a050406090603090506041401021204051b060301031a0c0c01020c01 72
    0x406041160902900031000c0c00c0c0984154108480c1c2e03520800c1c000617030b000301107003084c0329900d641240040001290105910106c01c182002c2080b054503503c107011503c503070082c0b0100c0c0116904080c800518000205106018030010345241001c2c1d020306e5002c1a80c290f8206400f1071400404111b82460662032207028444696400e03052003002071540b450410f4900500c0c40d8074103107240d60b04100a548800c207010300002c079075200b143c0595109099120407002001500c400d1100604558000d4082c40e02030540c0581c29004240000004012a031042e0060700740100c1c4a085142c0f032081d0f09140f9944031755580c03408000304001c42c0207890300010546031b5a40d1582000006010420130341c0c4070740101401c0c10103280020f1801705a080e00f25a104107203004a5145182d040d000e805020b0041c01103902d000300300014000000f40440340c0150044009094150391000c0c090715102c01d01010b002c0d001c0c500c80502d09101e206108a902841c0c0420141c100780207440400d00b1381e40083d154011503034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 681800926 1250 681799676 681799681
    0x1202010e09010f0f0806010b0d150812071703090d030507020f03071a0f1b0a03110c0c01080a0b0604031e1a090d030603030f030507030b06120414070e011403011112 72
    0x130b40b0a41c00c0080d0000d440201901d41c501482509140702c0c1d03a110303203840b03900c43c042d4210000c0e40180001c0079100d0101a81c0c054182042102c2264101c40e1050f02e542030070a100c1c1c0c40d8440000d040781d0062b014003000c1e10707942502075000d901500002c1d005508621030381c01548191403062020303104c2944205150030120b4403c1c0c04034420f519004d008a50340503445001c0c41081c0d002140e9200320f5150621545454045203401507000745141490070a51603c001102c00c901500840d02c0300e81e2100076260703000a5160002a0b50848090003980d07500000c0030041400410050640c1c2e00c0c0c04040c031452000c3d9121141d82d51100e07170403010400340543d81142e060222500050040100d180c425240c06c000305071942c0c8008141035038464110040c140d444010038400c510a0b0030187c10001c1c00b4100c0c698604058140003102c01c002c480c2591003010865944d410341401040103402c4580c5000303101109c0c0d08008a0b08114140107511380da0642d82c0d40c83c40f1a03141d490340042c1800030100d403111161803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 681802176 1250 681800926 681800939
    0x70b04120e1309080d0203040303151a0403300807020706020303070918110f0702041401030506060919060f03020102190302060c071103060a0b0a0801050606041202010e09010f 77
    0x40c0c50324a00403040c80110300c20410261211001808606a440d0001c518a1007504000d0741074400e41004210032030001003004149500358124075030f4105901030504c4003980d940d440c80c1940f80c00342d4034150621b404110400201d0354010ba0411145a04020100b00014000c00301d40180700c11104000030038510000c00081d6034041c03160800500560000d07501c2d41c9881c003801401011540500b2084002d00200e80354501000d6000b00c00d204038401420b47c3e18440404441090703004000203d1249041803401021040100880790481c1d900c50020b2030386442d11010408210001000540300c41140d2810014084030340c0141c1004041404441c0c0206040d800028101100c04940320440b503c444c14050000f9800a0303103690066420704c1c201d0304e0722580e203400c600043e55003030000e03498800d035014030816a81941c4620043c4c1400c0300c00440b142c2e5548040c0d800c3c0e81d07007242d003903600c0103080c0020085e005282c07011680c0b15205240c00310300410110002600103000b0b801080020111080c01e0000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 681803426 1250 681802176 681802193
    0x503070f05031b01020a02060d0e060a0623060405010f020a170901141201260a05030408190b130c09020313060e1603140111040e06030705040626070b070b04 69
    0x40848403003050700e043c90220002c4d584a90041000b401501c0015200c40d0003010b41d4001403044a010007600c52509000100f20084e01c510f00400801660000144600030308203070105041c0e4030003901090402e4506001500ca01d407c0c08804400e40c002c4024a00005160540d185c40201002e040a42c039075580724001000450084111074000c002040000c0c03510614000070b40c111658a106800c4140004030804108854011002282e205100245d0104203000c00500190b541d484e040750050500980701480d1416a000e020300812640030110301107551001d0035015031030103040080c4e541c90391481e01c0070882e402103d90300c079140612038401080190314004c00c100246044010704442d00f0180d40315564200c5440000c00300910032400b030034011000c1d00469034441d5041c4010341c90b40e5903100308600400d4100d80c1da80c402d0080c608045403901d098400e20043c0c80d00f640702d074100c001d0005003800343d00280d20400122172007180000100020041e00a0030303098400c15406005040238504040c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 681804676 1250 681803426 681803443
    0x40602090603091b0406060c0f06020903030a030614010c08251205030702010f0e0709020c010b0a080a1b180e0a12090e061503280c0804140f07050f010201060503070f0503 75
    0x440d03418504200442a8000072107403550f03821120000040740c1c070f450920002d2084056137901400041040d0021a400d6403090044981300380250002285460044034060014000201000018402518015941510041c00c1c41c0c1254003014004c1c0311740c50310038880d10b09140800010740f00108000d010355080c000c07001e50740342440c0c05100000503203240319164042806442c20b05a408980640158000d400418803410060100e042e0300b03171a441880d4030307000b0340e4205480d4035081c0d40311410350250303010107a000ca9405040c1403504804420204001e484a00f03080c40c0710384901d00c4d68401140203845108200003a40d02c441c803a2904d010f08000074114000d0403184100304200c829511440c902044a0348040b26580c000e05401842c8000c06d000802c0e410104052840c00b1081042683c100701c1d024051402100703000148004000d200307913200047c1c0c604a1040c0c00a80040009040c80780760014401d005000104020307468078082480e0819a40c04030700c001001520400c903c1c1420300c100034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 681805926 1250 681804676 681804679
    0x50a300225050309040e010f09060b151305010e12160801110405300604110f0f0a05090601050c100902010f090303050a200a050a0506160806040203040602090603091b 73
    0x809a480c0c0b5150345407240215891540215241c01e0402c2c0040c40a600403004404030500800080026040450040c02c0c1c0030051401500410bc6072200c5d41c00f00302c140d03400311500c3e100130800581841d00464103112802d000d1500b00403003481c100211981071045414004600c0d007004081071803d1100c0d400d55140a10605140908220503c5161944c00b0742c81090604456900550b00f4106910001002561011800c6001d14003d000400000311188401c0003012030303ca0a15101400c1003001f00c58807005800c1e401030901c5000c02041c00c1142940b0340c4400305042060918400209007418402c10f00004d8481d41e5a40000f0000c540c2c100c420b49104100d00e01c1c20310086030a503070740907000344941060081440110204030014031203507264483c11456000503211400401c0c60055918030245008407001c2c092603002a0b03107200c42c0d08082c241c00300681d40d09001c03515120140300c025070000d0700c00e60324242c00b005080340580b244c3d0300460040d4601b130018800c4802c058440300300c60f84c07110f0605 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 681807176 1250 681805926 681805987
    0x20d0e011b021c390803150f0f010815040c0207081014010605070203030d060303020d17130803090c040603030203190203030f011e03120908010506030a03050a3002 72
    0x84004550040c200c0350340c6030070810407031003509030f0a1252100e51a00c4503d0700b1382a901100314020401e0542c050760040128440020038108100200b00d603079542c144100e5040090f5012060321980b01c0c1d5035158020f0038251401041d5561007012805a40307241010340c0140c0e200440810401c0383c208181e5041001802c01044403204034096036560a03410700c14502008030114800c01599001d0044420ba0bc10071001000015640d00d03010351114a056900c4001c0b48143d40e208d001100c004103c5449840104410784100d2410f0341d071000c0d0740d00090400c50191090750901c8001b80c40360722580002e1030283d0001c5071a10302c15081140192814407054007150400c0c0305201c00c2441c1080c0b014151584a2065911480280050039100b885540003a044064005001e422103800884240a40e6144002840070343d03030352014169a00040a40200050010468000210308c034000c0f400842c6e03000780c0c1c40600030701118062080502900707269041a0380c0060074500039003403a5040c1c0848600390806 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 681808426 1250 681807176 681807223
    0x40608130f0219050307230d021020060108010509101a010809031c0c02070905130b04021201020a1e180e100f0f030b2404020d0e011b02 60
    0x340c540080440314000e00451103049003840300c421002850300a41340240071034610b00d544100315900004802d0700b40390a01d644d04d00107180d5007482807203030b02c405802800a8114894592040700d80782000860741444060500d845100c440080c03125600910200c2d001181030f080070700d09541082d107a44110101c1c18a03214542d40484244e0700f00240100c824286810b882c0d48003641941580f1464070743d141c0c1030320701210146610310b6941c005013814040e6422a183c1039152251401140d074151081e09141503941e1844002a26041510754044e2010f800c40c1070342035103900c5143c2a6045580500007103070b412075100001070742542c980b241680880c5003095091003911421854089140500d400300f03648200020f080c2c0e948600d05a004100c0c0c03400c0c00e01115030300d8018000030025801300321104044817000c250a40d10001c000034141c081080c1011040c40d854003040000d50241c080d00f612540c650803003441d000030a00c0752490390080b400719060500703403050000b801d18103040c903800408400c142d40c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 681809676 1250 681808426 681808433
    0x50108010b190504050c0f030405070f0801090809040924020306040b040c120b0406080706021c050a08150d06020711100503070e1908070308040305010e1b010f032004060813 76
    0x2050b0100c035010b4800240d503480b04100303082580710340401c16040050010a00040100004840f811540c1a074082c0187c0d58a41052509880d04040050044501448110300e03516081d0710900c80244281d070b03030512000000d81200129810a1785844096902008000c1d903404e1038050303010b44101c00c440c1081124181c1d800941110009030300c41203100e68a00340780400303480d598070410243c451807081300c1803540e0b80c0100940c0d966010841203500c81201001805c200e01550a542081d0416241c000c91303956034020050140f800101410742c41100c5c00c01d1140030552610051003814000d17104450001e01c2c510520204841c000c0c11041000010400c00180aa00c42100c40200d0030481d08080b09000caa030405030355500c5504880054081c8800000030850048000d00c22a8861402449099049084607481301d44502c9600c0000041c1c2c0104100d561140500c80c000750ba080c1000070b00c0300c0040342c00f070390b01045406c8034510048000030b043c030405412402c032079480204480400003180040e90f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 681810926 1250 681809676 681809719
    0x708070f050f0d0303052a0409110406090b0c010f02040e16210218060c010209011106070e12191515120b0601091505120f070818010f020c01050108010b 67
    0x74090101686d94001c0f80716101c1d01d2000118858004e100456a1a41201d0010300380e03002d84142c1079441e00d8402500090181c08069a040b40c520341c0b262030401c5d140c500b50384015400403500324801e560b00c07034117a44000441d00c00340c0b02a000e066950441480c1400c1821100c0581c6103000701400020200030303180890805200d20442c16403000980c89100e00c8504061500c3c18400d07055100501103650800b50300c0540c06041958426a2100015081085269103804080c3d4407200010503864803030100e810000000012034401c0340841d914a5411484030200104415044800030710300c10000a844580d07006003101440a0310160314403a107441000c2c681c43d031a030031004280340c240d100080c606a0080e00040e0003000406204544080d0121008000303501204040c0701000050021414081c07014404507c107003500c3c1c0b80c20880e915804030402c040c089130084400551340360300201c1000f02c010b001401e80c050750803001280a506086031700e800e5644038000a0f0241d00c20a0482c0404c070b101d00e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 681812176 1250 681810926 681810949
    0x10603030f030219260112020108010512210909100302120f03030412090302060d06031203111b120705060405010f021306050906070605090a060e0609031e0405030708070f050f 77
    0x81c20514050001e0000e080a2480500034118010f6091000001d44d900e0100c0840c0c1f065100740d03103800081e0b0303d840030850041102c40011625078015200b40c0c6003070010700e526242e1004003200c070300d050080101c0082d100d00c104490702c0b944984202030800460074a06104030440141c10301820141c00652013041e6a80801800603010740080e0720003204040c010f0003e08080d5401910b220303500ea00304203040300540f901d44421561851100740c01100e040c8a0f01c211050508621825841c00381d01c0c114010b81c8030051800080e030b500940361004120304491000381001c1d84074001410452410303082240c00c48502c0c00020306180c0c0108451414070900700901003c0d0392007410065200c2c1080c001040050250010061a043c50001480140c0d0400035458079142c0c403603c4c0034080d02c0403071f60780c080d2034071400d4039111002d80c0706000030307642040102c82ca1040d040c0412000380c24596500c0000e0301d040b609902c8020310fa0454178043c071442e0401800b42d000f03050141c4500c020400020041580300d59003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 681813426 1250 681812176 681812227
    0x1140f01051c060204030b1303120204051012140a0b19030c051002120304030e0f040b1c02040b04050a0b150403210e0d0605060103061d010e180d02010603030f0302 72
    0x82203142010080f49034156409141c204201a0f410f103001e900d004180f0b040581d041c0e01203094545500c0450342103008171070698801a042150320207811105858204c01e10750600003003601c80007101c1400200703108591103150071100100e008443c8900340040807102807151001451040418408105008248070460b44191100e021074103800c40103d040c01036280c0b4900e0405000014003090540c805043c607840001210080e58441c2a001004115101841c1c0d098111000c024824240c0c07514241c180003603400680080b5180f01e07454000b404580084410740c41003581d60000c01170710300300400400601d0100352101c9281a05684400c0d41d03081400099a00c080c10b003411036028030344503104440320301d0f4000c0c3c85041050807600d0002c024040032107115001030719006000400611f245001503a200000c0345c4400c46034200314000110304001019845070803881011299081010410200300e00c985600001d0303405c0c21031270000c12501c00f00750f0003810580180000300c0884110b44100aa0090 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 681814676 1250 681813426 681813469
    0xb03010e040819020a0c06080601020709180c090e06090f1002071103161505040303140c2103040b0f0f1314100204210803071404050a0801140f0105 65
    0x755481c108601d03108002d000310446012070b201ca140c15400045003040c0b540708010480c2c03a90381f105030072111200220748503801a4440c62041200c4070284c2d0000c5d84050080c000101ca0303000a89600f4038100a81c2e21809203079607500145c1040e410300307118254011200f48060030244883e889904d603148084a01c40001039800200d607010042121020b00a0843c080c050701c0300c00c004400d6035101903001d8860035410352081e2219042e071a00c258122001d0760f51648410602d80900e261400142e0080b040d03040b02840b0fa003484021001100c4100403003461484046035807071030941b40041e0442d03070262030b00d0038182000741807002e00400c0011181d44a29007001d814080c03a51420300700c00c0684401d42c0c4803014000d00b4291919203c13190000c00903120101004041e580030341c1103088200c060030704003624007041800810b40c850f1089502d40000607145491904064898000441e401055844010307140c0d9030f40070307190402d814460365a900402c1c103c407851056140c180843c602440340d503400c6c007500d01d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 681815926 1250 681814676 681814681
    0x91006061205220b04030f0305070906050c0309062703071805060a0b03131703070801060f0201020c030a0804030e010e0a090e012307091703090402071e060f150b03010e 74
    0xb2600b0070f90040121000036418584042e800c0c603035885102614140c2c0010490030304203140c28000d016103400340d40d0340d0340c0301c01c6450310313108d01284d560b00075850300c8015000801014078290b46803c050820f0700b45281c0c1074030201040e0407101840d08100e0405a00a07001480e0402c24410f040345840303070224118602040994a041c009001031410340c1110300700d82c0020060102091a048a040c503061080b80980b01740c0500c04583c0b041404101c40000000d1031103001804068418040d40700f00d00700600016091144200030301c0d007181c002211820003c0c200c002004241540481300d111510003e0905649040444011030050402ca004010360180c6032510010315040961081c0d40785100c51401d2050041042c604030801002500c481001804101c000b10301d03030403000c4600215002190085203800c1000c000d12019410120007550f08007041d001140421b80034112019515101e5000040c0c80c3d586503103450100c80030302e4441010003d0240b020b004820401c8100c80c1500c210101018895 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 681817176 1250 681815926 681815941
    0x9030f010c0f270e06040c03050f060f0a030c03050a0309140f040b2e020601170601121403070b061c0302121b030703020c03010507110d0804051212091006061205 71
    0xc074443c05001c10035004001000589484251103203005900440e01032060943c0c1040c1101622010b561911400403030501041c2d05180607140140c4910010704040402c5d50b030303501d40032210782c001c1d8819619600312216204c101a400610180a4030202e00c0c400c9900d081e01c4040b8070008082c11140d40950b43e50320000c00190740e07410021258001c01c003424038502c040a10760207000c41071102c040025200e00400807030b03800401d1800801d6040302c68014040b0760700e003a011210110f500c90050340c04821540116a05103020300003002101e00800341c5040504103074061107004503072500c19103c91501e0000c080002507000c00c91408074000d40031002e8845010300c00003c0c140503419203036501403000240c0b01c002c242c1c000c50041d200a800320020030459580400c20350f40c3ca040380c10460400d411100d4028a1f0900031009507410501a0b01195003d0618444991030399000407070300c200d015504420014055802c1040341039465403141c051220924183d80500004018840507d805445c1c80000d40c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 681818426 1250 681817176 681817217
    0x5091009140703030306140102030306011202030c19030902011103090102030a2016140a050f06181c020306010b180d0305070605040605011706060105040918020d0809030f010c0f 78
    0x214401c03800307403008180e81c0d140140042c0036a201d10f40301000c10044200c000d60001c0141e903c5a9410703161084407050041a00f8020346c8010816203894a040c000341c440345403541b6021800380202d4400144885081c0000341400b41608000d1303e06604c10810f00c00d15981c0170041d203000d4041424805040d403d010060000005400c04580e039922515550380f80400e04076014034216003140780182d403000b00a01c01d001e030218a070b0040301d400903041e0844101500f09031004041c907200c4504045c0104da08200041d20441d11502020500c7c820041401c096280501109006000e451540c070314188d045007000e0051510814602d1041511104000c10b00d4000c0b012500702d10b5126004202c2c0e0716240c641280105420b00a83c200010b04450114919400041c81c41c098201611b0701e604141c0740c94a07190261800a110360750f62481c100c094001030700ea00d008200c2da94460f00b16141c9894400e01030503d008d00e008035001c070307a0f818504d0b50007031240c08c1050321a419005140102555034102041d508 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 681819676 1250 681818426 681818453
    0x11d0d0c031709010912030b0609131508010617010b130905030f071a060f0d060b040e03030a06060f0206010f180905031204120314010e042306060306010905091009 72
    0x2c9042601000950070040d400580014070642a2a05122a40e007049003100c0001d0f1419400c1101000415814a8154101c0142c200d4610003c43c050b6403825403070791840007030303440f0200d169144c0f5410320210103a0b40200b11080c851500030807600c020940041ca5461800002a43c0d4695480b40c1d00d041c4401031085480116520400710360355032181c90701d8600b1100309080e1046103010384010400e64a04a1810041450300038810010b0450a458910061645c2008280c0c029075074485641b08800c240003a40c0308880c6282c001410920300302c000b500843c41c0440440454010100600601c20101c1301401a194105181c564a01008840c84002c081b8210003905500c00414030101000b820400700348518402d40e061041d520b481082070702a1100341780071010100002c801032200c10303482c000d550f9200d40518030000266403842800b1403041e810309030380092a00402e04000705410304120700740c010b10302031100f040301e413030b200c007082d6150a0900b06480109072101d00034014001840c43c0c009 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 681820926 1250 681819676 681819707
    0x60b07080910050f1201050901050a03030f03110d0f0f11070b01030308060d0c080a031808030405090c040f060203071412070b090109060606020309040f0e120717040b0903011d0d0c03 80
    0xa030b4030800d69000d654445c4007480340703512400c00c250002c170340f906203511540c0880781c0c10b4681c280350b603060070700035800781030060b2500700b44903014081c0b43e000d40c042e40582020100d111500080340900c2050b18415a1401d18154800704030070490030000428140c1c40b20304480c0c040c944140241c4403400060020724800ca400385c80d250b141c030b03004102e181010030480e160600c40e40302d01c0c0c2c0118440d0010002e485403407103042c0305601705110030081c600b0300d00c0e041540041540c841c503180540b5901d0480703050401d50031581c01640007080201c00c101340040c00405c0081c000004001017403140d51a07406900c40d02800a28000202011030a444025000a89110f034840c00038048140c403518000d64075003101305070350f100b05e0410006030b281c3c1846128003034036011624090040c40c0c002e82d0350840f280e4030441d01100d4898540c21400c815145c070703034003500c042d2030b40a04450b41e4903001010142075885480841380c20001c217400210761280001507000303240c00a400d050303100000c0b0b0306080c0c500840361080720 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 681822176 1250 681820926 681820957
    0x6080c0118030b1005040518030a0309110301090302070e010b0c07150e0d150c0c02030c0907110303071806020f0d031125030216030b0c07060f0f0e01060b0708091005 73
    0x2a60407240c01d4144d041d2402a201001140c3d14961104454501c08904090b0383d0010058500254403d810200d19540900300f040744c9080c0c4800400d00b101c00300001680140c02490052207400b2030491598010070084170304c1420140902016500d0398120311a20300c40350f8941e1041c100e000e001d904001040c0c80c2c024000c1c952881642403e40346802c0c0c4c3d140c0070300320714a000340442c95a0300410320a0706140c1c0290050844d40d03512414400100405080c000034404101c070569620344042000350f2240400344d5038080101004007452000346100c1e0489429500001562076491b8000a001480d4012a241c0800d0044903050001058426840d1026140303100c4440b0780c0004e000f510b40d1010303843c469402c440e84444903d2064104400f50302009040310807900c0429042d0803000d002c1d0042d80d01030003001581701d00510a40303045030002400b4114540c4c90303180303e1289203800c1c8181e000400400c0d5250780f13010045e641c0c0d00c00030320516000314419101d940c80b0785029417282c0c00791089500da00b84503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 681823426 1250 681822176 681822181
    0x109080a121407201c051b09040503091009180b1206071403091518010c0906050904090609050601030f1101021b21030f0c07080106080c0118030b 64
    0x4080240090003000011500707005207441a00032400c100d40c03045412003032481c0410488101d00000e800c9072041c445d8418000c0f80f180300031340110360400071200d10600003040d44c007039540c880490610301210810b1103507000e6410007001c503034080102c4070007200071220075420b44000a01035680c00d0441e003203085044072608101d801030f1043d03413001c0440340080320100795415400d01c41543e1401c0407912100004d00c1c1000500707601c3e018401850308482c001c07080c2c85060410b0906025684400c84000802c402d5001e24111120001c2c0300b00d6421069914019490314102203000d8080d1040d910101d00881d602c001e03040a103d010b80c084117005a12409030350065a40781849003007030300c544000761400c01c0021050340003507000051140c0c040e91041c0c1000300124040041040b14001d030884000e61090701591000742e100d0620040c2414040252859110383c00f001415140030404c1d0000d030345076032402800b800300403c0010103051504d002d103040c0d00c6402e4000700400741c0180580c80100000c404206 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 681824676 1250 681823426 681823433
    0x42408152e0f060210020708091003090f0c17070311010f05070506010806040213060503100e1606050a030e1f0c170a060608060108040f0803060d0b04050a0501051602030d0b0109080a 80
    0x4020308443c05507007100d090700349448407003040344201c110003071101c00108904d048a0034030503c88031000e0400d040001d8080ca25855440c00a041c0140498000c5080c2400b8080c1c1d802d040407085442032101c0c0103154143c00c5549a0400d15807010f03416041c0245150700050a900c61000c5943d0584d0002c1603907802e594a4043c43d82c0c42c10159812440741c0c5000c0e00844803018980b01d03050803598020014488004504003d01c014040303a000c0c3c107a00c0c01105800801012120000402019603590b290350320112080010200c64801d400c500030b83c0c110412003801d4880c12140742188891043c40003500440321841031781c5a401c1c041c03403115146911410044200e409034405d00460300c041d15071501c656a0000115080d400031900280351110301c040840c04a05814041c5038000310161101c03800840c107442c0e08a50060440e012680355200c0300081003000000c1c002c4582242d12032034202d0380455654000b075200c0c010403c2120b80681c0d200d800d612941c2c800c100d00c0e002071070208195030109110b4103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 681825926 1250 681824676 681824699
    0x4060f0614070c140406120f0b0105040e06040209060f030a050703050709020307050304030c0c05031510050105090303030718050d060e070609060509040506040605042408152e 77
    0x200303400104908101844000344640200c8500d958070054000c1d055040200d104600090710042a401070b980342c4010554440d10222400328a014030b5910b51026501c3c0b6002150000c1600041e014604101e440c034502840003442d550400e60480c0e071688583c1c0d500010449070281e061540c0ea0520440610038244007020400c1c2007907074010b9041d84c0b030854039400d020f401e070300c000e031800000108100002000700c2d102c1c40461000310b10520100b00950340d10790001e0324010030660f100c0300070180702e000d0140080641c030409004150a0030020b00b01840d460010307440740401820082806140c06c2d00c0d41c206418000c0c41400303841700812007100c0c2189030820200905e00904c00c400642705007403001c03600c580201c1889048904503a606880d000e0f841c824080a0440a0100364000f91600c202250555807070081040800120141034800300a0a04010f80c03c02242d1007a84c0340e800000c000840c011516080c8c0b940110794440ea031030004018160b03226040780d4201c009200c04500c80b4045894603250 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 681827176 1250 681825926 681825929
    0xb0609180906070507230f012c0c0303030103081b010906020705010f0b0916030f050103120f0f0519020a051204090b1215090a1b0e011d0a0e0a0204060f 67
    0x212001030f81c0e4640260380d20310500307102814085d00320540c0c00e0308500c2020540b010f00b03821000d80b0740b0388442540d89804e50700700340d5104002c500c000c42c3c4050b10780c03040415002030f00140700061444041e02c0c0e020035102d01c03060102822800001841c00114225040109150400d10008001100c154105a4005d400140c0c046560b5400c1a2411400c1c1c15140160550107500070403c001588a01000000151500d4145414141c50f0000119040814803409000318091090040e848000d004000c0580140020210501c1008c1c0e01d4901002d620000780c0d80c06030010210303840c02c62040c90302070f490a6240079008190307110383c0c4d810044980002006d40229040d800b0103100aa400204003d4002a50001d00320942c8c440c00100d2400384101d1102031700720360300505035540f10255448000c106006a8030540d8400c42c0300d5400c0100f821840c91490051000710040031810447c2c00e00c0f405c0411020341071929264480700c1e44241d50740140541901a0360040c820000c1c10350f15542c1d4030140185 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 681828426 1250 681827176 681827191
    0x702040b0d0b060112141f0b040b040b09060729010f0308030408090a031401090308060d03020a031413030b250f180b03010e0f1510030b060918 63
    0x8015118155040244602140640c080d030550312030342e240e00044a0103050325413013a030429140d50607046e902402d40c0103103024081c45060404842101c0341c450100034084e5000c0046010100000c02c10a041d2000703403404d0f10f41341d401e050340d07603010680002c5440c0241d2030090040d10007104000c0710004805600041c201070125070704031503a6074410480e00034906100142c012a803c00025001810420040100c03650041c98101c8103506d0752604142c0d51000403403160141e640d00100014190440c40c5e4a90040e011036070029241140e550094031402500c10080a10070382031840040d024807034040d10180c5486025103611195641002e00c554072080c0ca04460710362035418902d6042c02c170390140318499101910780240f440101401194052500818900119419000462440d40010080d4000c2c604940d4852007800d142ca1110031126002d0000c1251928050540c500394640d10520341801c0114103000807401c40030380129040e4860400710783c0e840f060302c104103052000c00a94081c0124007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 681829676 1250 681828426 681828431
    0xa2909060a060602030306010c02010e06040906121e120c0507050603100509060301111c1413020f030601230a030516150302070510050a02090a2601090c060c03140f070204 75
    0x143c8600980c0c0707900c410740d0221300007000c5e041c0000140d402054114034020000c0c00f110314241d540d107194001c90303099800c0550071f1031600300800b0a101030142c0a540540907401c2c0440c4040c0c05540f040714419490900509010741c0c0d01c0e01318207100092020310b009010207488681c0e03a290070400f0301229407940c040d90384908c400c2c000ac11080d0505224880805a01100403846c001c68441007900e900300e0b00016240468484007104d03207a41200b080b10303000d507000809421030960584104009008400c00c2c0d5402644240010002044603010380d03801490544059554400994007050074014035400140c40d0b4450969119140b500c048020740c01c99942641c91810700e04003007400c8040e4483c0550145c4917a000100845140075958006a0010440d0300b00501c0c00d4000c41c0851110291a271185a00d450003800340b0100603c1c0441040020381c0c1c0400030050505265120019010f00d070240d9810490b41e03003100f0007090302490311080000d20b0000119200e0325074030890400d0707130310400c1d0480c0100e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 681830926 1250 681829676 681829679
    0xd0e0f0f01140103030c020a0b0a0801031101110604060c0215102d050906010e0414060102010b04151e030209010e0921121f0b071406090a2909060a06 66
    0x28042c42000c4002007500720900959280d0f40307007103d200c3c1031a80146da0144643d8000100d0f9085a802498208065181c0000941c91810801030b10545040c000f0306210001800d141c1050003c5102c90784030b9888070b0001a10156248200d01d00104038408500c00840e04092005c60301c2160031110445a40007815810324000303501c0407142d40380351030700b6038042d03c4030100900c228940071203e940e00c01d006140103a03030b2034026400242501c1020007064480602502071200c036580c203000d003104540e8255414092440740580684d05a0041c0c4a03044000030396082d0364040c80c030414098030007550014902e008558461203070b000c20ba42e042e1100e5100b0720030074250803100c510b442c072000b039015516000a41005884210f00c400c080f402800c8000000e4800e055001041c20020001c000c0c02c0e06082d0030361552491b10305039400c0030503110356078600d6000e0740c20404240c0c00029842c0c2515444028003042010916882a5440702d40c8000c01848459808000035107a00241c6288200080d060030302ca1070303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 681832176 1250 681830926 681830953
    0x170408190b13080f031504020409091101090617090a0605040503030702010b15250c080a02280b0f070b0106030e0613080f090f130203041419031101020d0e0f 69
    0x88000035000f030040d036041c003480e01074000150185520090f501c0038642c4c4020f8290000701240d10582141c014281c0d641c6298082c030094550040c58484282480350f100c1d400c1010143c00b81090300500108614100f00040c500070043c80720071324050340504144010b003440e00d401a100d40085840d48010761070995245050b00e0038100c41614803820308001d038a07020078000780301c0701007200b004030094444405d10500b001642c601031030001031000030094901201d481c41084030284821011540d400f6800010400d001344800003c0d0807511000c00c07040d41d80701e2205080c489802400d40c0a03143e0704000000007078860300342c3c00074200c0c401d84500761142c503502c1440a20030f43c0d00c108030152403924248035100b0000170310380041c4402c4070000d181d1171303034900c2003000036031080340d20820760b008070b60040188410801d03224050403989840c4000b900c3c800d1100f05814a18002503040542004500012040b00900030b5044440c5000009800d000c4600240c8120b5500e84090040c040303180f090303007040c500c030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 681833426 1250 681832176 681832201
    0xf02090f01051309050c1810060201021e090a171606031e0b030f0f0304052b0b0a060e13120906021509011514040b010f0804170408190b 60
    0x107a0b00700030000601034424000f03000007441e104030101d071130384100b9004c550b00b6940c81481410041d0842c2c181d240519000c1105001542d580d0b00807419680140103001191080c007c0502e4030318540050540c0ba0009900041d00709803a59000c01a014081c1c4400e1001e4040403940781d01e00c0030a60204844256690000c9040740c4141206030007260810310042540c000d20f400081c40d07100d0003021284501c2a43c1d04150400f052800c07102141d13030000904002c02d0601281e00311070f622201c1881b0ba4410b143e28143d1700150303c0c240005018051110014a80001070b50004014211070746900b0110710706128020850b09810304181c52745400035061449030761017903035a0426140d240c0d0261190305100107903406170b140d000d02100115520380707401080ac100d210b500040148610003564001c0c07100e80e001c0c0302c1100c14050450b410810407019600c2207070380003c0d0003500b00e680200ca070036025583c602d41c0310150007150040703640d034000c248000e824264407102d8061054092400c4000c0c54642080d0402c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 681834532 1106 681833426 681833429
    0x18071e0806070906080406020f04170f06060a23030f010c08160807050a18030602040603090311030405011e0504050d0b04030f1403010911160f02090f01 67
    0x200380c204014598105610f030400da0016030500c1c0005101c841e00410103001c554001643d00e07106140c1c801110000c1036500750950000c40400f803000d03112510403210b105548074020118003d4036101051030101d800d00502243c82d42c038001da0007140c1641c168081d0798140581815240006400c1c0100404100c1c156140341130352401000710b042450b0701d98005d400b006100d100b0031079143e80042c1202d03c00c48207410071407042e91421186204134002ca07080200318a001007800071f09150140c0121541903c43d454966484204000c034903aa402117100d810b0000d0380d50f69841014801c0312010204111040c6021494141c640010920001d00030300200c1305c011200e420030007415070084130341c8403280d118a8049151002a0050111404180201c05200d0f543e04100c0762010850021250f100c2440340c22030810405d181020030358401411802d83c01400070000117030f40c200c0d04002050 = true := by decide +kernel

theorem cover : BRFrame.Cov 681654676 681834532 := by
  have h0 := BRFrame.cov_init 681654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 681654676 ≤ n) (h2 : n < 681834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
