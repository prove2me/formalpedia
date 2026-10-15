-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5157
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:56:06.78136+00:00
-- url     : https://prove2.me/submissions/a5d02fa3-9c20-45b7-b340-574db2d1b054

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 927338129 ≤ n < 927517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 927339379 1250 927338129 927338143
    0x101d1b0901140a0201060f0e06011b150504080c01020f031906030210080a060b03190e0c011b02180c03010906080601030b0106030f0f0626010b01020316080c03030406090311 76
    0x10b848180004040c012540b815401c030054090440d943c800300017442110440c82400103100310914104141489400100110100d000201c0310401070400304000681d0104c1d0080480041000003c0c0303174550f450f0a00b118441c40e000096150b0000c0f030b8525003021413600547c0610302e10b90103d000740c04c2c2002c1c8e101c16921103100c06540a03421081c200003ca000d00310442e4404400180003c0c9251281c0c1034a002d50070a5170000502e5413107202d60b4200d80c40500c904071a011013180240910132100000034480d1402e080200400500521000304640310944034450306030301d00c80140f050b8a80700d071070340c0d8a80e04244034001c11746042501c00108008003050050503039801c50b800da00300d60308000782130b80038050b404101405a540c615054a08001500c00e40003e48104201041192412200704403100c0d18010852506d034034140e49180030741e80000071900d60710f14140c035411420099043c0b00d80580191840802e46000000420080100992081110314072175110341c0c400c0014030103090703600e0300c0d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 927340629 1250 927339379 927339397
    0xa02011e0504051518010804050c0f030c04051e0c0f0f0c0a0218060420090f03030d05040c030c140a09110c19050c0105030705090405101d1b 62
    0x620056090880122885210381032903081c200149080d40d24030200b00381044c51006580340c0d040101d041d1a80000203048240c1c1302809203032494642c00c0ca40c880c2900c0e81c1406002d0340c400c201d81840c40303600b030f1010300000d220418001d20800403840c0c0041030031760105882000306c4c2210202c40c00544510f4241013a00c0010b07003c03220030b0f41402c62007400510380e540426a2024503110f0900740c3e4006a807001c0011002d840c503400b044d01242881001e21003507840c180024a00c13207100c208090310005c6810140c400710749040b2042c01c130350015440030a0071485282d40300b11207581440b003000280040340c684202101d200340503440a440d41c0b01e500c503a06500c26600d06a100f00030440401a0300a02d4002d00c0d480e41c10703542c8003803500c4016031145281408040391000f01045169494043c080f05011942c00c007402820006d180d440d060f00c00800710312925590034400c030741e120041200005042841c8010342039000106000c140d0b0201d4461000703104849040184401d20400801040311805940c0405 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 927341879 1250 927340629 927340637
    0x90f010507020d02101a03101d1b0d06061701060302100801080607230c011a0306040201050d05151804060b01021b04110c030301031505010e0f0a0e010b1f020c030a0201 74
    0x8118900501d0251148402d05413801c0e02d02c12013406d05a40511009540c42a40c400010300002c1c0001c442c107424a842c506025260080798001821540103000d550b900e600403250751306045004d1a05a0040c006900404d2082c64805450282c40005520150590380200c40394040a60307255401c58010600740903090841c0c1000020890050141c0b10680140c038400600a60038200c082c6c007a101c03900f1000180c0a540e440d038101d00c081c06d09088801c226082d00b940031303049528242d00080d250748228196075a10a5850f80050021712803020400354100e0010460940800042d0400498202c00d440540341103181c901e49a01541c00040d04200c04890360844a0580c0805801c00000304a500b174240f4a0341e5003001042c90703e11050005602940c46010182c1c1c00c8803070343d410602240d130140c11424190300c12405010340d85442d5980c07242d005081c004085000d00380501540e01500e900082030790050802d122044c0b800050a0180103280e4240d030171100c3c1c0d6030781f550805545000240c0064042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 927343129 1250 927341879 927341893
    0x81e164a13021f080c070c050108130c1805060301090302060a1e091412181e09040809030c0105030f040615031a07030e010e0c100c0b090f010507020d02 67
    0x420650041540301c0074120348030701c0010341c0740c0114040100080e00804500d1141e0f00c00b4088a030051121500001c21914045c1013007003a945801d9125003070700510303041c0001c81002840350f95088500c46511940715680400e2259110000f5442c0007000d50000d005078141000120203040c1485a000103a8246d8010100e03508c0d030800f980c00411400b4034902201854866500101d0181e02620240c244a03030300c07134244800c07012503da08001300c1c0d82d144118000108040c041d40305003100c0301034450000b1112419402d0300a10b050b21b41c940b04404154000c42402c00f00814810b250000e0941400182c080e941000d820a004441a01c0221030503e0007440360001321700840c0442d4051f04126002e201d4050120b0380703a80792841031a5034960180803110b049c034100b02040b94503009820464490030024000c0f0441e00d815503403100c00c50f0f04290300071145c100c030109c0603030322a41402030496001142c80d2821304003d10201c0d200c001c1030960700d08660a00000c50341003480050641d54448042c1d02a00360 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 927344379 1250 927343129 927343259
    0x2010c021f02100605190315091b14061306080711010c0e0111210f090310092d060504051207080d060f0e010e09121b070e01081e16 58
    0xf032420048c000c080196a09841800103403008040c00544100100180d02a4640710000d080001e40c8130034103014102c00d001e2130440052604060050301d01d24103114180f0b0707a84c884202d43c250415841011150708103401d0340800b03a0041040080c0709000c1e650b00119040684003150b5402c5044042403c6001c00c034552400580d81c000035100002c114a0389070305e801d2400c8002482c200e017074071418000c56583d000010400c00342c0b082072034500c01860021807180070070f00c0c880380300641003000180166446d20009030801809112203610042d032040b0840d111a524104003c00741c000000401000d032514401003103103050b54001d0030465221650110300383c0c0c2000040252104041c00e220b90314414203504417209400d0b40080e100301503800d41d503c550420780507400c501e006500d501c000c032b5000506c0d0041c0062140424101031a00c0082ca403800c200d0041005a86848590440940509180c81000c03800302c03400b485e00e03420280c240c0d40c0321410402c0b941c50b00203060a020f50486440035803050084c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 927345629 1250 927344379 927344393
    0x1501030902120102033d090b2107080f010b060405100e100c0b0a0b03030307180503061f170a0212012d062102010c021f021006051903 59
    0x2030118800382421851480b4088601c0c2a0382007500d000c0841004940b4400c151070030011b00034001001c010014401090380203888044090902801441c00e803555031007502502d0307801d0020900b282240c8464a403181041e4030316100d03501030052035514060b100001d555003405010380d49004000a294501e803618140800040c62404840c8000740551142002d03400c1c0d4036800c0407c400d0b9413a444070480303d80c0354913048400c0840106401d41042c41c1a12420550b20000b0035698001d07564203000903d0390005009000c044500e511940d40340c42160300708481c00d440b140d503010104444403140340c1050b0311120301107403a03031418a0103031751a40402f0701e523005490000ca1250000004200010303040144410007969070390030014076003140c59900e07406841c1d45500d00c1841d0041c0480d045503880c0c080e111003011103180d03404c94003074100001652503c0c195031714000344c40b02a644484000780c04200c240006034560084e1101c0382246440c001d0001014100020303401401c500307508bc940000c50855803401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 927346879 1250 927345629 927345641
    0xd020114070f11060a021305240c0309091503190b060d06062606070203070206040b03151003200406050307030c09120b01230303031605130905100608150103 69
    0x8000c01043c0c4a16a010352814450a40a0085a140035035030382c06400c40d40c030400ba0b02c1e074005800303080d01c11860629280501400180d0140380035401c5da441346100ea450385140a481c40555100f0003003002c1c0108002c0b90780e100307c41c030202507081d65070012503101034040c0b12001441c054903a0010342d0003c3c0c0c06141640f040c0c9200c0e40304a500141e903079140d9140540c1010360040d0a0750801d4284d160350740e039000820500d580203803107200035840e0405030f501242d4107001c0e9109a540241000c0081180c1d50b403040c58a02c0008000380078100e840b1800c00c002006401095050348158034484002000c05424070121010380b80705489079032843e10380d684201c0003080342d1400801040440751700491881444040f050800d03028a070140c849504095040480c40ca04c50100b45d00d002809480350802d031404003e40c0d0b40407400303150b100f24a6000990584540c420581c5200249460000c00318a0003565840315020720415042c1d50840b0744c0b244010b490341c0d071045d50b0141d545160350001503861340c031075004a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 927348129 1250 927346879 927346907
    0x7080f03091e210316031d030a08011409041211070b0d09051632090a061d0f130503070c08060105031002090f040c050c0d020f0d02011407 61
    0x1141480b0040007070505241001d8821072060300400d00b02482140203807022034006802100503455420821043c00440e1100e952140078107407607103440d18154807406000783c1002024000d0303035510200034000078140d100034051101d21400c2d0080400c00c50808032092072146601c4284850000d04943c8256144104131050300c0760380c490b414012410464901c041d0000c14040d61001c02c19001c0c43c076106041c090080f8050700000380c0c20204101d60b000c20211000f00c0018403007105495004001980041141c800b2007a821050340f50078004204400e5008600300e404c0c1e24030289100300400300d10302000301c0035a103c0411040210102d14030006100418450510500440349420103d40d02c1c0340c0d040025078002c2030300b904000010040c078281444082d02922400034114501400705001030800c0130122603041c02155204650000d46001c0c0741101c001d5000c140450301c0c034054450000f90384d5403601c00315910900900041c0102c403401400343c41c030340083d181d4107041641c4d207602e4110399138800c003201c1c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 927349379 1250 927348129 927348133
    0x90f0d080c070305301b280b092b0302070f080403021908060f0c04090e0a0302010f180605130b040b060918030306010815060406030605090a0207080f0309 68
    0x20107140070010088030340190b10a41c0900b22954407005031801981c0150040b01020b00380c03003202980c0d0005001220021040303e4401131210b50071802507031402d6041c00349164058903124002030031911411040d800703940300b210250f0140e80c0c1c501c4059201c6003a11080c0585803c400c040700c03a4a004220340c3c10801411380b500508040094490009550300211705443c6440d00050620070350a01d0007001d4510024145131140c1c0c24a402500f03543c96600030058400300014001080301744020004540040030000d606024040400c4805034444d41d402c141100558681a400040440f40b4003032740718001c40c074840c4000c4662003070b1608030181200501c9007419a20b402c80b150300181d0010031442c051801003039400e803985805420f00c00b584401804408800301a41e060000c0d50200008607035009000b80ba2201c2d0a44075200c402c134490801600f0980d2009010501003511a8035610040407201308a440d007105450343c1caa020200d114200002d45464000c1104e03144030644100110f401c00701c0e60003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 927350629 1250 927349379 927349387
    0xa020d0f0224010f05030f03072028050108091002091305010f1d0f01050118030501020c010e060a060b160804050d030f03150609180207122003090f0d08 67
    0x201801a046841e500b1890204240005104002d40c500011001c1c1c84268010400c420704048095903038040d400d001044070440d0082c00da58407040d400340020150307000c1c007015500c030100b1405a1032181f4840ea414042500c0c007000003599885032403414000d900303450141550000340a202006544181e04454000740281c103c0c0c400c07582d1520071103000340805500360402c0d50400708024030000782440c070704c8030140e082010702040701a0000030504541003424a070840f031081001d00320710601c1690000c2c00300c0d48080f4070315604110641016412003480010b403001a42c440326560212031a9015800c280c45040c0881085404003148004800e030242c42041d06190b40d03600003031056007500b942280094580341a000740940c02d1301600d102c0e148603205c1c40160a0810b20b001380308802a10600803010860314002d144880594121408141c0050a503840207041c0030020b0039510001c0d801c40f040e43c54540d06022500c2020040d50350076038000b00030156003640d007010000d00c965a9007003500d401d0f01c208 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 927351879 1250 927350629 927350653
    0x27061413090204080706081b03090c040f0204170f15220c05040b0616060b06070614060a08030c1911041e0b0f0f0409050c091509010603020a020d0f02 66
    0xe4010014854004096941c40c180320469040c0592544602c0500208600303008000c4080e0066070354400501420a40301d03035990800520f00f064140107140c0042c81c0c103000102110f1301d5002030082d00d41d1581d44501c400c0100744025a6100c040610300c1d06030f004403000007042602c608000750070000241000d1403d0407040000071b2103c0f40c5c0701040718070a9807400104404c0c02c20303014401104504a4419003040d243c41d001288016158200030b100c0d507510808510715a44800950b20303030a0b01b00d1070400004404170b90000708450140e403091320505406a00003280c03100041124112000c4c1e074060146c16030b00d40000075414092a030b00b202e0440ca80202c88005480b1442007519085001c8002c001c4249558080002c848012030381c0f0b801413130030010302e07072090320354200c0e000c0000015240040e510200c0d04241d03003418014034400307a01010070014081c1300740c1c40c90142c2c010004112104000c9903070f10102a000c9100e003604010141c0c0000c050701480758007644000652a04e6401a519005d0f82c0d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 927353129 1250 927351879 927351907
    0xf15040f02091e060906031c1b0501050f0f04050d0f02030708030f0703051b1c0603020d0b01030501150311060306010c05120c0f012c01090b070c0201270614 69
    0x440b00b84025001d9198034035414220703201d0891308060192101d805508101012940799006a600d80241e4402c001d40500340700d1142440400c1120103000800801e002803401d80c0c00790806540001c1781c1402c1e0000708940d0396220100c54091303a4088000c00c207031000c114056440c9480303000314000b580010300c0241c2c00300d0400340040d4843c40310b03090603990703618001c200542107034405001c55280d2142280409400d01403030084542a643d41e0070711103498511102504081d00807600025084010351a0481c200000032850905803031242009015454a4950b8441007502500c0050701346519514207010a040c074400035900001e06240040f0000d401d40c40d45403808607903500d00142c1c1c000000c0c107803c450f0414000031508411550081c04554031000600c3c014201d48041603410003403401b40701684420035400f17992202c3d440701c1d100718646810f5401410554040e070f02640070810500c1941503090103030805101c403a8100c1c1c0f4402c0443d050603403c03160702e4181c00c0c0210500104229018000320700d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 927354379 1250 927353129 927353131
    0xf17120405061501021b0d05010e060402011d0d06020a020a0204090c15110304090c0c1410240b03130b010e040215031506130e0a060f080f15040f0209 66
    0x4082065092500e400c5251540040918a14002c0c158114403203aa0100340e02864051003600b14038055440740000d1001f0900b010000e107251310f090040d01140801150b02c6100341d000762210114072100005150303416001c08003a65210625504000002d480e86d80601400035952044842c81c41c4140d011a0451381c40c131000f074032184404002000244601142c0e484110300030f00d0b200c10284610140e85503680a0b5000310000305440b03101000b2041d00c80c144500c1d0440c0c121b214080c0901b440600603403180000442d05048a04250b0b03007503241e40411920130914240c030f07a00c1880c0680f07429403440940d04064110380400d48481048004100201c035924060411300c1d030344448509007031040103026030405041d01200c4805104110144d0400791240c620105e00369001556005c19170001c00381e0f5826030f08810f41000e2401c02740f0003500065031102c3d0680b6140707a182c0151a88900c80684d5410030b000d02081c21340d00c041e002405250110740d0f0079070098811004141c4450a56002503c0120 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 927355629 1250 927354379 927354397
    0xf19061e050a051e13031106090a0302100c0b10050f100c0308040204060b04032003070f0e070212040b1c02031308090619120501090c080c030711070602010c0e090709030f17 76
    0x1c5d4107020300c1031100906130350340b00d0301e82294a04c0ca060b1000f004100484420b2001030b20404034003076040300482c0625074034807184d5407150450809140c8103018028078441401014041c10050070300b060b0310705201e0880080d817912602d031454a42c0745941c0844865a006104070f8000d51582d0002802d0030440740038101852044411600f00b00c140c1054607005441c0c140c100c0e101c4c0e400150100085a41c8091000503070b2001281c805580c1d440c0201a403a01030f00c1a420200e05000140005606030b21801900f8102414084045c0b001745104c0700506a00042c1d032022400d400321010200041d141c54001c005008003d0105030504021801004d410091447c0780740216880005624005541e0302c40e06024102d03480d401c008580808500402012005000500345840000070440590052420009800b40c0004507106143c860000a0180c503403c403001010881c0d109401501e07113010000036103c1c031000c0d900c400920746543c485d10110a80440d0070f8a00001c5c0c40c1007030100004450080170407803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 927356879 1250 927355629 927355657
    0xa03061a031006140d1e21090501020f0105010614090f040e01200a050a1d09010b0d1d03092e03060302120c090705090f19061e050a051e 60
    0x2d4600040c0410f100798856007136115a0b01100c0d240c0c000385550b401400c9013045444008184c50042c540955080308549a034000a070341031100f141c000e980020001c040da202a4256400c140302180c1c294283c4400380106000702d40c0030131110340d0940650002d4202d008004003610b4603001004080340480d9903005520110384d454001203d042101c06803e5064903013120007451030b00000c2817009043d03000301083d5a00304441a19804444401800404200b180050a480c02540c1d2900344030090343c44041c080d0f0100382030480128240e00f80c44581c60340070301050040c614100c070310b6081088561398101030012100c040c180380c21800e4480c6848008254142e200003400c94218010001d4040a02040281da540038a00e00300340354542e280d2a613003002033410000d460b00003c100080b580c00007903010607000031640c0c1d651552885500421821101e284d02d400142c0700040c10010011910f00c102c01c0d011510401c449200e140c46040100090202c0e142d0285a403210948083d8a640c0070800c40c031504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 927358129 1250 927356879 927356891
    0x14160c0501020d0c0f0605270a021f0e100201060f090227012001180b0f060d0305040b0304050106051018150c0b0405010e01050c0706140103020a03061a0310 69
    0x1540c040050b0300300903d8a003000750b001036480e0707144010003046820080085844e800410200400d80280b104154100008000c803814620001030340c640034080c080c1e100d4040d5401c82c40c2d00103403074240844403142565854400b00c17449001c0c0703c1c40750502d403440000c566070340300006140d600c2c045021f00603040b40000980d80c0c40b0784036403610103154002d145803491005417035000a03680c5c10400d460070007540800036240d0038401ca0700d094010702c003160261001510082c625010400d0741c0718007904c41c3d0070044840034030b621141c0902401c004030800c0240490420081401140c1d640070195900ca4814000410b1903034450700407451841103400e000000c104607070340c80403030405680844d01c00351220004032b4540c8652204000d01811824401500222145020806002e07080d00090194038008000344003a0804020034101079001c010240c5400e481e201401d44e44403000c007852812290020580c000e258290f444060052041012031a01542c80d544100c4003510207102149206480748000519 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 927359379 1250 927358129 927358139
    0x705010c1a09240c03070f0c0c260a0f0f06061d0105031b0f01050f091e090c04080a03110a020a0f061701050a09020a02070f0b0301150203120714160c 66
    0x4000c40035054a40340700f80600420954400d24030503642d00c4001480d11380c1c410550204180e60304034a011000d001c0f403a400300b02044000f1000d0192641882d0413080c4410402c2c200700c11038440c850384130001d0510104c4805403010800701c008120034039004860020300b444d61000c0404860000002c5030740000640c400420003440d051184240031038070900800305c0c0c1c505460000d40d43d100500da055050100114501a000c8010340079101c1c1c144003e441c0410004500b51b002c03400c42c8000503458402e56042c0d00141d00d00c0048000d58040b80c0410005243d004c440d0760301034a49403035288845415120383c003003020141c0d0b01c0c40440341c0103080507002c4600c2d2a0074000c0c0242071150131046207404d0b00c0e0f200010040d54840c1e007100701c02c403040050016113543e41c84e04103d041080a6201c0d02852003516004500c280300f42d8015030480d00201c02005000300781030820ba859000300340803501c1c8000e01c0e80000b1822409042c0740c0c6001d40500d00b0143c5040c140c144200c46904c0d0800058800d0f458075101800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 927360629 1250 927359379 927359413
    0x3060106210c030f0c0e0108222f15091c0602121f1404020a2001060905221103011b050309061b0a181802190806030705010c1a09 57
    0xc02d1001032400b15a082d01490018164590180c046040a0700c40c035002540086401821070740c80f2b5001c440c01e4a24450f46000e20400265204000e000c0c0d010000da250b5a803802064500c000c04121154070708001d190020443c8a8a0b11541c18650648203800360001840034801080d015800001282590a05006003003020082ea449021042c00404044c004809028286070810304119000341ea200380281c01160400411680f10390800048140d105901c041908034009694800000304000e5864018903241c503002c185001007090324020448021810503010300701764410150000c240070801d10500076400c84034601c41c1c4001400442400040401032025a8000082c0007080c10440391700010030b1100d1003060b40702c00604c840000450a09103495981000070410b0140150410200402da0400703544500c054000e01d03912203096000c124002d041d43e0f401205c010300180b1403941404019180e00d0b04005040c1d41c40000b600c10401980140d4081c01e214241c240060120222140740c0e0030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 927361879 1250 927360629 927360641
    0x120b151215040e03120402030705090c1c06060905060702040b191a0403053703030e25090e0102070804120c1413050c1303050610080a0203060106210c030f 68
    0x42e100d0342c14020301003007541c0d00205a51180b94829840802d0b615240f0004e03140103c684d000f81c0d0001118010003104006490280c5032107209096000701c0c8140070000581200c440380662008613601040501042c10283c003c2c0c8400cbe440a000060094600780c0094038490b10341401564880e2404030030301400344a143c9664403008410080c1d41484e003507550300c60b10f401c122217045040c025182140000c030244103400180c00d0f07000d210503046c4248241030043c080c000d0304800c0350310b034452070302039603110a043c144400381c0e0a144241c8408036410080090050310500c03c604013559020302180020510103001480105901c1b0840303c1390003040d01c1c200d40040c083c1e13800b40c03100c4070740e40c0328000e060746900485100c00d11010134005515902c09600741000d0050405180b01106c1d14440030007040700c0043c080b0701a1400742c8070742c1c5400e03503208002a60348002500003501a04150b00400074140184201d42000c1d004c0c3e901011b840c4510380c084400c503884605c0c0000003989071030018141301400d02c204 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 927363129 1250 927361879 927361921
    0x702190210211b0e061c0e070306020409140711060f0c12150102010c08100b070201050706180302300f04080d0309030f2d050d06030b010f08070303120b1512 69
    0x4509140d8424400c04890710b44003814a0481e407039154180c0340d01e1081c012340000c1c51384240708540b20b60300c0d0340122004105603400d030034112601001107000c41e40240840110502c061b070040015580302041e00800390b00141c1043c100a07000d00c0104c014040c0000328070b01c16018094a1100060040002401d4802c222921820302031001c003480a03a8911044040c20f0307507444862140d940a10b440105c0f4603208240000c3c010501e0309042c424080c0d00c01450544060096080354248e01041406104118205c090494000080742c001c030424480c04000c1e01c07402c1d41e0340c1c0320a030915950304803003810082000c98441c0040e5031105117604054100c8400e900b4084a03142100d5411130420014081070440e4500b500c408080041d01401203100e807084804490760b80030103118440d92850b080e245400203020341c100403800300002240c104000140103049076007540c0d038031440300340c0f0580c030000501c0f5042000750010340c40102c10111441040060000010651000011303203460912042c00c10400d000b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 927364379 1250 927363129 927363139
    0xc090506100e06040f0b1c0c050711010c02040908071a0c0904050a11040e1e0126070915081504050309090910090b0a0c0315210611030702190210211b0e 67
    0x40c5010149d4880180e8107035551120410310120b4400c40140c800e10180e01d0300a5006d030030700d03009200f00030b4290007600c800c5d84a843c01e0150510010003e080c2f1160071151a0b010910600c0f009195141541095070800c103000c800080070f42a10760b201c04964099044085604400414405c1d50001c6000c402c0b41c9210865981445505100da42051071803220b0135681d02c0b691485010080078014050f1000401c18a2010406103050000e40c0c1100403683c41000954090482c1408507013000254180c8100d0b030100280d440d160703294003000003200700500346210b00d11071102c100050605522030180e455004001207910352070f0040442c0d003580e99035800c1d54105030415407043c4041c2030195a50040c0c0d103000a00c124090b04419442c0c1c21050703803800242655081020200ea040c60380740c000c1d805462194240c40030600405d054242c008161540250820040c01380030003054400d01000c0203101c00c1002c0702c072650300181e0003a42520303008c001d1030319003501941c1d482d60100d42210040c1e00040c001e0f54 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 927365629 1250 927364379 927364391
    0x1207030803040b0406150807050a050d08090402130305060c180d0309290d0609062103080c07120f0219080405040203041b060206040c090506100e06040f0b1c 69
    0x9a016014080604002d14401c400c401203005c2141d1504004501c3c41001078460410f43c3d070700101947c604640c442c80f80613620404000c2814200b521980c80519000106249041040310902c4002d40c440000c1c0d800726102d504002c00081c9040c48034030700482c540704e041303901c0e40d920500d00907060800388040341c0f2411078000316400094010446204503071604407201401c0d101c92020351a1015084003113011800001219821009079502000c10f490030f1400401440b5101c03500201c501c0c00c2d0ba0044903d082011400d00002841070406c5607000321041c0750705040000070303034596503044003100c02140840c40b010902050390707904105d1803400f450b603002c032003021110b40c0c0c841026502c01c5000e114099500000028103202d0103000321080d080302c2c658074500040e13070750100030340f6440140d90859582c142c1c8240000d00c4506405604e00907032006001003003904010354240e0303e83c410140c0341d9070808030921001400c3c00b420548a80100940007040e640c0310440248402102c048540400215107015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 927366879 1250 927365629 927365633
    0x712030f1107030c0b040c050607060203041208041502070f1509060f020319110f0408150c0a140304021503100905090a05070b1321050c01230918010b09120703 70
    0x201c600c4c00c0041e0014a05c4009807140d04061038507941a82019410400024080d0304010f03180c0d00543c032480c092500181d40e2040c0c00c0c2c0031034001d42d0945020b092a8040b03160b0354020606580204221031084082c28020203660760344e10785048a00b15118012a41c0b00303018418004503003c0c0e009000241c4100310301c0c51a113000c03100f42c0d60106917110780310b0702d55a03003892901c031020b0811034442901c171070030040e2941e60362482659140d542c407010302e4081080e01d01040920450300309517180704209866041d01110600c9049501d904000e005a038442c41c80e0411115244401000b18007030411a4248082a81401503480c15a4130207005a61254020205c140102e10080743c90307001d0362020030a459680c0146d28801100100f142c00c400311889551540c03488a4074011819500c0e10b11460a031280c180100005440c075070009402d04140708448038a01154691140c001c2c1111000200340302c66274007400032911342d6000c00341c110003902c07040041c01303260916145031500040b408c0c420050030014196 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 927368129 1250 927366879 927366887
    0x131b1706042a030906050f07180f03080a0c210306140a0b07080d0e060402120d14130b130f050a080c04020a030204081603120f14070204020712030f110703 68
    0x201c8080c0c1030038820741d81c1c6002100e100303801c40011645c001c072040c0010700344054103042e03902c410b0701c0c41c1000c6040c1680f404445205060f0060840e104091480e8003149141c0ba00794165001310405801c11904894440001d029414002d800070105500300901242018016048403001d400092003c0c82c02025002e01c0e540d44070983c401e0314000c00c445520b90481d40303089103442c0510000d03841a241402940f500d003210000b800d070302c03c50085440d00340614000c07103095280c9682058020015001c100300c17440d40b01450008181034604a004107008641e28906400260010b000840c105100410108911290106c10300090941210210700340d034034000d00d0a582e40e00d010b074803500903500031584580450083d415079000b400350500340c60b082c10320440c04489100d41400b0480d8042841e5842c1c9079001e21481500c04600030f40d0301d8200d07803540c0d1806580c1160708921002c81e40160200322200000d9110b000c0c41a1510040d200811280001038810081d00c031960009611301c00c09020300d0001ca0b0380 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 927369379 1250 927368129 927368171
    0x18060c0f09081e01090803010914010b030f06120c04022712030403030f0e12010e0607020c03070303080c0d111803010b090604020d060e01080a0c0503060103050309131b170604 77
    0x600a6100009100b0703070181340508420300c00901400c0d00400001f5055420390001c5040700f84428180603da07886028a405034081510004100a02c4000142490905071045040c00308084216012500c140c00000c00380c2c0e01940700c1c94580c5000046c1000f04544107074040d4191082102e045c44144100c910703881e44c07030045100240800800700901d80d1001d0007168031025505015104101c468903000407580039007012924a0090700c904800070350104d00c0400c4a0038a40d030000c0280000601e90f403411920303090003030001240e00708108103214800c0050300c9901064a10341e050760343c0b501c428043c901c040d070400030304507402641022840c8950f651141c0c441035214030704480058451490711000002400c041d001081003401000000c80c0300400000c10409003407040002000c03840e21107007859203034074080c4401480740c0c0c810700056031140303002e00185910642c800e100007825031081c0e116000101a071451480442c500d0400458240481d411150b484041520300b0700c6200b05042003812040e81d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 927370629 1250 927369379 927369403
    0x60b03060d121101020409061e0302130c021c1701060201140105100c020406081e2107030c0b0f040212150105040b12060124090b12040618060c0f0908 66
    0x5610b0b685032000d5018044192106452000840d1240d0b21031450348005c0c42d00b03010304074003283c6010001458101d041c521006495000e0400c910410b40100a24050034010310040c040d070298a14541d001d4140c900c2044a0002c0d43d0f580c517407030381a5103005090f0840e044e002241164180340d00100302c4070b8940a960304540059407844040305907440d003182c0c641c90180000758028141030001a05034000100e5140c8601103410640c001c2e55000d1419035204000b19104540d540c05000342c01c4016008030290212074024100714250030315940c0d0340441d0389400c6030710314480340030301044c0801d504112100c0080c48410304010003a5000a041c22803107044144a0188241d45541c3c4100041d02c50300c26030003400d034a1104542c001c2d40c484403d80180001c280c44003030618103a1b80d50748041c40c41261040202c8015015040c07a04996068080079a18001d105440003520707a007000b50030308103030542a11114090700000401940c1200000d1001d05204006410080a01014007069001060312008a8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 927371879 1250 927370629 927370643
    0x1006080709030b0403182c1f15030c0504081b120d050c010b09060109030620030408030a060806280608030f0a1b0f080a0908030d0c03060b03060d 64
    0x6035902504580481258000620588004041c80101078009030464207003640300d402c203c5015110045c11440c074040d440c41c0302c56201448041c00c040d0407680340140d00302d5013102408000c1065100403d124240d41d074046903600301d918030780002c1543e15104001d61190305203401c52500741390440e0f855541140f0300e070b041c080c0c85030310440041d2071f0b0b50603585900e88040e00c03090714502101e081d40506a6000000c44440d9542003030024001351074818929841401c05848082c1d8450541d100d2000a0200452a103810103085400740081070100d000b80d440340d80f05050056591800d9000c0900b59403180d07001e804c00368820018403950403002494000b00d04480951a440c1c594055651005030199074012403a5000c0003817120b600c5042d0000401380c101003502c2e4a400d41c940341045104030001e1318006012014003c116000050307400d001002000142d1034104005516100d101c2e08660204d03411030402540c0d044882e50302c2c0d07010b00842d8001c0c412050160b003103250103004501040c80b0240010090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 927373129 1250 927371879 927371881
    0xd11031311182a0a14030c0c070e06040b0f09070c03051e040e0106080f0c0708120c04140102060c030606070c0308030703050a110c100507053708100608 67
    0x140c1c4400d5070011121840a010414504190302c400420601982103495079600f44042107075203e5031103007102c41c0b295a55603013807020540c611404229400c081c1070407003070200800c415002d03581d0800110010701a0141da40c20745003040801c020440e20300340b1803070780141881d100c04141c6d5560700c41c3c0e01d07600400d5401d1550304841c00345002c540a1040502001051409007405803100c0740c50380180050710b40358006040c9990725201c0c19210ba00c800c81d15403400250f40000100ca4500407009000c1e030610a0142a040c4880d64034895000c11703044804207008000818104545403030705201400d06002030016101e03604240e010384485120003080e040c0158030000718002088581048880155040a010f5481c0e050805004000e09810b441d86103505042c10240b0f00424141000c40e402c5090200041041d0800c80383d01030f0140c4001840b840034058107000400c110150241c00c2e110201c0361790304d40c03e4140e65903035140c908500280c000d0310030000c0b00402c108419803a1400074042e41d820b4200380b001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 927374379 1250 927373129 927373163
    0x40e010801090f2003070806010501080915010b070c030501020309010507090b1206091008060a1a2b050106050a0303021e0c0109140607080a080601020c0108090a030503091603080d110313 82
    0x101484684e8903980501c21a03000107a101000301d41c8078180e501c00d1f82c2d002d500b0344542c100f035a510000752080e118100c0e81980108150108040240b18540c03180c4030b05003c0550702c1e1516030882c0c0040b550214507035106c10801001c02d6104501c1005040030a6019042070005a554540c081000b401c2c24010607004000c2014030a000181400030000f02c012240b1074036005e00b032178014211000d203000643c03030307100c426469600c0c0881c0b0058142c03d003166489070100e00140ca1104990681e102560345550f2107a0101d001e4a40c11100c2011714001c2d002410a1400c41c0810703c982d54051810440a40015010a83c51ba901c25611400c4499141d00b4001c04850100001c03054801c0700001020810000b03844000c180c2c00514080c8200426000d0f1190005010010b5654100484201000742c02103240703400001d000d94040c50304074098802711640e2488004024054076031036017003074441501c00724140c01c00807071347e0085044000c1c0b6803415904504108900401711800740d0b1000300015000614149 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 927375629 1250 927374379 927374423
    0x1110304092408031b010b06030708040c031b0503150106080402060a1205100e1e16110f0f06010602160504050a18150f09051c05070f08040e010801090f 67
    0x101c481e5070b900b0408001c1c1d4950300d50380e0340d50050544860900907107844940018041c42030038403545000d418545160b40e0800121028180207000321004130302c2880210104181001d1000144488403003044036a0402041600c2d040603021148003840c1d002c401848000d0340618400d0b00164140d074003e4452041c50740070344442c03402084540ca058a003604000c0340400388170580007203800e07640c000340594542a0700701200c240f0700328507440c20040c0c0328081202143c640c980b90b500c148243c900711106d020820031041c28045028440b14135940410303a6580c41c102d05000c51307030050516000070000e80160409520b040003061181310b124542d2040014000c52007600508280c0394078105c00342d030144081ca0701894441f00c0c011003d20403840c1c0340d00303d0542103482c4119002103030860000d1030541100409907141c0040b503441081002814001c82c00006c070b4900311851030a200d003000036161801d0040c01c04503458140d0281880b43c0c102040781c0d022900103040d60002a80012159481e0042d40c4a110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 927376879 1250 927375629 927375671
    0x4030507080d050709050d0203070608062b0209070903050a021314100801051b0316210506100507200324010e070503010503030a0e18040605150111030409 68
    0x140c2050030008001c91040d040343e0116100312605d80b41c1a8103292a0028050900714415000750550b21101c01804818041d00c5101d511078401010010307a58500c0b000e180c0c0e2600c00100c564042031480460004601e0300c01d150960140e000d140801469246031a00c55039401d0041d00607009181e2a1b100f0340b035042c526005942c01021081082d202c5003451080c0c115170700000d100f82d034115485c003000b05100c4010081c0c9508540e402007561815912003002100b840924180c07504180f05200540707401c81052412842d4841412450008451030000148102800d07100c1081c0100a800c120301c00c0010a41d101200c2e101c039035400006200f9901034007280c5000600f80440440103800a13082c0320701640f03c45210f050711000009400705807100c0a00741d80a000a001d1302e981500188001c101c80c40c4103030202030014100424001044160184000c1695010341d07040d81c140e911003042250076100c0701c14000000d5820b107440c0e07106000d501c840f9907ea000b40c0c010761007900c1d101c4411020510700d07031000c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 927378129 1250 927376879 927376883
    0x40503040b160b2805060127080a0f0c050303092d150c010b0a0b120c1c05090d110318030f012a030204050904030e0103230106030b0904021804030507 66
    0x200107402c01c141c90040c43c044820740c19010241d04c08090000c01c45900640b4041c090685445a00c0d004070380607082e161848580c440722031025181c00140901080104440080c01000d0900c50700c0c0f124202180480c03800c2d08464000c2d8810003440d28a0b0b294031040320040117010b00c201510740f1001d500c03158543c10f005062540405c03000e07009403141c08001c0c014030841040c4002005400c0c4420b0500500718060700ca602440c080a004400300780b5045082107601007400b4281a00d0110700c2c11580c020342d410840c81841280d528820003022440c02c02115004075203508000340303a4a0b103e4802c2e9900d1040c96500c0c0c0d0b906100190356200c64400300b046800c16521b400081c440200884004000401c803540c68202d034442000f4540f4425000c0e100315016118080e00d1020540c0d1180c40994020b441180814105644c80120803402640c4500300c5540a10100d02c1009952401800a00f40d801c0c420352a84207507514014000107a44401d02d140c52041050039940c0e80740c1e20b905085d256030042000c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 927379379 1250 927378129 927378143
    0x30224010302060c0a020d03050a0315031203110d05040f0b0a2a11101b0c050d0503070e190603060611030415111903180b03190618050414010203040503040b16 70
    0x1224023055003100292120070002c1d90200805500000344403a402c20a1102400650b1000c8a10f1510340c03298000307a18444c202e60071345143c06142c40f036040031030344100c90686d60400004520b0042041e010318140e04809007800c140101850b14024803948491088c000d003a020014800007401c90017011032200c0c3d0f005600540e802d0004101d0140098000d007000b114004403078101c2114490301800d202d0451710303009401442ea14031000302c140c0b10341c2c3c406840c000501861120f5402d440d5184000440c0c9038070700030611b6031030f58034151000c0c00741c03484c0740c000c001031100301c02160182401c000180c4085a0104c588103112585c20700041c0ca9503040c1c0c50100016000308401c4420201d080004c2c51013103440703680c03809002c41c0c0220107000403800324058209031803030801c041980140a040c900307040450f41c0700000382c5a030b503031f950b20b4500d00c0720034800400d455281d108001c10b100c110291000c072501c03600300952540c07805944690301c9101d14000c0c0007000c040800c164071a8042c108600360f04075070002d9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 927380629 1250 927379379 927379399
    0xa090203160f03110405160c02010311040303030c020601090203070f0513122001020a030c0b06030c060a0905040e012f0d140a05090a0c051519030504030224010302060c0a02 76
    0x11941007400c1c01c601098841c0c41c4e81e40c0010500f81860f101d01031203020400e1741d0340d001580303c500441c0c500004210136030404d500c50f00130003d007e00c60030007000114841d80b4000740c040800100a0300b4504140e000c0741a651042c800c11603150340102c0b8144954055281c030540d2a40c0d001c248004a40d5503070020f404401120000200304110280c1d0782210505681c1c1b2810f9100042004903a144a43e020080000b100e03900a9400280300310607030350300540002c0c00c1d01d29020b52040489c0c02c580203d010080040c074011010007503401d01c1d00c9081c04140700c180090000d24848100058124071300501214000f00d02c064030101441924181d071041014400244040010107881f1003d000701503500301c0403e0314000208a003040005a8100440d5201b11104642440d0800b0040c55101040c402d03030b100c102c00c000011052080c1d01c940003c00030a0341b00080c250405040007881d02580f5110310010b6082c40980c0e000c1d0b115010307501c45c1100d0381111850303555010b555084e4103141008000a4001000030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 927381879 1250 927380629 927380639
    0x51002071e08090a080703033c0509100203030105060a050a091a0a1b020f0114121008120a09050411071a01031e0b06090c0720010f080f0a09020316 65
    0x1a0080190f01011107001c3c07041c540305c01c8074580b10b404920000340401c51103a00300007006002c903d030350032540c00c403e90824001164070303501d440e400b03820003a0b0300000c0d400100d55440c8c0c0b9001c1001c0621704e085100a500310b44c1020301161951299100c85c0c01031140102d2200c514510499204002e4401c100a4880d10800e1b101d0720441500300303252103000302e100c4110484a41140200a8548603002002448a540510010742e402d000148800a641d6010403148488103200e00800b0301850494007011500c52611148a09091400107042c101d0002009090403559100200c441078130000c540000d1800558105080a132059090080040f17105854200707984400c42c8503141200e02408855031039030103a038845142c00544d80c000408100500d800310b5454101203919681c0181c4421106140400a445080c01c807140c0d04030070344001010040030035a075640308000e1441507005050140403824506101c107030224004008078a815543c1c0070350415517800b0400821001c00918001465540319 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 927383129 1250 927381879 927381893
    0x1060512041b1e06080601030e0a140c0411040f05042c19030f09090c050d020918040f050c09040209060d06110a090f0e070c0213060305012a020604051002071e 70
    0x744074410105c0c2015002a410303501a0040c1005010b41b0809810106030f40e5445d0a280c004000c1a1409841101c0c0420500e8507a485840800c00701c0c8001151102d01e090038584044c0301c10340200c3d0140c2e090040741c43c5c1481c00303030070b05090340e140020784413841960304841c4918040b80c00540e8040784002017003960526030044241c5500016984e9a8500c4a441d055007a003591015400540081c400b080041c030381242582c0540803049004000e40162004001d0340782d52060160703000e071281002901d0080401c80e08100c104803044041d10304031102e180940020b100c50388024a098041d4442d440ca040405c40268450800102101c102586414100e01e00901b404118024011200c0d02c8950100b844049000e45900c80c4d0318030f551300448003010703909016040d901019001030311500d6120200000d507081c0640600c100c00889001c051248180e14150300000304400501907400403014800480c8020540000094000134056942d0006182c5a410340c8001c40d0b0114008051a851204200d80b03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 927384379 1250 927383129 927383189
    0x4090c0311031c110c0a030302010e06070c050d03020a03090c090506010e0103050103080d091401060605180f030d140c07030807020301140c0d09210905030601060512041b 75
    0x181c0c1d0120030040c0329405250740c0d0820703040d89060b1500c2e0207480301c08062103038100c101200c0700b075010340b0550782c2c500c00031510540d441d800450160351124002116124100074807584050b9038500080c400100c4d482c2da5445020701c1003104105030f00003e2504096009800c5100c0c0960701c80e6103051542d1b42c590700040186015140300f80010300e0600411269803083c007031139050b0394103c0e040514014480300108010310054808803001c6116080107100b4400a1041c0e000a14141d00c6165540f00c10000d66440c420900c80c0f6184126901041c01d403d036100055a401503d116051080d59000d10481b507885502a541d480301040c41030110210401001c40d0281c99224401d40007030000001068208134500e01c11144030f40c4424082c0500820034015800503076042d40a03a011100301c121800c144103c1c1c000700a6a03001081855100700b00a09041180c14010038907803816504000442c00c00040b000c9002d000580050f80003070f100ba055426a504072030061520500804015450440c14904600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 927385629 1250 927384379 927384383
    0x170c030705060708160c17161d0a11040b04030f0b0c07020d11010315081c050412081308070e0907140a052202030a0603051b1f0c0204090c03 62
    0x20040d0008990416005941c8071a44c040065400d06455004500910306a5138007a1a031b00320400d4001140f0240c011001d80d4510020042d085030384032940c05409040340c90344407140e10145506800000c0721000d134210740180e400d0b90003080070481026108004e00454000e82c0211800103000420410b000d00f2203078100740304808440341e03580c441660381190b000302c800203500700c04000881800682000b050380940d40c41410006802c0e0a480700744181e98415400c08459640f1060128246044401600d803507204d651403c24605420001c14000814150b0f078001d001c044003186040d016000c0b2900900900102e00441300c1417039031101d403040545030a964802440c0241c040100705155515165420316001500c0c034180146444240904902102440c00d1070341103130110049000c0c4c1500096000c0c4c007000d0404603280d41941049403c2041c1e501032503000c01e460758405416600e031081050950301d96455165403540c00a0f100307032420002d024009512a20b000642000c104662042d8000d030f0b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 927386879 1250 927385629 927385633
    0x90f0d02010c0909021207050304030c0c060806010e0321250605010f08030c0a0321050c091305150d020d0503030c0301030c090e0a0b07030908041d070216061206170c03 74
    0x10b0307441503004202c1c8205021a0403400d1400c0010340350314019001180c01c078bc480d282c140c6508540352500e440c2941d07160400000503004005004440d81d01110f00d13080b50f00d00f00d01800c0182c0011b1860340131110b2055540c00c0e100c03404101040007032806031140e00c00c01c1c0c0801c1e40503000c0c211483c0560080c0b0090080107451b142d003002c0450241e0001050b22030401038440100a103a0907a00c003a00e019890062086002e22a20381010007010306018580c00344114003181604c800e04e002c00c01001c062021a009982c3c0e00d00401c0107004941c18605984200003920b49440b44401030000c180d110b030544901070518400001481003041ca4000114122400b51001c09a41900d0389442815150381c81400c204a40c40440114082038190040640201c442d080018014245039100801c94200c0d6000c00c03a07106010003842172003044010080c0d8800c03060310181968861b502480c2100481070701903c020014490044030062030903a00c0328015000c80101c0e41ea2150312075071495a0fa20003100c040b070082c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 927388129 1250 927386879 927386897
    0xe04050c0901061b110616030f08060102010b0d150204080d020d031a030307020906030f100504020a15020307030518060d02191d06030a11130f0f0308040e090f0d02010c 74
    0x55403040403c1441d03407a101c9040d04c2d40d208140c40e0488452a000c41456110304204608003c2000d00d100704944503200784c41d40d00d01c02c554800c025100070300084c1454156418008041405d41d02c0481d502c008591107010207040350243d00071000240695080b0f48018480d00024855454000880011418907a41c041c82519100c070703111076520f0b008007412a003680c02801101c1c01850201c51803640444054101ca01d1482c0342a50189010842d6255605890f920800e21095003000c0409002070a103004252503c0c09221030029130345d100b0050054100300b40401e00609424004003071030b891100013480030b0780b1108030345005002903100c5030b40b10104500c0f00901da0480382c007402001206407184030f003200341055a40140152640010406000c265031600c603011002c5c0004017600e103903242d0a000c64003207410f109902280d0201a00140c1011101e0401000000e4000040f40c0030703502003120010741c90322001541c0307103400709105d440c2c080307809030030b07040c05e000d95055001042c41500c540d15450700e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 927389379 1250 927388129 927388139
    0x130807060c030801061d06030c0a180608061c170d0f0506090c0a02190f020a0b070b2d09010221090319050d050901140c030f04020f010203040e04050c0901 68
    0x40c10203889000340810f01120041003c240203440d8920001c0d88688a1500409104009166580120b81081c0b00c1c102c0401c00300a01c65025030154120030142c001c13042c049084c5800501542d0008010034070030361603403803800120181d60428040060340071614892045156003111425080340e0301540070145404901400c3c0c1c2c150740500307400342d80d002d043e42e400303515070b903003c4d881c0c40c1c0c4685c24040a604c181c5e40300d0259400e1502c0310f030301424003860f820010001d0510400c0001029680701a44040c0180216004140550041900800004010b400802d007a808001b102c407650019129001413a508012200307030190001c00f150700c023061580c980140961500c421100c0151503da8903a4001c0c0710040c4880c00700c500c20006203005050060410301c406001900384d0701f0840e041c8486d65144c11003a50250344e01c0c2000740e002a405200305046180400c24030b0b08203072008102900c40c1c01c82c01e40c060480c3e4020702c101d40241502e01040305540c501801d10550313881e400b1501700c0c0146c0400000103a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 927390629 1250 927389379 927389387
    0xc30020d0f08040b0a12200c07180b1908190c05030d0c0303051b09190509040305090112060308031504110c0604020306060102150711010627060530010e0313080706 72
    0xc41180c2d8107d03400b0071080100800b680c540040320f62101c0d900c1b030301e5000f245584000540e42c5908404a80101d4a408801d05010310b045400d2a00301c0d0101c500c0d46c05215080c0081070308810060045004d03c561111400c0c4040b4003803255000c40d4050142c51a40078042d50301c104400d41c554040c0c1c50034002a00c44401c01450400c603200c82007034804084c8481c039100d29011030340c07010f050494610f10651948030000600c400005503811400304100151f10201303560072943c814075145d0b00040c2000602d00e19140e41c81030f480001e10208014180394000c079660b66448d8014440c248030f00e00e0a540720700040100343d80c0c070681510164424406d0b40c0002c3d60319071000a00c0c813103c0060b900715150980b05c020094440711540c0d8074078003043d5240c0002040d40440c100554040100d8506010300c00000d03400b1010850700e45402c003e005034541c0c04040c4040008002c219264040c900d005011201a411080c0c01444010301d0310101e0b001c0054400c0d4a998080c000d001601c00d00350aa0f2055685c50a05403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 927391879 1250 927390629 927390641
    0x3030c0312060301061a04150203040e01060c0f050115081632090a0f2004060507030c06060b030105010809010207230f07030c30020d0f08040b0a12 65
    0x1245a84100403252510351030000203508094007800120702d00b6220030300101c4c10055282d0000c0d40b06d502140401005400824501c080303240341c0003540c41c06041c0819100c080c4014000d44003031110a4001800f0054140305890701a500107008001c0c500d440694103c0040e294419503500b442104d4150414440503600314049840000303500c0142903207150100c1d50310000b4000c040e04176040110b80d401d50b49a610107188034503c1c008000800e0089400b800c41100c2500c1e12800050002c600038400c03424600d0125004d5450505146e80c030b03404070346000c40d41c4221400006000b60f080c424009100360809000c1e6058540988910020b555101030040c00c078014004094252300080c61454080c284075284511034082c3c40c0155450601c21145036440c200c03072540b04079041095203c080002d008846102d441c01000642e2100c1c1c6580c25101b01ca14a14003050080d21801c07102e00719500304560101d1f21025268014256602e869584070301c621036401c5400d4042c0402c0e08101100040500b5200390 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 927393129 1250 927391879 927391897
    0xc03020a0803091e0f160f1403031905120a09032c0d140d0206041a04060b06030f041e02130c05190909380102010b060720030109080a1107030606081b0303 68
    0x9110000d240c6004003500c01c100400e809e41500080012645218810220f401c414a65488051307441c80f107034440025114004200c1c506580c42c140701180026071054030000c2c1e0302c004840e5050321100d01d6001030050030f42c0f1204c03558080045e02d00f0504019400b90034248401081d01a0b13488001082016600c0301c40450b0000c2220583da1075203892000201145900203000381c900041000242c40424a0381e4400d44d11880d000061000300000c001c0020b4281c48860041402071a01c1707480c0da40400e0312119283c00d078040440e103400a1815070b602c60001d907103080160b010440c200300b2281e88050020782460080e120b403a402e0001a000c5000c4804100302000346c0503d071075210714550041c0d803a01d844c1030007999046540b00d120000195584801421046004401d00420004181084501c2805269680340246d041481220109140c2e00554a4010450030700c0300106044299050800c103032500000c0883c0c0c40d002012500c61000158545540328203503045049007021820159240508400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 927394379 1250 927393129 927393149
    0x90a060207031a070f030f0b04021b1209101d060f04030506130c05040c02070306060807090e0a030e0d2906120c0a0605090a0909210c03020a0803091e0f16 68
    0x719103146480b0354482000b009410000007291341c80c8000041c01c1c2e074040c2d0360721084c2d0016001d07100303280d0b141331120003110707490030712168a46840000401c80200d8150340e51011b2100c0500c103c1c0c6034a00c1011000c10703005c03004141a41c0e03480e1400b40b000c2036401900081d81c0d00d00c40c2e01300180d10800c21030103022040da040040b504074070f482c0100300700c05001001030300c1c030840c015900000005807a40c010784014000c0900034000003807c0003090411241100f01d491400d07840035900c3c0002c80e4120400b01748680341502c120001c0351890404032903580c3c40c02c1c040c18009880c501c808045402da140601d003c0c14081740c80380508203078800020b550b01c00280000750702107041041080341c540a00300074110110044c01d201e828079910071000080700c400d007400b913412145800000c08110300c94402040003901a040c03144a40e12191402550303035445140c02810070780b0010218010450410036201c1074000c0e000f00c0703107902c15103d003116150843c0c5d1701c00300150b1003207140c00b803007515889112400b6201e0140c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 927395629 1250 927394379 927394397
    0x6260607051c150b0d0b0109050d022112040608010e1b03060109031e030f170c09010c0f0515011203081506121f14060a0311090a060207031a07 63
    0x1c0c070700b841620030009180d165030700c511111510040c00c41c50402048250607041d03d80004410a40581e0303a002c80c0b540c1004a4098180460b55510301b03120401d640540e4003c0307052000229120744814020244007441c46041e584410a10040b401070050b2202d956503003060b44d070395401c104100e030015076040b44102460800d032500e80840a000e960304c44414034290301c4071075030386d00c0c0d1520043c01d00c00340039028100e44c42c040c0306240e00024448244481454001031407090941391310b41115019107880c001d10350028503240c81e6803180801d6901c0a4220034540544c0d50145007143d40d4084076408403880c41003020000903541500e01c0410038140e01511800b8072603a562805125103c0405200f5600160521100d0482a03041200600c0360203504441c00954640000c0c031082d0112960100b8005000c00c01441d04680720701043c0e0b0a001010304000c5003901d503101c100f801900610b008140c2203680102c0002e903443e80040c4d0802224045c4681e0a2200390541c1510b1403060219a80b0000c16240301c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 927396879 1250 927395629 927395647
    0x30c0e030a1e08270109210302071203030f0b010e10050319020d020306090f1e1009060e07090f0f14040605030303070c2a0501181e05191a07020a090626060705 70
    0x51f003024080d0b4032a01c1500c212580300d12050011822080066002a0b42d4500c4404141c03001c6c4078011444d803007401c140078442580400a00c10036050f4480408000004c008a00030000c43e564200c604104407906645482e0f8800c14280290401c5803030720b11983d4004082486c020460420b180162841c1b1200c4a0106d146008801140005800503654000c12440002c0f281c2d0306101d030a024103803862942070b082c01c04000041c0840000e4206038000c0020031410040e00c0e00d24a503010031502c04054107030b4042d08400004004103141d5000a405000000800561715440f401a5021034071518800c0030703075240d00c00365007481500103001400e81c0e210020144565801000c000c0650283d210115428903100e4030029840f8500803205100c0d010001e000b0301192a200039803100c2405900c62649900340703049509228034003d00304942e0203500000d020010b40d01d559110030081c04036144244001c503500c0198039100c9194070690050740300074940352411201c0200c2d006015007090381c1c40a081601030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 927398129 1250 927396879 927396929
    0x1504020f190207060908060108060424110a12060e06120a05010e01092a3809091608040b15041a01030c0e030a1e08270109 54
    0x1400c0003032038402070003424840c084038105a824080700c0d40c0600724a0340b800c40003900010003500040d0040d08100010304c0a0100000e200342e1260f00710f0f18682d2074100900d001940410b0b406041c041c4142040800707007030350641400800c0c44040c603039144070016100b04990317800c0351228041c00b885a6603400124400d0301e080c002c0b184000300c41c00b094441c2540c066030b62608445110b00d6000441c0d4494040f202030003c0b940340001d250055440b2010069003c0e0803186410202e4094102c100402d04240450540000396190041801c000e0700c940c198031034440c00e010ba4000c415820300c50003c12000807a01c003a07540c44c1e40015071132915049a81e44072a85c500500782030003007000400a0703901a02c04510f58603400340c03854041e128140500400040700c00141661403a00c256014090119030010090318001384440c00e403500005059920013103021020102d803a000e07000740103544c0208050706603051000f01907000c54401e50500c10f80c1b4460000540e410640d92140350031004603490009140200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 927399379 1250 927398129 927398137
    0xf021009060b130510060c08030610110717061e0a0b1c030e030d0203041d100b040f08010b0a0e0f090703051f050901050f0103020d0602040e070e18150402 68
    0x3041c6408502844010003180101c0091109240e03001d48800c1840b120030031132000382e00030300780520300b04602c0c01450f01c905c003403480041d240341d0143c004000e0706000346108038118082c038a026401d0b225859907600402c400950354264410b020300465001c40c1020200d220b56182010341c0071004003c0380d0b29158240000c100300459590880c1d6040a0034005810b5080824110f0703100c1c1e16121070003209801814901503401135a0001d65104004c144001d510100758614208a4684815415070392204290044210380d0302c9655502d40108010802c074080c00501c0c0280c540100003000428640e5042241e852128032507102072003a020046150191140060340d4131403001000c480c1e501c0d560b941d40e01d00d001b1542039101e1154004140d502d0500c80f040c05001c1e007005071a0002d210341e00f40202154454001840001d01c90420070980108105103a0161401455107200b0780c48030345040100a00a5425021028821074204804040d011108010140655002c04510082007451350500000303500c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 927400629 1250 927399379 927399383
    0xf12070315020c070603091a06090604020904090602070c030b10030c12051501030602090a08031e0307020f0d0f080717061009050303040f170708060703021602030f06090c010f021009 80
    0x5000c00c2021503d150822481009094581c0e0004042d100c500300002841903480300707141c190581ca810702a030740c1e5856a2032904100e040b038006030b5900d02d1800040041c03880c1207004104900105140052007414483e00702100d01956404070207a460b449083c5002101c2d020040c096680360800384480c0c454411a0aa402d100740100c0d0552880f0f01202c40090000b6030048610680008240c00c240c1014000b01d0b0060050790002c5081040c001c0c0001d08481d007903a0309607110700e80400003070415403081004110f00c1c0051400d54505c0026000e0052002e00103040700008100c05401241740c0c244030310100c0e000100e074040035164949070b40003003020301013030100c6450421615860114469809200a00040030500d1070162000d180c0f5040354000200c01402d000d41d60400c140400c08260701007015540720009280060307640e00b01d060614040e10300340e000603400d4418021550707203540e00055103e0103070001d01c7c00c0341c2e81c20b4001001100e042d02a2510903005811208003000d030170309580c000d044814 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 927401879 1250 927400629 927400631
    0x60c020f061201051507050304090c05091203190804321203040c090908040b03100909060207063e09090403120f05040305030f09120a02010b0f12070315 67
    0x902a00000301c558110031100c222400d8500700401c064680306a801e18081c104030b80302401d044582d20354030b4903405903100c0c83d03040795210886052010712a80440e9000302c8024200046509041212030396900604d2104013408850001c8003400744c01011045d104030b51010741008008400d80c000346c203601c0c20449001403a0101d002c50003490700d05124490445100d028000c0d03c0b4602400c100b15880e04603400394040510345002d920102c0c40810448060300d46881c0965a02e40314040540e00e210b200394094902c2926002c001001c000f059002450340703034010b00c010303c114139209220b8030001d1a8800900e10f4038030012500c00c01d03907001203a11990095030404903810400e0b04402318880c42c2c002c580c00c40020368001000038403d56180b10302103840350700000070440e0f442c0c50b6030b01500718030010b0300c02e40044610034000b0303802c844100600d180c21410030081c19112265084080e0117004010503c84c89201500c0b414400c44c1014030742003200040c140000c206d00f51460b16422517004d10020066681 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 927403129 1250 927401879 927401899
    0x10e130905100539090d0507090603060515030705031e0a061b020d050406020714031903181a0a0c02120d020d030c260c1303300504060c02 61
    0x7200d03c03801d0b04c10480c2c1103550310b40860008107030101456200c82c000c040c22030000ea4244582da0705080c0c0340f401e00c0c16070300d5504c0d5110700d0402501c1c0c5412980b00141d2541005000700401403107401c0b090085403149160082c0b007041408060700d40c036480c0101c43e0960701443c240c10700c06404141460380c004523402914145101516404191003801b03140c40c441d80030301d10600c0205581000b20b03240d010701600e405400d0900f461402920780c0c10744e00c00d060910280032042e1b4090355092090003500c50041c21404943e03001c624016000d890314600840d00d500c20b0726130010745000c260b031140c0140310751107000600e801001003050f03d0717040f10118280d8000c10b00c01101c0100c14010000d10003001044d400030507500f906150010261a202001e80c400c104e02c0000f859003c241c82c08401c0c0c6540306085030340c0c990341d0300d018407100c00740150340b0b01003011143c01c80c0010501034884070000e014451003901e10300030710b00c0001c00352a40b0201c5d040e40d00010f00030003041002a1195000300d4549100400010003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 927404379 1250 927403129 927403153
    0x20d140f0403140307050c190b0a050d1d0f24090102070803040501050a050a1107030f020c0a0609080d1713050c09040813140312090d0812070905010e130905 69
    0x782000d25480f002070744000740f400705002c1700300b08507825030008030388410002e040d03680340b4100103a080c42000501d50020511015a600a80070740b611620601c00402800582c40000c0c0301002c007280743c2100d44d00807489080000240412680503d030050301d014003c440c120341d05200308580003480d41d034043d5401d0281c08000703502c0b0f50055000314000d00002c18541402885070044407405456618100e1800110030200c00c810302c00e446469406046c5405029107211090341410203003248294805240400401c4903500085c9501c1550300f031034112501c9490b441e00c00c1d113000511590140d0314003034884c0010b24688001006201c1c81c0d00c100c05640c0c0601c3d103070010a800102c191000c031100f903808201e07000c103081d5595400009208000c0010260000d08001c60785554055000c1154901c001444c02d07100e440d849a40703a4050f5000c4370007947c0354080d10f5140002c076815112503002420442000549612401e15000035220040040132445020a01000244a44041150540600c122042d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 927405629 1250 927404379 927404393
    0x10504062309030f100b1c030e0a05040615081005030a150b0603040c0503010c090303121802090406150f180c21020309070e130f1b08100b01020d140f0403 68
    0x1c0300c10344c0c0000c00c0700c0a40780742c001080d41c0f032118201d40503207018507040ca24109200640d0007120f4060500b10064082e01c0046a03810302c0c01c0c3c00458009003044400903220340c444540081c031081c10b07515207050b61104e031040b0007541e10314402c2503819032081b0110b50226448d407844420f1580b101e0700001300740c000032011840540040701c06568680803140108920308081c09501814405460401490360850341c0280c0003203162000500c20650b02c4100010090034a041403070180e030000e0902960345018504000504980c0822150f44491b80c10005220750102d50540e003a180c1840000c45410b0501803c003001388403007100030082240714044000040c18080701000b00ca41846805603403454100050b07880c006055101c81d205181a00400680d111000303124420039a00410701404902c1e01c0c1040c0803103844403007002c0104980710100243c080d600182000f00c0c044465018000c0074004001681c994284190f40800b18480d491040404a500d800411061050701030513804e280e240d4699030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 927406879 1250 927405629 927405643
    0xc0306060d1406010909021c0f020706110a090f060f050304081b33190624030c05070201020d03050a06080f150f0115050a14030915010501050406230903 67
    0x1040c610410b040c400300e07590005c6541c002e01080b10b0258680403013072003080c0235564284184580c0540c0d81d4600030381709203250122002541c00000038040704000c55502c3c0b51507480415040302246911074002900214141114115100794881241d51942040c00f60751076032000784210303000f11080240c0141881c101650b042e07080c40040003000c8007601e490070840b0000301d410400780388506220b80b911460910050710b541c407401c03400301da8142591070400280034100c82d8000a105c40c3c100d03a06c8104010500d06c07a2402c04034070355000d10400e0b00100058801c5d1080050203070058204080b2442568007a8014070b8014088a0300068400e0f42c45001c41c1c202000746074000704540049080310400070102c249160880c1d008110790b02c880d4900b850000c00244503459580a101c8003264000c002802212045410707401c40d12a00e0382ca01c3c3c8141115107a00291840e0403050707401030000b141c15403080c0107407070564003942c40d44400e0f0f1079440c0843d504950700f9600c1300142c0380100045102c030b0b2001d100309 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 927408129 1250 927406879 927406901
    0x250509060412030509100e0a0506090a03121706011b020402160b0109090c140d020108040f0206040b0309010c030c0503070c21020105160513260f030309010b03010506090c0306060d 79
    0x1130b6032a038007035004001c62160b01007a5035040090710455181c0b036541d1f5040f0117084a0040701c0440d550752007000491203164180d40040e140298041c03e50096a4100040212400354850341d6000c584e100c1c401034030b2620711005502c005901d000d090728014102580182052103003c0811219018980d41d101400c04d0260480300340c0a807640a400704200010043d40060304c130484030762001513212008104059801140681003000d81400f0030b05000010b01001c11040d0081c0c0685d98568480d01c1c0180541d10681c0d03040d10940c600302c10522064803e02c210340b50002103a449070303d561203101c012160070280920030b0307610310181e50311405a818024040c0d1090b560940002c25285407c10740394240c00320304c0d40c804c801e0010800001010b102540c08400503a80c040d10404d1088007803294055800192038070701c49032440f0700010a40c08480000246210700a040c0080c0a070112540a15007600c0003070300c5140e00000ea8202240351404504040e6a12450203408131f401c001c400c0203050140c0c0c96081003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 927409379 1250 927408129 927408137
    0x60606020c19080d05280e0a090506010815011202070b0412080c040603021305030a03030506042f0c010207050d0c030e09040308150a0f060504090525050906041203 72
    0x1a14142c14001540d800e504144440c0041003840e00c0006500c5410f1038050307000b042400900100d081d241c85032400c51280d000340300740d02d00700c04843e0046c1c524580a03100743e1164a00350000259283e003806014400c2c0700681d545681ca4460740141011045c204c4491814048a01c1c1c8040701d000503840580710b40c80c09510cd44149081604202c0c1c180501148500c08000801d0104084c5e180718200701c4080341d1305860010b0741d075201d48034250340170700c2d043d0000c95150140c88460b45c289a41604603d00540048800f04810a4140018400c00516040051340880016004501406002d024220034101c0c20b00240c41c001b5156a00c2c0c0c00d1600304100c00001ca44245503032014141e00c00700c00c0e42241c605580700383d49030426407030207469201d0003000d0084c0881000d0309600680c070b4081e0180010282c0d001c0d01c4405548404000e0481d4005000c1d0b460007901e464002800d51803501e0720300041908440100460040345001181c19500440300e640c0c22001c10040002d807142080c003001100380c007a0356 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 927410629 1250 927409379 927409393
    0x50319060e2b020c0102150709050d0506071d2103040b07050a0b0f0606072a152d0f0513320120010603050607020105061c08070b1306060602 62
    0x2000d19030100c01c01440b0011940b0101c449012641c0018001d40d150b4180e0300500c002e591941c000316442d1980c1d03001180c008907826450b00030400000b504a0065000d601d0341811a80c04a05a41f0502030a101d010703400444000201000e28502c0031281425440c08282c91800703856000143c2d85c0d41c8040005c0310380740e0200e804134041c85a01100c26400c4600031000c0740d0700342080c5001403524000c1c000003908503005501010b40e40d00030030f1003004c00c000e502694003070041e5943e44584400c580b1580d0309070200e46000c0c101400f000c4a03513015520342020380e11141d0030084001b011904440501500c0c0144202000300c001f100d11500d00b02401401030002c00030707229aa4185e1040c0440c0004490880c244d030380110b0300c07072030b0ba002440711541c41d9408680c2054440d0440850b400340c00f16a1000e011030040c542481020340c0e040d08000d200d00c2050707034204810311054110441025004001034420182840740740d0020742800c031200e800c01400308400d074001002e40c4903d0110f51141c0d00050242e84100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 927411879 1250 927410629 927410683
    0x305031503010504150f0f1d120f0306060c0c10020106080f07080706230408060703061e090203220c031a371a130e0c060703030e0f160b04050319060e 66
    0x3a9155027a1160011820314509481490440c000549039910603000480c1c102c0100c40100031070001c5e0740c0010035582c02c0811405010b07000304998080d100c03142c060303ca40041c000100040781000c07114a0002000316500e802022a04107104002ea28441030280020107040414040500040d00142d0b0250842d0704011401800700c43d2240c0c00300c1d0461071903540d025083c10a00c188003003102c1034401c003d80d4a0703075066a04024240f03126030440002511804010a0001010580041d81d00c1107a180d1040d501c12a45c80c0d010070000c407403003c40100745504404100350003200d0300741c40b842408402194a4240844941903071110700039002c1c01300c4042c90346400d030318040c4010090804100c038104035900c5071908242d103c440c3c0c01041402241c001540700d04041c8a94042042c200b010415912a10f070f1140c4482e44071000c20880d09181c1000100119410400c2c00854088801c010010300c081d0809141818152541860650300036a4800a10201c000c0902c40302100d0081c0c40c4180503454119 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 927413129 1250 927411879 927411883
    0x4141905011b030605030a061a04020408010902040b09090a2a0602010506030c1e040b0a08120406080703051e07120519150806010315090804030305031503010504150f0f1d 75
    0x12548504050502d00204080c2e02c007c03400742c3c030498100c100412004800c20a4055580c958a00c3c0d5400910006c2c6c005040700741984001d00841c42114284514441d04007001404034013030b01c2181081d081414880001100c15500302c41c501803111080c50841c07102c0d8070b041c448066540c003200c0541d4482e01040160714092000d86c0c00c802d42260403461810191b00c9440340c4c52141c0c24403901542d5201044585940c64241c03410060400108543c1c890030a0740340b40002e90024070801011980502c0815003142c024020320b03102c0c0d01d030240c0610819401c420f60001c0204040c14107424090000240e42c070416950160718410702c018102100b100b90800003900813102d07120041100e286e0721080030b119400000c6005070440c0e4100b01c0104901404d01d0560b0020200301500a203071b038400150000425070401c000d1840742c0c580c125402c8103c0c20ba0b40c2130501b2384004440c014250708400c07241c2d6680200e250b100300c5c106500024000f800000b0701203004204c1d50800413030b1540181d142000c403945081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 927414379 1250 927413129 927413171
    0x11707080d032a02032a0307051f0e0613020d05010e06060102070e251701080601060e06210702010b030609061f0b070204020d0902030d030501030b070c0b0414190501 73
    0x1c8001600c800b1898000003d44078065060445c0108130300ca503140d412100e8001054402d82001c0d1b00740c0e130303403007980d03151080d80c4445004003004c0240d09242107240f4039109118034122100c024003d0b044035900d46400d81c0b44400d1112040340d101c25140800e1700407030320034801c01c07a00000c440014209410110006890401158400404072010f00e04000c04009a6148410012510000723502031000021050711070440703203a034170700200b041c1c5e0000192201002452034100d45441d2520400c4801d0102400341030b2040c86440204d0440815105100c0071b842010554807102c00e100010300700748603100007400c1806c2501d4403511584240c0910890b12140d4080c0c1c0708600d00d10410300d00e8180340c450160040c0c011050060b210315400704880750720080d20303089010000d030f008055940d2140843c40207402050300b80810342e03001c1d00020001c0c6000e400380e00050303034880c0c000400548507a155a02c02c80c80140101c0c0806450050000460380551207408010400380b20700c0000c10f1038080403a000900c044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 927415629 1250 927414379 927414431
    0x11030a090b0132010e060c012c0c0d0213140a050604060f0314070e0106050703020c01091412121b300307110d110106050405040b011707080d03 63
    0x10401d4480020030a1140e4215194003200203080d40f010319006a525408a6000c00e800100005e1600030101d010b600c0b04200f414010003225604140d5159031841031084920020340d94402823048070240f52060280d0900c910083c040003a202940810109640810402c403940540000602c803c0300100d010345540b00c0425981041914909040072400d0549032001400b46030100740c0340c1d0036200d014070100b0044c00030702d0140c01e01035a59100c020101d900c07995080e0014041c0924050b0558454005d10302202c1483d129003001100386010800203105070040c0441c40d10507159180c01110500c009007008800060095203078a00007000d26052624020380b544441008e80790070203200c1c54800445822180e00d805858583d59008419900914504200001b038400d0001d0413154661100031551184100b01c000d211a59403401031005503401542c004101e0b18070f035070060180d16619000c55404801c0001100c0f60607564032035440c00d01c0380400307818000136111100000c1c01c06040c81580e0040c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 927416879 1250 927415629 927415649
    0x303080a0207020a1a0f1206010f030923010b030d02031b0706050a050d02120415060b030907031b0306180b0f060d02090a0b12011d0607020a0b040611030a090b01 71
    0x602c6500181202a5038000c41600582554059180389101016a4031041d5140078140c4e48010001c8400e411884c1155030500044410740c54000007442806401c48003035024010440384c10010110149001040c00201c3c0300d0f40d6200d080050982c2e040244940c910400d030051580c0b110b0911000441900c6409001711950043c1c008004880c3d01004503444052940360444d26035000c2c58050300a44142c0121103207070040c2030180024019040c0210107010034841040000325602c00700c48a25002c1250b40e2034660300940410800b240102e0292030b0340000d0301d06030390001a226075a002c101c0f6507810300d20261038443d04901003080f242c1e2440715000364558103a44220302d0624002042c0741c00c41140280503080f0038020500001c4140c1001d0701ea044020100380070031a80c000c489000340001070500c0da82585c5c01d110000005400316a06005005c66070140000100d030351519401d921002e803003211641e564400c01d0100c003440c0d9010b1030203510f010001180f985041d0805040c50074043c0c01101180f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 927418129 1250 927416879 927416887
    0x1020a021203090d1109061017060d02090a0e010e150c070201230d0c0903052d1915060303080703091a04080a120216020904020604080105160f080c03012612040303080a02 75
    0x51600113035041100c4140307204000272035940e607010070700c40208040000e420030340c04028003180c00d140d03800055103540e040d00200294203400c0c00ca156103407000c00d40542e030a0a04c00200e12545022002461501c0c0181402149100728071070800c410100d05000080034003003c114040100404e002d554000b9000c2d14100304102d040d0303115241c940c0010300680300b05920400940f98500eaa801e2004600d104071400d441d00704505050280540c00110003c0700c41c04503d68601c84001c50b94030a12042c5da405a4403142c1c50303641c884003a00201f801038002d0300d00d103480c40b0303034500c2010030100700c28032903842245500c2c0c40c1c05036218064a01580d008120030070900603c0103a9591440b01c08080e003442c3c040b10042c0f9141c4a5002084480c131494000c080103501b44006c1240d44125405003110700c100c81d540d42d46904807002000c036803031141030718540b54504040004002c0e00c030f4007107101d24040407002d13024085201480c0714680791000368606940100382c041170820605420044080c0c1c4034100030025450 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 927419379 1250 927418129 927418159
    0x10b0a06090609240e2409130c0507020904050703061a090717131401060b0316020705150c011e060807060315060f05040f08030301050a090b01020a021203090d110906 73
    0x13440b990b009500b000c200207010010420341d40c400c021040440208034454004100d0369885441c0e5201c9a2594090b0b07075444045401e1074120b1199030300c104d070107540700760514140368200502308401070130a4816210700b541c0800401c001d841280010004203a4042422007508180661690000c103030f4014001000156000c5400300c8000340d070310000c1c1c1c441e400b0300900a450600e501404042100c070075586030150100d06188030500440c020707015440803494400c41000102c0c2e9031244e60080680200c3c1d140031310a400080a009058034400301e03000400c001011824014541b04080003800505880c1d03039040140c0715041c0000b030042c204a103007d210200031202450318107804c0b88618002c0115000ea40c0321414421025940580715049041c031449a40c1c00080d540d9402c2030242d544903400207540002e648080d44248000954180c010781981c501c60307003c001c031004511848a60900040104080550b60082c054184900c01c1c0805061581018140041c02e4030041000340211384007162105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 927420629 1250 927419379 927419429
    0x70b0609100315060314060a180809040b0a122a1412030f0a030608010b0907121a0d03020a051c14090103060b2106010513030b09010b0a06090609 64
    0x3041d607420403a040003000358804504001c018551001c3c06d00f03441711407030b0300c8204004188107025446814060040b00701c0010310303a241c0c00040390020158401013040384d4050406401078003460714000e1411114503074980101c0c4c4440c0b00c401c41115010841c1003003210390303181522290940c0d015900c1c0c8101d582d09242100c5210074044024902c20522110211403c803000c000321881543d84140e00d98988482900c080c02400081c0220f100e15401c0c0085490315050400d04a80705403116030340d007040c016924a89500030003010016900c00000c02d102c5480c41d4440e9070030025494030a600600514081e400d20500346540c500c2c906842a0b401c10102c9400d5030304c4005a5015104d031102d456a0300e11031401a0020a45a0b1180910b031001054410040015800c05070b404104a065443c003a510840111a10701c100c540f9a81c9480c0540e1040c80800c40c11264075500899001c000110450407000280d41d1010390740c855030000d000840309109640c3e010040c003004041025040c003c100301d01c42601 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 927421879 1250 927420629 927420661
    0x6121605040207110d1b150e0f0f0301240e060f01050307020a0203070b0322020604211e140d020303061c240b120a0206030c0c030f070b0609 62
    0x2074455900400d80c001800b83c004000c1c62078000c000c000c06422126450705a07540340605242001d118414480003032007401c03244000c4440303000741d581c9119048241080020514221150f650807114007100f40d4500d07202481000c5400600c95401610784031440320841d84000c160704100d4021038480e01380511501c405054001840007420070607100e6858074422882c040d00420082d505106140e8001a46945070b40150300803c06111124454800000020551b03441244c000f5005030040004000c0014101d03840072612001001c072182c2070b80e56840c0c0d4411050702c3d2001c0201081042152010001242c4ca1400ca41c450100074044280f00769901035201e010061903a0700a00d5400590801c0804003103168400c5580100510360069100504080d11411100300030582407600e0869800c0c0c1c0740c9901c1c01c65036240c258004062024040e0300780000c9030805000390108590610005500700001d001030b1541d42509503134070382c4400003420001d400160140a160068043d041402001300d030001d004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 927423129 1250 927421879 927421889
    0x190309120302071403030403050703090e0403120f020c01020d061d010e010e0402010302071e021219141c08070e0904120c0203100c0804170c210d02030f061216 70
    0x503141c0c83c0c04d003000014103000b800003414a00000041108064010018001c0907000f035881c52076050300d030403000340303045c03070a80d8054041496900c1c165850560ba40042c0c0740d80400010250610034400906070070f981040b2000c031030303941c1c44100601c64547d00e4091343c400340480401e24051545880e104403540d03035041c09000e00c0c0030030f1440003c0559020350119500a80c0c0443c0a1007003903880d1400720b0861400120807031041180c400961030010700060043c284d80c1c504000d0450f6a91103541d1095002d4000d02305038164011990320039200480321500840c1e0560f41e444180300c51400e4100203040f0100024018031507140c0005100c040b4111104040020310b0608080312003035140d0000030b01e0310452b08400328101d41002900071015038010280ea018034843c040310000140918001d40c081c0c0070b400341d1164541d02c103c80c0b511103402011504001c040750004200d20340710700741250400781d9008858400310b07841004207111392810f01c010341c0b02a14a01c000500310b0b100001d10002a8a0403501c55 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 927424379 1250 927423129 927423131
    0xc0a030908040b16021002120a120603170403060605030a03170603010b1c0506181903090b040f0806070e03060a0902120604030e18070e0108040f12051903091203 71
    0x1200e010002400c003124003070400c000a0300d8841e02d0100e6543d81800d0f01d540200d0241001c400000c18690000840c2c041c0742c80c604410b1400c06003520b8040321a40349178076894141540b40c000001c0411901c11b040c182240608040b26540c5055007420323000c0c1c514a5000c00d020340d20036204040400ea00512640c0780c0c08440c20300d841707d5258403000a0142071028102035209042e000d0035203401a4140010000134404e60951341c465a03140011644c0c0d4520810180da10342060000d072a20030002c10818502170710a081c20500c8a8542400709141d07006a00001c05d07440d4516810300c079402c81041416030020385840d04541c0ea104641c08680c880700040d01046205444c1c800400844d40c42015040c5110303154412900640760904000b012506170000040c05007014800d1282c0030b05a408810344150000e4903205042410000112046000140103440c2c1346242d80da800005a0806130f4a160114039503141e07a05c4040e82c0203000850404d50358030720281840d004100001448481440c0c00b28606824 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 927425629 1250 927424379 927424391
    0x90306071d060a030e060a0c111b0402030702030d0e0105010f0e1b03180a060204051c0f11040e030d140a02070c090213030203060f0703060b0f19030e0d081801050c0a03 74
    0x307054028014040001c000e500914040100032a100c0e0f10008508030183c0c0ca04c0301d0307103a6108800352181c0d8640720b0740b610b5030381040014ad064100b9400445e00243c43c0d00c1241c1c58590300e40c07040750031104a1800d40c11140d450341c0040007580360840401001d80110f10740c041a42c10a1160740402c0e1002d00e0041a031034038040006803049140489201e1f196100f20151150051180b616000a510070b004440c85041001c100c0d440e02e5212440300084c1c158820640300c1074042d55103071900400d8a07050711550043d2641c41001d4903a600340050801c0201000022403101c000c400c0803042c4000c01065800319500c103102c44804503603801e5080007268405240142d45207046424606c050b542900041c1d0140b00d4030007071001c8000c1100c1410b110b084155420056582c480507881810b11401400601008050081408400c400e42c2050084120b034140003a03500c00381d0b00070b40e050407800346d05000403c0c0e041d020482d00d2021810b044d82c0490701e400080203e841c1c00240e41c034070b5000781030503c0e04240d9961 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 927426879 1250 927425629 927425647
    0xf030c0904050f071d070e030a0305031f090b040b013b1f1103040321090503010c090e180a031b06140915190e1002040b090306071d06 59
    0x80141c03450308518006456245444002203503110301d80c0760302a00700a84843c000b03400c00348103007d50707002c5440c000e001e0540c81da80b0351001c94207904084d01c04080941c00014a803040580e50342c4030300007043c10300c0b40800c40c03c150004000031101c0500a9078103102510303003c1088100000c803240c290540980460240000310007100c4020254000a41d80040c03406c1e804000314141169802141c0c0c459075241c0d60f40340d0764861015100d01842c4801008080d6440c4000581c1000002041400b8a10700e03100410136a1940001d0035116400d082c41c000c105004018044115103000440d400050807214518010240300d01c540d5801c801080603040140e130700f100c0e60000103000c0c0c0d84260213400400c00d01c20204ca00300caa10102070140d0320310042748560b8410750046504002d0305131203000c0754a03190540498044c410030140032080004ac0246c018002c0c0f1588a244510103400a4080d00e08807503250f59868080c145800700c0500844240b094030204401c0c10b000401c40b043e10301c8000d0f140301e91038200e08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 927428129 1250 927426879 927426883
    0x30c0405010e0606071a040b01082b0f03180b06100311030a09020111010e0106060905030a0b150312030f070e03030c060a0c0c0609050c03120405030a11011e08090c0f030c090405 78
    0x62071041b44500c02440034003080c01010700c40300d4140d03044030096a43d0504914016191100614034045400c150704201207003850142c42c400d6032515031810007140d00e14841c0c030b120240d00480c010444074150010148286801c09034020141402541420080300c5020a41898103010090000750280c2d141e642c59011644a1111590f0356130001c8000d1041c10026001c03035020b00554081d20340054518240061507260010342803006075000380c80080c1e56101c1401840d151503084170016058441d6280715400e00000d00300442c402c1c00002c0300d030309450a2690005110300070000d03440748240e0042c4035031322079103c000c5581c0b90050011100003c1403103005070141c440001042001d0646450003565000b0700c03a0104040c10700ca0021410384100e01601048100180140d02410307400d03511040c910030020300383c0e4008082000050401c51910034046081d40290403c0c1c0c200c541c0028210b1044c014034036010002040c1c1c0c000101d507100701164801002c02c1d510701d41b0756011031051000c035022a05100003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 927429379 1250 927428129 927428153
    0xf0c20040b0d0b091b010e010e12070603060f050d03170406112701090f05060d0e1204090c021207081b010203160206060d02092d0103030905030c0405010e060607 71
    0x101074004520b03501c1c64100301124400c100ca040a050084410790400e225240c90342001840c416122649409920710044603820054440b00350880c036010240506480c0070029000209119600800c2040c104000001022940d9100320b000300317014201080004c0d04500b01031841112b08000d807016694500700b09000d054402c40d400342c0b2400006078003880310442c3c082c00405034a45240d4407201c0c12900011140008a4440d411080103600340511040c035081d0003c2c122550700040100b01c0840300c04000d8100440c80e91000c428240c0060300308000e1000b80100c8a00018030700240c450754540304c1d0b8007003040c8280c01c0010a200c400050b030030f403c00c113031121068490321050000c43d100d1810f05401c2000d1b0341c0d404142005446030380000b034801d01d44031400342c0950b50f0243c00000039481ea04e1003555820903100c00c1c1c1c3c40c00e02c40d41240c0c4000030444104603000314001d0f520410098a01000d040c100007020b00e41c0790142d0b05200c01800f458000b5043c2076041681600d8407681c07003095050210703801603 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 927430629 1250 927429379 927429401
    0x3070c0803070e10080702061e0a0c050903030414120d020d0e0103140907050a0e19090312090507031403161b080717012d0203151f0f0c2004 62
    0x7002070b4041200c1a440321801b8414582c1d41c0803204607465412440c2d021507a20005040c80c0d2008030005800002150860500d90810381401801c0c500100002402e540054002d1454260051b200aa0f64600030510100b000300700400f5066410794510001c1d240c0b08000110418411400d807401d0715070340f00e0380c403006c4110b580086240c02401e00e48612512401d41d40700d100e00c581820680407a0414407003a2981c040c0c4800149099001c07510030680d0041c1128000c203809003c9c81c5d1008403400070103400380650103482080034007003c0341585003012441d803604030140c402d5801484081000c0440000154003a80c00c1002981400746c2c240c0d10401081c403580051985004101c00080c602d8014035034003d042401100034059140040f010810b60907c5503030b0120f00100c4d244a038043d41d02d0b158000d40d0407000c0c0c907440b0304075201310401141515002800614007003042c0078640400700c0d401000e029481b0620324107100c148400b503c0740c41e0119407900600103114401c035040e45103a40c80f0ba20109280d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 927431879 1250 927430629 927430639
    0x905090c0c1f0c1713030905090103052805060402010e060c120702310f09022106010603051611011d2104051e03100f0204091103070c0803070e 63
    0x140303a40000075440d0202c110503056038249550342d200d550040c040c000a10320713600b81d00b0b1059038503501da02c17650030303030401040d000c0c412140c10100300c5880d2007081074065401040200b00001000d01d40c81d02c41c80c01d4003400b01800f03541c4031403140044c0021807041c0c0c21940920b00249401045000107e5901c20a11202c40d14460240146da91841000180c00700354002c135601440400e00b05000d80001a00c080d0144500b54400c8110152442c1c0350320140080e9840c0d0400513a82000360b002c01c006145c0c00c4603803a13503e1190744e0908000502080114054040d07480e040c01a0300700010091741041e4840e1021040c4100040c000002ca03000354014910148610001200030a042441e19194840940070401004030030501c003100052000480d81150300140400c41d45041c804030000f0b280305c90059441d80340c065042d84100c0701e505c60141040c161503e520059460745421100c0d412580b402c201d085c4008400d000300104a5000170001402c29042850030f07940c1e95607046d044644131034490500d5400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 927433129 1250 927431879 927431893
    0x501030612061d06090a03140a09060819060b0417070f090c050c06070c0c0906050f06070501020c06010e06210c0409170c010c080a0203040c17010b0a0801050907060f0905090c0c 78
    0xa64001074411041801f0783c450304031104c41c0c01c08403081c9200c0c2c5032103000403a0030b43c9820460700d0710550110380e010340001c5c15008a00c2c0079078034074401c0e103007d548603020104010a0911500d500d544100c06001c07001c20080c02c100d4a000740f020340300c12a0b8807460440da55125903049059000b003049a000001420a40c0c4151171700d507001410314040d44c182925a410801c401042001c154481e4409650000381900010b4a0440400c5400da12000080321255003d01a040c941402084050b010b014803050315215884c0400500ca03a040e40400960540008102001900e0901040c420b000040030f480220780b42c0403504194000ea41000c2080001220003d62114103010652001d0303599021603540454070b44071085070303006038001503070050040c002580c01049400c9010b600c0e407103d4030b016000456502d04c00300024620588540c0094090703519030b01040100b2000380082e82c06400141856144bc1071162801011042d01d0b0040901a00820780442c40502080054811000d405400c560070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 927434379 1250 927433129 927433141
    0x3230f19060906080c0603130f060e0d02010605040e0102071709060f07080a09150203092404030503180d0c0b0304020d02091303030509030a2307120207030506010501030612061d06 79
    0x80203c1e21401c0b02070f00401c10001039501d0b050007201d008290b141c108000310304181d161030300038809540049500c2c03950b07446000b44424041c02030354580c0c3e14640002508a2820052101740c4090b518640d019900c1040104006280040c1c0c4070074070030114003d281c5815001f0045103051151106154a00001083c80c2c1c0802401c2402800944010b5485041c0b43e07564034502203001e000381004201580051012030041c0c144980032850310000d8940c0c03030009480c015811034280c0d00c9501305540ca034000003910b110050340f40c02800980f031410780d00c1c0e44034845152900c82c1d0380240ea008040b03125000202242c113540e01c800e41c0070203c54008040c0300caa03041200101400070307042c1408070042410600090b032a81d80220954044803100c0c8c480304c0300c1c00721119103518442c00303a40b04156070003c1840a040880e100b104800b00d44610381c0c00502c0c0c40f80c11800e010b80307400416481181018145641405070304034450100c00c0c481c0e8400c0d03004c203140d003103500b441c8044c855a45000080b84601381c10440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 927435629 1250 927434379 927434381
    0x1b020604121a01030209040b0406060302040608030c070b04060e01051602030102030c07051e0d0e0102120c071a040f090209042a1103070c060c05030c060f010603230f190609 76
    0x2140c0704094001c084030507031080c0304079442c0901c00a948200320100103004146580c10301544207101d5000040c130345403a0760018040b00c6a58120346100e50022801001c080c3c1300700440c0014050221559080903e0060010a4a0710f65042a8100100481d861052106664607500002c0c3c1c010005d548034502042610b5154211160039103451240c0d44407111500083d094080c0780c0e0b028980603003000c08030750303000381c0340c05560380c1080c0c3c1103120700300d103140107c0070300130140c5103480c4000f0240c218a4a4144400d4259070302d16050001a84c040104000080091190f04112031200354090b0310b841c0c52308000b400410b01208001c0d40308510040001e0280b1034000c2d20030012603907031078440c00b0b0108982c145549000b0000001c10380c8040f5042031050502803224000c0143c0304400312840c000d58002c44074103205040ea14407500d0011240140851609805031014061041e0b450000141400300c00c1d0030264005401c1289108484011403480c82500c0408a0380608140050003803036610302400c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 927436879 1250 927435629 927435659
    0x60f0412021f08071409031c11060c041e0b18270402040509120f0a1b03080f0604200301052b03050306010e0406060e0117070f1b020604 60
    0x91042d511a1690b021440808005141801596031840340c1035032020000e5400c60b0700600840004002030204441a580410002c0300c80c450300002c0260b001e00b458800386c40f5a40c148945000d54110ba001c101c8444072150640d800c958503041d5407000728a030111002e1403040c07603401c1805144000228149d4000320507840c21603c02d0140ea5104c44e42070780c3d9061181c41c110f442c0c1488910404003001c00c0161070644c00c055044901c507001c4d180195401003803181d940c2c0c00f1101e9210800404510b440844d0340010100c6d41100c1000700041d9840019a00203041c4c903001032000c00c0440c10130000c00d44645803a40404981e40100900e45080c1040d540c07040d0440e0400d1082a01c1010040d021508080c0382c5110021500144203c50360460f0090307809980e1078100603c114108440345490b0308850740c440c000e0034010800c40d111410b020f400030b070004008001c0090f0b480d0a6003182000d010b50981d04c1148502c4492043c5801140d506510800100c403a00c40c60002c0d600140114010a400740805007107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 927438129 1250 927436879 927436883
    0x521091507150506030d0509040e03040617010609050639010f0b0d0203150901090204090602030901050a1a0d1403030a0209120a0b040222050921070c05010e060f0412 73
    0x40d14840903405034002c01d585080358915056044a100b403603195028070081e200381c1200a002044070300c2030b4000240b454003c2c0e413041d000148035402c01c20074100264400c0d800340615140c0320010034200401f01c0c815100e103081c80da14841c5440b800d404e0b081c1120500c0034500c82010101707040441d001c6515400b9000303c020280c030086c5170250715807083c43c00900e0840c0040d400703030260100301080c00394200f05150041c040c00aca9501c0f01c25903001661075101c3d403400148519070050b101c1c00c0c8400c03568216000189032a038014501448841400c4000703c1d520228602103648400c0d9004a00c1c010303c1080040207240311511011041c0248452943c01904034030400385c68102d44203480d51391184d902c803802e4038058180d06085010038090b080ca0007007170114450144c0d500b00700481c185020400c44404a40c01e5010b6000301c070f403410b100010500e40f40a4042c04280c0903081403000d480d081903074101841254188805081c544105840710000d8030300710a0001025522a40e0700c0c02c0704e01c2007004101c01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 927439379 1250 927438129 927438143
    0x10323070b0c0a0b01080d27030b040321022106011403070306030b15040b01020604240207050d0e040b040e120903250f05040e061f08030f04030b010902070521091507 73
    0x1c239116030490756403050340b595141102e00720142d10715281c0c0150394001820550421001006c194031000141c3d00449a0144444d8016518980903980e001d5014074020f050f8182c0310f540c1c0038001941c1c0e010300954044001d000086540752141c2205500074401b65000600c510b10410030020f01072021220001005000d49041c0701103202000120f0304d8140c00c13107000b480700c0e40e5805035100d00340484a54080e00607801d40300502d4888181c49881c9803848560020340010307160400503049040a0003814900c0d0030540d028001d41e040901c0340398455452120300c45010746d02298520310f65900708900c03218405c07501090358040c0004161000c8440060054500c003244c0c034000042e80b4101032007140c2c100180c580217407143c0d07102c4038014200c841010518181402c65110007180707851041c0000d15440c0081d580d0a0398035071452130541e0900d00141c1c0801482c80c03050000001240e40494000c161803a01d141004010020f0095502ca03401000545504010f91208a220728420300d4028405d503801520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 927440629 1250 927439379 927439397
    0xa330305010609090b040b07020c1302070309210204090503041d16080c09010c0c0905010b130506071212060306060303170f0106140c03190503010323070b0c0a0b01080d 74
    0x10039030180c0d85035140042042c40003100146c0491044040381d41c010700301c2e20555104126000000c1c8581d000c80324140d81040d4000f414004040d0020302c200300400380c1591f013044c030300c800b0361070341e1641c84681501901580c1c0b44c0b8040c10410034180100c038054000c003804a01c040581c40081c0d5041c52085a40707a0740f041a000c11180c03902c1c004e070401407051407011401c914282e020001103401d4003021708210303105603480b807002c142d0303407a2405558080e1841030b9000c0c0d03c03210b207541c0000b4141080c1e40564004d10b020090700c400305148140c0140ca2480c2400d121310014149401c28000348240d91010700424030304007020080607403282c105001390544141c0f607802520f503208880c2c10711a00780b003844045004400443d4850383c0100103440f0440c00745054074140507105080c0c00d090b00c08089100c0002e40000018010080218019250001301c00c4403003003241300e01c1501659941690080005080c00800c1104031080200b10300071613a6030142e540d280b00c0d691116125a5605040308034008180200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 927441879 1250 927440629 927440639
    0x70302030408030103120c06110a030b0f06180307090905100606030516081b0304060504021f050409050a1b03060501080a0b0a0e09150709032001080a3303050106 71
    0x100030340780640c0e0880000c80c5143d18684c1c0d07040800704003000e000f042c4011420071078013007815442909106249014a0b5030795030900c2c000103040350110450b1501c07034000000310704032a40340c2c03130203580345006003840d044003008843c1c0000e032030030007147e0000040b1810308401c50f04100b400301e05402401c24a40003400700d00c0d142d21003603061b1181140c0da0581d51200c41c0a501d001481003c02c076801500c007140c24000d810b410000810b6a80c000c5400b43c404a446d5802c1c4401c5003044031045003030024180c282ca51003d210a1300030407038030540c42804c6e002a290000f0424180d460b5104500100c0b40d03030824642c003247c000c405005802c0c68403034940403504c00380000710b03d685903003d0402d0404d0001d1002e00079900f402020711029102925002452007201060581c1e2142c0c680c600e400744c152911000310040ca180703400804c1171100300300b10110346a4030040c01c1003a47c0040d049904291200c00100315101540d00045c1252044410f070121384036030618107102208140b588e60241e034050300c003c6c462941c0320 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 927443129 1250 927441879 927441881
    0x423030c1b0609100e06041a0310140108280c0e01030605010f090506030a02070f0c0314032505100204060c0201030b0307050904031115192003010b0d020405040203010b120703 77
    0x5100007904400c2c440c000410721803154070300e52996100181b0380b5080c03d031205085400220300c070f454550780b60400428480e400003619252001400103c0000b0300d00c01030800020940071b00a0304001200d072012102e840354080d018044000c001c80d40b4001c02011048450003481b03680400401800700b46840008140c03940308028920035071402e40c85130003070903150406021442d40028a5007954582c203010042c00a00f05414003801a409041c0908410382142820f409a185c111244859544200b0984250b1900000000034020300251880055106801d1450070b0109602e188290b01e4400100407135583e41201e02c6c036044038000c1c1c0c0c041001c0302c80c9905041c0d131000d036030060940c850081800900020b100301e00d60764201d80307201d003a1502d10740c20001501103030506940801c180340c1640c04080140310244140c01c940458820000c84030242d11010b1116440180601003e9035400035030210140210b4044070000d0101900840d902d60b5500e20640340d45d0040c9140c0c0c45600d948201148440307207e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 927444379 1250 927443129 927443137
    0x1b0f0a020f2b121a270c16080403060902010924050a0e0d0c08100203010803120601090905071205060306040308060f03071208070b10080d030c12020a08090d11060423030c1b06 77
    0x80000c940c546444042206d41c590f0881c0300c12406c099190f00d40e030800210780d2006840210b200d06804607441160f4030001d418003a441c0c0103a62245120800200000f14801c61003003804180e0500941c0ca45010704100c807000c5604c000150000c020003404400c00c61150240c10171540e4030801c0e5005165a1582c11040e44001e01c608092a4030174010803e0b902e88503480107400860504080d00c5095460a800041c2d8600300c0c2e2000100c1c20040c44d180701c00103039016550b44560301310041c00c024a050703900500780d544050710030303401407010102e03006883d2000c0200201424058490003108441860904200d502000c0d04032403140d002008681c800201d00d80010683d14146c01401049501810807802010b088074540c1c104100c4040d55440b05500340700604421480f03542e41c200750b10700b100c2e0f81890310b84070700404401c00541c0d681034041d9000c013003030384c5030441e43c01901c85814020110b100034107115007105008981c000012039650b490400500030545c81501130412142e0420fa1003081383d41c0c02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 927445629 1250 927444379 927444439
    0x23070206070f02010912020f1009030b160206010b09011d0a0512010902031018240f020a0921030c051204081b040c050a081b0f0a020f2b121a 62
    0x100d4107880815440c18a416049c000c0c00380c0791030782d00c043c1c5da42c40300c600714401510018024403c0018003000a0f80c1400924050890719524038a040240000289821864282d0390301c82c00341170034400c016546405e103050003403030001c19200110003030100d120300802044600300d100b03105002c85e20303404400c0740c01825400a6240c0140307072090800d80302c0c080e20b110582c2d00d0400051900e04103d1a01c1118030032003a100c402c040780143c0b1505580303000341c45c10259402540141030001c1520180d0b42410103101403040d450302c0c1920b0106050f2401b540360903588902c0e400a2040882c0215807000b0000e40c0d1454208521130500601c2144421b020440d01d59800340000190104441482903000d0f1100b15000b84034549070b800250301e101461043c0c0e07000305808054446d40003820614680d410842c0c100c2c0c1d0303410780c0d002d00380e202d011000d10300a8145d09840401d00242038070261341c01c20b001c0c88000410240300c1109100c80d4000c0382d9a10000800c2c080e180c2c0c4140e0020600305001c4802d4400070842d81 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 927446879 1250 927445629 927445639
    0x20a050c0c0d02030309090a11120105031e0715050d0c050a141201120f0b0f07030f060f121509060902040c030e062403160f0806040323070206070f0201091202 70
    0x108200b00b4080b10000080c00390081f035803114a5409c1c0074030700000521440701000c9000d5019410042003605001f0400503031140306901000849003018042500000c890070100030340b00800000405a45502480c80000c1e03026240c100009a41600311008280800a41c0d98110038a404105231300d00d140183c048490342c002070701c0c0040c08188024503600141c90300070340300b400407207440d0703030f2440c6000c170003220182510520b58051040c2c15405016010080b01b294a00340311040c200030240811a0813486100e8403850003856410510000009800207800802c00034000b081d5181000b001170150854100d01492500490601d00e5210b07102d02c80002c1c03580030241c48162951000300000f80c0103842c40c51b40001840440c1905a80c041020100d0b109815050100070b520388600c1d41240380d0303140d00a203159004a002c000020342d00140d100003403811081c4803200c44400003119000d502850340700139080480055142d00780450b41007042e034014402d0783d403402c14036102c0c0d01da000800b0403044002d41007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 927448129 1250 927446879 927446887
    0xd0518010e040b030609070504151215110d0905330619090f0b0a0b0703050a091703092b080322030908070b09010c0b06011101020a050c0c0d020303 65
    0x150310881641500c08070041021030010f140f5030019003059400c0c0c4015185900080c010030941c24103000d003050034840c01110404040ca0002e200c0102501444000c14814511224503401c0860390b100203582510100001d0325030040203901d00082c14140350a0710340c1d1103151181b06991500c40380411003960402104403800c440401c248615410107000f1542c0000c0e90301c40e8007140c03103070509101c1c0207280d20f00c804502841c2c6075074400700b12400d00704040d0041851050500c0440302c4076080301c1c0d1103585403814035030fa121030300300856600c40c554114917903035401070240031040e20b00040548403a190448940741c8446503404066908801d9840d588060303041d154940700030448140207154002c1c0e4042d01401c501501d8400c05081c1025a102200490403c0005001074003041241c030b406000045003891070043c1060010703080f0402c9020080a1202d103000261299209820310180704d4520742c000c0d525510200e00141c6a9001a45038045520500d600c00c0c945142400c40c82c400260041d000e94a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 927449379 1250 927448129 927448177
    0x16090c120506031227040605062a060c0d1505010f0e061207031401060207080c041a030d0201020a030b090105060a03091a1311030a0209150112020301090e0d05 70
    0x1a05000b0000303507150003007201c4042c08000050040803400308500300c9603082c090b015112100b84100715811401a841e144060003581c80c0c4808880c00c2506d8070340c0c40c441100b80034400c07107034416803c2c0803424240039003003c2c40904910f01000d000c400705028403d0055a92555000c0400b441c20701c500c40c0001c2c0144108207080c0d00400c50ba00300202d02404003464042c1c1140440a01c8030141c803a5030021396a170300d103a10b001c00141640b42c007401e803603c060b203011460139120555a6043c11304485c8940c0c4d842d194101a045034107010a84044054140e07402422480f2010303000350012480d640c040b07400c01d904c11210340390020403241a04e100800d07550500f12a007100b20028051142e0440703024080a0211034014180800300380705100e90703001519560010726041d03500c0791840f0b403141d000e580281e010100603941d140c1c05036405003115510124108000780100c8141143c005880901d0b4800000422800a9038100403014409007045940040c0d01e080c080707807680320740394040701c1a00c44840a001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 927450629 1250 927449379 927449381
    0x306061b1a130501051008071a030106030b0f09070e031b0901150e09150a090b0f0f040b1c05010e030a0203040b0f04050406120c0f05060d0e16030516090c12 69
    0x3400c03100080141d00d860b200c5075100c43c00c49a0a840114840b000030104005558041048802034550701c144840d40c1c40a07d6103000540c04180500c8041c5600c40000340f00c15126821544001c4200800c012030340d04105502508840004c690140640a600c1c1906244112100030380001135001d421540035a00c0e24039402940d43c0d82d54030020420140c008070010540c1e80030b07002402000c854411010075500d40c3c1c1005081d03003099024100380d40c140480e9490ba0741d20203000c04134003903090b01c001c00074541380340008005102d04003103142d114040205484204078401c1081051740c1c0b08038000c00c010404141100d03664012400f550f40107a00c10001440002e40b040b000e0304c0306805844407507051944039400601580c059800c110712041484840e14180b004281542c0020701340300f45150440c600b09404a1024800c1c0c01c0c140c82d03600e0310703404200c002e154108031800d0812800c508010819031240f510329140c000c0c001600070b05007048440440c0841c0a817042204940158991001401c00c0c890000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 927451879 1250 927450629 927450631
    0x140909010203070504090e0304050a2402010c090306020a180b12010e0f191127101d15070501020a3b060712092c04060504020a0f060306061b1a 63
    0x503034240024040010241c491802440c0038085c140402465058030480d1203e124000c1400ce40441e0b0504c04490a56a04040c00c01d00340c0341c0044c4050ba803800f41138403e640c02c0c0c0c031000740700d80c25149000000901000c148040c1000d8106d0b07207868081130340d840ad480b203441001a10392584144031000410119181c440c0e400285000f600390100d280000418030908540010181807444080d1111f4000f1a0700007a004040c0f0410031070f14840013020040000300000e40044a400b1540301d440a000d0065464604444402d41c441804039a207040e0b030f2030064041d4018014000210b103000204180c11000305c80c0c0749603203100d40304058200700100c481d400c1c0701a030303540c24480d04110100149070110700aa0f00604400d5402d0300d5100244e0715182d444460402d01d0160b44010030491803d1480520400383c409030056040381002c41e25451354000a00c0d052100d03480780c44240c0f4280c0f0005146a056004441101e049894102103006848406007020100410050140000401d02508505a10313051 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 927453129 1250 927451879 927451901
    0xc0d08180a03120b0405040f150e03030901090c06081302060a031b090e070e03070314030408030c010c0f21090302280c0609080304150e090114090901020307050409 72
    0x30035160156004050410504000540020308003003c01c083c82542806001c007090002d0f5001c00051505481d400451111400000c011103143d0304d01d070503141c005800c13981c0c00c1e0440c03c1c2500e0740c80c00c0c40d001503402080c1e9907201300e514075010300000410a0003110628810f18044034000e40981d03e6600700512a40494170100c2450740d030b100700100f031100c8003480c0349045034a0f40720f010b901c5003802882058110018226410004100740c00182030b00c01141c0c660881794406c5041c4080111035448904502998101001c43c0c440420f900200580540000c610076450351500300ca0302400d5401215078100d102c04081d01c06822440321951091980c3c800742465000f48103503014980f0000760004074034100c4810207000303182c6c850108140841088000000d01e0300b0300309644018a4101e480c2c3e01e0b0302480c410350a100014161020031b5901030341d03109465803030080058109607141d440c003000002111a4044c0078000c13200000311407100510071280566201d440d0a81030529040c86840a4402c2d5061 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 927454379 1250 927453129 927453151
    0x1a030f1f0f17010e12071407210b072303062101230402011e210606030c11031c09050604050a0201120213120201030e0d05090a05010201020c0d08 64
    0x300e1165100030071000d08418001801500c0e00c012000d400d48055004016880e0420519074008100f21300490700356640c8109a81b40200716034003114104040c55024140085d1020f4002846c101000c110718401c5100d9602c49007035071038000301280c040300f1603000d82e5204036641c2007450504074540081e65120000424810480500f02d210006607030800304410550380d10f0341c456441800405501070140002040030151916280d00020181c040c20b480c408200b00354403c0c241c40151054400d15000420b81c0c0000f403030705c050558550000c01c0944a910006450116000ca84a200d11840224201800019402c00100795101d803501011246040080303a07a075541000025003d1100920590040d009050b080c5010b00006d0190364401c410200524410000c4101c1c44202002d400c05452442400c196184001d10040e070080a60090000b00d5110308860341c21810342c050010601081309407005c20040703540f1b900681c04c4c0d0080380b010901e1504054030303042074144144107850b031003d850300c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 927455629 1250 927454379 927454441
    0xc0706052518060512060d050a0506101409240102010f0e07050301180f03030b04020d05150f0a030309140121020301092304110324011a030f 62
    0x1603081200d406034001c220307141d0035442098000407070400101500e00305507140064074445001c1c02a802000d8607c40c0903500320000a10000304031081c5415401000c0350440c0c103110712890b640341c0c5270307214041030408549040c0b0303550f00305803040c64065002190320740002c040700b41035410399880540c80e2a04542d40d582e2003071804c0301e190040400b04031903040035005540c00c0038280360a54a802c0c0c440c1e0032007059051000006441120390710300080d011320700060142001400500603114440c83c1d424628102001d01505031030514500342d202c00c040b180400780015190601503500424440034010410801080200c289440d01d95000101c05141240c1103001149645000a00f00d940110081d9400b00040c404c6042e20b1142d000346010b10038101c0362410902c1d10343c0350b80300d9001300000d102002242c4001e002e5202041401a821885c18405007040c818025944400d103003442032101d5160b110745e01c410481c40e00c1089078041c4a545641305a1703a0748809100076150501c3c1201540301c51451 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 927456879 1250 927455629 927455671
    0x30420061303060b06040302010f110a0b0108060a050a0b100c050a1406070912170d090b011d100f1205030403061814070f1a0903240f0c070605 63
    0x44000c0510025184000714103a003107042074002c5a10312100c0500510080005102603070300440326011815045c90104100003400b0020750400910346401010b0200303180003c40c0105001c20400c3c841e4801d08820404ca540d001d42020a59645040c0b003030b0081c07110b214088925200c1c0c081c045106020300102c03100031900365584012420207807130000301c13604000240254142c0c4514030200400300100c13240d00d008203d03180d0701c014460880c10300201c001b0000e8584015142c54110551080d00100050341c2e40d0380d984404007000547c18004031001d00c0c100c000900e000180c010017810782c0c2d00360a00c00b807401c4c18191864a0300d041e40b04103036401c0c03100340400800200e0340e000e040b42c01c45000c8005080680646052940c07080d82c80d007044030320b82055005020030800480010101c9405042e02c0c484010b5240c0091190710460881c240c140c0542d6460b08014400e0b001449038aa03d110f20110700e40c1d40d442e4000062440076240c3c00391780d03901003140340c0219a50390440c81c0c010444070300001201d5016 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 927458129 1250 927456879 927456889
    0x4020a020c03120a020d0c02100815190504180510020c030c03030a1b030c080a0b060d090b1b04060c030e060412030207081e070b16050a1b05011103030420 68
    0x804140c5040c4240001c4d040f09455050061440460703076401e00b01400c90303085d40011801032108000c10100031143e000610010484582c0b807481c80030152207100b1416211105400c020110b005580c012403d0840c030403501c0d030083d524130a8154100303018044000c0c1700001c0d0401396124103d000d503144001d114a040f5164244003e502030307800400e00150000c000740080d40c00b501008902d4040c146040010341c07030103800400013540680d418030300046150101c5d00140b0103008a01442c0304140c6403140400410011000c01d0740545400d0440002018429000e00c03540e04c0780740290400980ca203000000003a028404240038000300030700240c10291124040c0701180a444410f50069200010800042c5414001a2a60603a500c85500440706110500740d0381e070000d100d075000b0700c0c0c000100d940114101891440d085580b20059500d0000981042d403d004100100319610041700040011107600403501882c8018407500030754219a544d0319114010300d070a421004000c80b040c80f113400030f5611 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 927459379 1250 927458129 927458143
    0x6120703110309030d06061e0f20010e0705040207030903030e0406091b0807050a0c0f06020d060b220e040602030405010b030d03090c090b0d0803071e031416080604020a020c03 77
    0x101c40d0045171610358407030741902540c0440e0310000c1402140c00410807a64040c0b01100c40c42c0104c2d040c5088080c540040480b01c0d281c280c400c400410b42086034849400d901074200005d02101042110400da031240c0801003207104d0100c0080200310000c0d02000043c1c00f1354000418558000c2c0700080c026500c8080505a0b02841c031040c0c010358121008000d801e8000c01e00c1504041c0b54039040f41020b08881000c0c103107003a10702d03010b0103903a140d01e080c808002494044070011404118107220055540c1e0348200300c1d4110307070644220040080b0038086840143c0342d0745406ca442000715001c2a4032151107000003944080c01c203407825504d8000062651720104104922030400d942c0000e4041e480f410403401e9808140c201c1100c1500703140c0251283d42e60780d5801e141c00307500f0503502c0340d5945604000b9640215600401260b5103840407092401c150181d000c03280090070b04800e4113071070340e0740206100890801a580c0307000c01c40400105d4801d0600f54082d20400800d80110380b614900c00c40000d142c189 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 927460629 1250 927459379 927459391
    0x180b030304030f02040507113a020f10050f061005070b010b040f05040e0604030f121503021002010b150a030e161a0a0203030f041707140f0a02061207031103 69
    0x45480f000c03008504040c81000d91200302450300ca4030400940d80c0362612900c0383c00f20034102c02c194500c924444075441b600c00300803815079201d51f13604074103400029446544000510015006080b000901d8480d80c0c0181441480005000d10050355105c040180c10581e00c48018108a424040c03000001c000c0350401d13018100200400791120f1401c41c608400780496003005004504109079200001400a800f03a0011307450300304200c0d266035403007046550f000d964081d100c5071800c202c02c0086821800e11300c1000d480c000d46000b0920541c11034240e087e241c08002c503580050b210b00b4403034500d000800161444450500d000f080c04100d8985240c6008000703410a5414500c4900401c100c1e4003001c00d03840240408900e181c10045010780180d12400003c0101c040080c0b1107000800b00202c01c5a81500301200070303039494884c1d61a00300321200341d0f03205c0c1c03182281c2d100d01c125900c409000010f807082590750003000030303140140684601000200181100050684940a8034071854a2030045c0d84611 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 927461879 1250 927460629 927460643
    0x14090f061903082b06080a080a11191502070302060f2706060f01171807030606030f020a0603060b070201050f12070c0c06030902060d0e0c03010e0d080c04060207180b03030403 77
    0x13001104160314854007050540051480c24400700309000c4d020507161000398205110b251180b02d07008003a141030f011401484060300582c085a0141c0c0c2080d20766136606ca010702e581c2014540251008801c9124410b406000350f8819030000d403800c9080d05500f035010000442c07106d08680c2c104040071030700885a06022241d00300104010803030030212406403109000f443c0000c010b1005000081540c00090100c040103040b034215501d0003001002a480119880380e4100200d81e0b0380d003031001c0400004403040b0322078130b289500008c4841c820301444c0c040c0d03000182c0035854001c95a005503150b9003c5051490500402c0c002040401c041c882458442c510544480000219501c1c0c4000f1024142d00311030145464404507402685620003560242c031042c50b00064080d400c2e401b42e03403a00c00018103850b8190b003018408110a54046102c1408103041c0c0c40380c68403600e6040720f400d000e015034001c801c0180d01a402c200104000d803d50303141e207008809000202241d4000110f425603105410a841030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 927463129 1250 927461879 927461917
    0x5130506040b090a0b2805060f0f0307050a0314240f0a080706080f0f040f020102010e0109060609060b03060d0b04022b2f12030d0204080714090f06190308 68
    0x280c1440c0c03400c0a1b40c81d07008641c03410a650000384484007100c060045a01407600803500611400c0554202c488510000000f29120300c1d21000060040e806074903203400180c2030032241d66882e401500703403030300500d5070300f08016452030f4058030314000d154000749696008103d08220003007501c400d0000310151110102405601c0c1c00c1c20750181002c01d01070086040c802e400c0080204606620710515041580406c902c80d0f00907242c00100d02600c070714407105c8615440c0903040010840242c1c0079804440b04441d0500045a807068510914001110203542004064050100003402a4081ca522510091000003c0200c01884821900e00703089600810082c0e801d80c10144040c000a0084440c04500072003040c0c80004c01c0c2d6240700203140300704c0380201d500035040d0221080500c02da44604159200440d02e96540c0d0800c00d585000340e10038a010028025064540c1c0d0908094182c8074050b40c60416400381ca0b038505111510030380d043c0036251030080d10350100014004000030001c0082c1c40c44603a640c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 927464379 1250 927463129 927463151
    0x30703022a06090a1a06041d010b01020d020313030b040804080a0f0606050406080309151b071505030c12090309090906070e0a0f1e030812090d0905130506040b090a 72
    0x900480030b84200710301c0d840b10712010b0002da82c4010001710141c048180030510380720700003c100503000c1d10075000b500225020448044603815440b40f410101c0036400c84141014a440c00e80e101e101e00c008080490750000010320103e00004c03051500644200c0d55545171035130790748a090500c68801d404442050ba00300d40003040c040c6c2400b0321030240800305d404001c1e1070725203060703265203110b21300205002d20020250b4100d540c20300310030390b21451541c03011407013402e0808103c19260501400f0740000e070f540c50700c0001500e600c11000d4911515900d607207180750000961141285400052502a80c4e210410070144113485000d4200d00410142c00140003500b4842001342600d4081c0e0030050107030303854141c1000511000b9800801311002c450b0301640d59003d4912501244460380c102400005002550315810540c01552500ca60383d40302c2590141c01403004100d440030818031800d540010302d200c9519040d40250302107034010800030000a403954504000c42d071003081c00c841640f4480c2d42c0340303001c80c0307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 927465629 1250 927464379 927464383
    0x5090a031101230a0b040614030106150905060c19080918090c01030b0a0302060a0f0206090d09030b0619030501270203030a0305070903081210090b0d020105030703022a 74
    0x1007150260380240240540449400100300207007801501c030140100204030f00d94001e50002a8080015006108007503e03951000000c0c1c440c00b01040c0658030300304001891005403a4130988819403580c1c1c02070f50515040410200d9002852018614001c0c440c607108131105461001d134600340304d445402e407120025000c02c810703100305111501800081c00100072402c3d6000c241c0030007091003400c000032042560004030b41c42c680701d9000250031141c0054001c02c010f800184044c01a03441c0d50072114640c0d551115191600c04072003200000c91400001400056100d9100c0d950140b0050840d50070482078003218081c168850f0700070380d040c0c1d5480b114044540f8801100d000d0b00716a041507502c40c40e08079404256603120768800c4004040e87c40000c114054130a0b6050002942c011f60845e03218102156405600700c01038415120b0340900c50790000d04822103004d885000d40c002001c45200b90010340064032198801000c410030940e0801400850050803511108001200000c6142d0204200c200303c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 927466879 1250 927465629 927465647
    0x103110607110405090c040905281a1503010c0903060516080109050709080d03050f3301050c03160204050a110418021c050417040f260105090a03 64
    0x9000d00c0003088076801260030303004801d544031010346001039941d4450760910b080c19421190554018204031048040c041c1c0003e10201606000c0120714200e02c40c400b090501031403003d002007c0c400088041301c11280d4034052907500010300d03041c82805a605a00003421528001404008540d422030140300740f00f03d9100341544016550440b411900102c40050060790051043d41110340d124030000d4036213031140808000900040302115821101d6540203030280c1411141000c54503070103800620b079141c980b0610040c04400e40c8488048034903001115546d02c045034400342c1406010403001d14101020002414a801c00c0080d4913162001481000305844001e0b00e58241682026807074203100d03404508a0301203400041000207182d002140c1c00c0042d008101c2014000c0110244d222040d860a40015110700c1c455a6024580340725500110114080c900130f105c10004061001c0c403004c1c1995078051066002d218805a8100e0f0034001d0f0750a5800455072615140c221540301c0c070815400c24042c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 927468129 1250 927466879 927466913
    0x90106080f010e07050403141203010605031e070f121b031a0307380304061b021203011211060328060605030604090204380405010302030c0607050715080103 69
    0x5400c07130030082e0b4020042d00070f500000c0c2c14501d4602c0150500181007010711900418940070581f40d44c0c3d01c030f0001e00035403c100c8400300701000140042e43e030b114400340c04c2d0703100318075941782d84c000e12004800403501c0b2030380780109043c03407075440c0314491400c001c11000d221240c1081da40810340c410002e0040103031007007007403555000f40e00c420418040302c540f004022140c407088548609042c0015900481d6441c460300f1044844c0030000f0510041c4075040d000018001e0028495001d0039030060400c90341d8102109031074203500c0c414001480305030f0001c800d07124403500074001c9101c840e01c80700029003a640280d6060002504542600b0342201c0490710036000303100c024a0801c20717103141c01009080345c800100070500c101d5548006c08110754960b03001424411000c1001e000c00012107083d0020005070500380149100030404821162824cc0181d5050703a5003c0d007d45546d100340360070f215031504904403c4a003400761100115800b1005120002240c2d0181d0341c00a0552460034000c075028151080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 927469379 1250 927468129 927468149
    0x30c0a080307031a0f0621150a0b0307090b0309030708180306071403071407140a06050a1a06161e0c1d1605210609060a1503020304060b090106080f01 66
    0x7050310341c5d4590800303140c100410740c0c94556032100014402c0c409808214040c003090244800d216605004200030072450340103540e00d038000c1d0b40b10300b00302d0b129000460340840011442103040c020781072a0406142c200b405401185d044c249140d84075a503940041e02170300607150700b5a800503614034080055542100c041d0a10014951380b40f103000080b848000c0142c0244145046043c1d00d400c07211003141d50080c0c200040310309241031200c83c1516407442400580b03905043c10082030641c40075100f4104402581a03240e02117540400500c401c0d60800300000050401c00035461000c13505810301001030340031190740820054003e2801604402e01da8001007410280300a190046c0005000300a400c050072001e106e8004109903011600c0e0b102d0b01c0380018100245000f28140e00c01941c4402d8010402200da00c60950360382401d024035028103214134a9006407111a0000e410301036402580c106004503008100c2030751150110f40c22403000e13840840011003540030060084c4026040a000d0028a41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 927470629 1250 927469379 927469421
    0x803150d0201140705070e010e1503010605010f1110150801060e1006030b190f060306090b0904150e0706090905070e090610121107030f03020c0d080603030c0a08030703 74
    0x2c00f0614100007081182400055074400d001c4104091002025050003840c030940e107d500103501403000343c80c601502d541801d2940040d00d01030080d00d05460b011303920742e45c810101400454025030710f03100d12040e50007440321444549000b07018100380b100c40d02c110580210f1800301c0150031030b400d90380100408c060000a028507503966945200480d11507140100361150600d0026484415010302d60307203c48605403000500c0c640c00c0780b000741180c1d035039102001520790343c42018054034202505154012503e50000d400500c6900e800d00d41d206000b000000c4110f140c5141503d030440f10380285021a42c8840104071003140d6002d191751002a618113500c0895110020a0302d02c1c0e0301419261107040510201e507001481102d0846c110901c19101f8822040510000d44aa5021240a40004000310740d40c0e03240038047c0c003c4800d00707100d89006291607206000203c91500c4003820082e490300082140811301e0750200a03640101e03006600340d071390724208500090101c0b000003502015001e0641 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 927471879 1250 927470629 927470633
    0xd0c02070e0f012318071215050603011a071212110705060606030604090618111801050609010e060d1a0420030405160b09030d030627180803150d 64
    0x20400310301c424401c1040030200711680d800108554160140171120010107000c001c0960350060149088013501d41041004501202c1c2c0400d4507012805500d8102c08100010440c0c0c18802e0182c180702c00f09140d0660a041c92596070004000c0e0f03220003200003a25403401440720b54014400c00074440c00c80550240b401045665180e140e980041040340700e40c502100089240d21036030403440c16140e209004108415641e1400040c48050310b5041c1e40750641400416001d08109400c3c9a28403001901c08440740c0c600b10402460364030400740141081040c040d0004e041c0c17294000b030080d0310094030010030307201d1401e980c0c094012190000b442c412401d044107104442d400641d031000525868035010ba40b6279450612030310b080816460b101581211800000f071600c8814054428244110103903030f12a04100c41c118199042401120a0f004481c00c10b96240520b050340706c0c00e103e00640300860503000d40a00e900116407052000d80300c1200010030011030000210400f4003584e012a51901c5a414503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 927473129 1250 927471879 927471899
    0x1c02031c180504180209060411040b0706140702100b1908030d1506050403030302030a090c12060e0102042102030f01050a060501020c0904030f270b0702040c09290d0c02070e0f01 78
    0x1404c40a4011185400440d1554449070000b10100c0c1d4410313180c0780d6035030b80c6060b101c4950340090006c0e17491070303c0c206220f1000301c2c2145901d0f00903c0b681d401000c1c051001d400780401808074241d415480042c5d020103000320320f402028040242903030030140d9140d032403030020341041e07803144c415044402d5000e070301c140328194018081d0ec0980f500b600e801a265a104503508000b49036980d0050721604400e400011803401405000206030300c00c1c0e41c240140c0c03c03580850b07400c3c1c0c00b0754010304034100c01c1e058551402880314242c00a61900080880b400c0140140e941421200c0030384140c200c998413540c0600055030100064400200c065865611603d07254400401302071035540404100a20a102c580400d4103d51803039001202d80c5110f038178044d41e0381c03002d2002507204034000ca000d1814242000c2d0640e004d24490001c81c0d600a829034130205440140c04040c4040d60001024032405000302480140680325804007440700380c0041800a042c03100700017042c4c00050040842011a000600089011b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 927474379 1250 927473129 927473171
    0x90f0402011d131d0102071b0906050f060906121006020d1e0e060d020c0610080f100b0307030b130c150f0513030510291c02031c180504 60
    0x20800000520308070750104c00d0031070030b2002842411580085101d01c28050b848290007207189030701d003421100030b40c0c4640c1441500c10038812103074040d102e81000f04550030104020651040003e115900d00000b102a1521a500982d60300c07001a000e000203000c06c0e234040009100c0b041a50070466450030a002001d00b5118404100e8020032151141e100840d84489040d2441c9092501c010b54460400840f84e80d624407040302c8000d04841003120005040e00089484140301d0804005032018a000916140140501d022100c0c2c16100b020800804101c0842c140390140000070321030909045d1038200007000f680d0540101030454001ca208400081d04180b5124400c030355400c14079190803512100503005403469001420901071a0076200d0014110b0380100500320044c1303c000c10401c414410804100340c203104841c0c016241000107419007010309035103000c10b44010f08440310030300c6e4494484114050503a241d0007042e044032002c4600c9003a0781070311020f070070181c400304031440c0714011400c05261 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 927475629 1250 927474379 927474409
    0x302090604090c0507150507020606151603180810140906070c0c170c01030f0209031b120708060906070201050f0103060f0b120705030735010902090f0402011d 70
    0x19964180f0b0645600540942d00c0320f58000e030313000e420714824038101d0000d0030341103902d80014019140060f905113401c080c0c003280425644509414408c0341007000221003115030042d41407010340413025581e08011030031b1001034119100030745120b00c0400c103450181c13651170f12010120b11040e01002407500d0b00050705a40b00c03119107000c089080441c18040e240d945aa040040c0d0705520076000007036105c0003d6a4140c090080c0c3e030030850303e40c2d4075800104900810750003e0303050704003141d6902e041c40f40c030100440051b40200b40d41c1e820004950030341d26102e0541c2c410300d82e0781c00800400002d140140051988140d00b800244010702c0d08025009801c02c0c140402045e140d950f20b40c581c00c1d0040355028000940c00135210b03104802c0921540741d541c230214404e0612900c41c41201044487c1d4604c542c0c010b1101601c00096010100000c160990100d41c005500790366803200d80d07502698888140301d00039600507489003964100b40c0001020500d070103401c50f8070b8050b02c49003c402ca0b21010507400307441d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 927476879 1250 927475629 927475631
    0xa03060e0c2b0e01050103030305041506030c0504020a200a0b011d01031e021909061a0304080a0c0c120b0a141501210e010507080c18060912010504050c01030209060409 74
    0x25a800042d00c0c0104005840c1c542a0b6282800110402d0341580c0900c1c092405162841d648401540d1403400b910510302004212106240d400c101c0c03414590041d08411285040941c820300c007071120348086480380c030504501a44024600c006002041c0141b9024024203400c800d1294801d03458003078899010700c0000c2011002c0100d03082903140c400d80300301c80701d0740c003d109450031140e1120550240c506070241c0e0080ea490110300141071030b540320b4800d9880d00658100743c203540ea1529040415000f500384a01401141c03854200014040d0f03eaa0001d0002c180c803180b080d661505128a847c080200428502898400b0040c040b00300700800c1035010140030340e01c030381d01600a40105c51b02e240d40d42c009a481001c1c0320300d90511401e2908078030424005030008002680d90f80f8400c031081c0100781c40803910900204640c018020444000706100704000e041e5618000034540030032242e020008500096941d14814413040090500080c03c1c0d8200918040d402c00302080c00240f00da10446c401c1429613 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 927478129 1250 927476879 927476947
    0x605090607060621020f030a0519020423041a0f1306020903070b0c0606010c0209010909030314040f03030e0c0a141516031815050c010902060a03060e0c 67
    0x51a030000400350a010015130f488510700e410a41d2890010ba5040744a02c0382d42d80720100f18240001c100d0116a00304000f4016950a04010f184942c60708400342d030004d80340c1844071509141c070b00d2146004102c28150010b81d1900382071820448006504090200d40400207000302000004000b681101940d2040046101c0f1894190300078414400c8664250043d5000000d401e41c458025281e40c0811400b5541c0d60f640e418011180c0a21158000390302290500050090700d443c0e90001c0411071290500007800c41303d40c011182c0030706040301d0440d40c180a1511107410954580140c1850442500c0201000401e440004810001d0760242004c51894141d200d41b150742d5800043c0940000d44004d269a85001c5900c001e21440081003035002c59443c4000e0b00c0820448040c00084034002e00e03080410301e480da8800ca5032588490601e012540d204c100500141c1d0710f0702c1c0102030028680e100040c1d400d01d8482c4203034000f01c00410444004a091020203101c4d800c1550140c1c1040c0300710104c0c174003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 927479379 1250 927478129 927478133
    0xa05060a0f080109021f08010335071a100909020103061a030405120f07110d021005041703070f020f010215010e0402040501171c23220605090607 64
    0x4410210750200248198940000842c1c20043d80444900c40c000d80b0001c0c1000404c141c3d0707281c1341041003402e00025a205004101040c03a08007004c11110250003e040c00340c2c0150742c805485988114640c00c0500d00155001c1000a24012a0355010000c8810a05403405810020f2601180d1003052051340d00c0700815411603200341d024102619030000080300c2d54a001010406981003194100c603a0f11800070181c03046007910054403c05e04650006600d40240e0743c3d0703090601d078503201005030451110160130006070b440d00400c0441c94920ba440c642c035070f407421201288410034104140e040d5081080403001060307050600400d1650155540050b81548000403890805407800343d989100d030880000c2202c0c00200d0006000342d008503000d02a59072100015842c2c80f26101400072190f001135040044c1c0d40030960702e101c40c008213041c01400c00001d4508405421069802483d08130300010b503400e5210039540d20403070420000d0b5000c1450600b0041d0107001413181e030590b0b0384261404111034007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 927480629 1250 927479379 927479389
    0x17010c0206180307140606180405070303210c0c0b01061d060c07050a1419120b0403021207030323011203080606070f060902030d140403061a04060e090d020a0305030a0506 75
    0x803180d03400980e4071040341c500c80c90103486e0071003074520711302c500c40300025100a8a80c41d80c006000e02e80120207031003401d19696054800f54510900203000b880c401c1c0e04c0003400c0308548122921072440740c0307502c0c4a0420741d01c0d0041e4a032405030007040a00441100810450000240d8440f44c0c0000361147d03961140350071030a41c40c01849070b0105038004002e8002081000521001d007071900d2080d40c01c080401590040100203240a0080c10340c4450044181e801142d00c02c0100c40c1c08c01d00a005803001303448076801009866000100c2030700420f40700d859a410038900540d00004076103841c40100c11300d50512480043c0d60b00c1c125009010000600041002c555901d011075031225407004407050242c80783d1a0400242140c002e040e840b900501100f0300c00e0703c0c00341d06005682040302c8080c42ca041d00b90b655000041623250009030810b000204c4150701c46e26140708407005009941b01c603516601d01041051b141c0420b0840000c00c640000248000007904241500d0300120342910103d42a0703240d602081c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 927481879 1250 927480629 927480637
    0x9041b0c0624030807060e06010b091009030219140a081903021f0f0e01050118020f0904060b13090b100c020310050a0c090801153c17010c02061803 65
    0x60700050002c10010400101000900013103115000c01d201d400003000000792540024481d101e80072008104030086458240800c44c1040349600b02005641d490b070300820041c5901840c40006000c0c418424003103014500707613008080c0c500b2289101145d0a0664043e00c0741d1070521141400142d0055041c1014000c0c07014100c580500d01c903410b0071201d800c02002c060f10a03aa1080c5e0385a00e0100511100d0341d0601420b8140c42c072140c9030b100c40c0342074200c2031802944001409105c0090074800c1010316a0b5a0241600500490001e181ca501c0007082da0098007605a00c030307002491810190000d2922818055005075040d800c29800c201c030140040780c10000e00b1340c80700301d8207841e1404100c800c5015520032449103402d56035020000e40c03922030060072030303030a20420681e940d0955801c0102002a261030402d0910314031000d0312030320269400011808d803100050039651000e60080c400400000c400d105100d12500081c04030b000703025400382d1030b000042c3c080e1207850505040b030700e103a140404c111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 927483129 1250 927481879 927481931
    0x50a1505130e130b06010e090103260f070c0519050f27090601080c0112020c0703050a03030203041509020603150102121b060a062402011e0209041b0c06 67
    0x110699107407103c5003005007244400100e4201400f500810850f51007624503444098020340392030416401c544420781d101301000c2c40c2c0c149030b185070748100102da40e0a2000d400300c60010046a030315003801e460a800110100c0c0c0100340910024485040507080030a020000c60310305075040101c58403185d000c2009203000110044115107544039016401d079400c1d0405110b5640c02d01a40c0044c0d032514442c1d520745001e01803642c0090701441c04d608010301c0b941d00525140010341d080742c11480d926034503282000f00b07a00d4240c000c02d9010007004284010543e41d00006480c01908001e14809580025403500024101d444100306164221445900030420030045401c0310b070074140c452512103102e48010003844070b103182d10f0065501041039904203010344421b48803840c0200d200e0b402194403030520340e85101c0400d0119929908458500d40d00000a03046040900d40013607610300c0900c0c14031066070060b0b00b070950300d4403038540343c00e2607283e1115801d5078040d030181c40450304140740ca10382d0107020781c00080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 927484379 1250 927483129 927483149
    0x2010b060a0e03010b030c060d050a18140d1e0c2d050c09101a090603100503010c0c050d0309060915050429070f020f1501080106050a150513 62
    0x16540150b006607090100d25030407402440340b400c1d0001030549a400d4414402e030002c106104030440b401a0744c00c195480545458000780704489480e841035100700015054410959110f40d03040240004c0c804808080c01c103080440c408042e4010603030350658001246010020344901e075a0410400850120000418141c0c1070102c201c3c201c2c12000401b034000c011560b52203100706607842d90815900f00e5201d4184820641c00041c54200b24480201c42160712040181e02007014410a1380d0b507001840c000c801504d9118441c600742420726084501d0f8401c60030500803a00351a2000034000102d41034841001c1c603020030240c1c0c49140a001030803100c10300a0441425444036035085d0f0180d0301c00c41c032a60081e010540d202c04032111200d110b5001c1203100354a0340346040051071072400394011a41d00001e0b88110b40c81d190001d800d1034101094001c20041b2031001308010407000c0002d0003000c02802d070031100b650031281380910382030214215500482c2442000b040d1944101107643c0314400400d40840 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 927485629 1250 927484379 927484387
    0x5010906320c010e010b0604050d14010513142b1404080a0b07081302042d060303080108152e0603061e030b060d0503041e030620071202010b06 63
    0x11019402d4002440c00045586041c29072a00300005010b0603070701e400f01504642c50603041c9800e0100d041d5141c88244d6042111201c90a4011400d10415206103484d041c10007100e80d440c508100c00c00342074540c04034941c0c090f001c100040c07940c003002d940c22445400042c00121281c0c103806c1c2e502d104c010410000690740890700040c403e0000c2000c0400038031901c0c145120759a510021790f15480e050320300d041c003105c0d0710f00806d006040a50019481d8a01d0807035050f907204110108941404032402601082500c0701000c004140c1c01903141405007010001401c43c2104184141c44040401003c1919040b1a000104420403504512240c0329141001d080c00c1c0e503032a4007024024103407a201d00e40d01007075102d00403145111300900003816260720100c407058030b45039002000103007107084100744c4490000300030015001500820345159501015500b80302e082c5103040641c2216043c00b2100b61405242440700700900800b0100c4240700ea004800740340680c1c1e602d600b280103001c1001c1003a000a4001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 927486879 1250 927485629 927485717
    0x121107030507050105010b031308090d061b0e0609010c0b1312080f070c0f080901170a0b0906091510120f0902030d140a0c0f201905010906 61
    0x41c010564640541d000340210b0b43d07103d010340783c64032045610010508540601600042c14100100380c1c05400600c0003808201e280c54040856104100c05030228000901011031035404c80c03d030b03411001c021919a400d006140001800e900f145003c01401c2880b8800010700c2c841d8603981c2d1203c0c6640100420003000d17000740c8090401c62050303a022071100c8650300040e6140d4402c00035226034560200741034854551a50f11070074103802070740216040c40808070442d65043c0d0b200703914900c903540b5800302055007004482440303561040540303014083c02000c1e0030032a25061148440c0d01601d005e0300e0710304204004440c1122200601940b80b6080d07030826009003042e00c0140c0010040b24000c4007076980d0803a0a140c140d50692507020f00c010040c100380402c000ba2409460390056450080ba500c081080203560707102e107025a0204540560031016914007030904140107102c0310030007001c01c182c03211030900d0000b821102081c0310b80405c000a14441c0c0b4141d90018050340c01c030305000c0340e99a900d06405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 927488129 1250 927486879 927486887
    0x1d011403090304291e0d110418110403030e030a0b010f0e061f0809070b040e0f011a04030803041a040309080f1b1027030b06040209010f12110703 64
    0x243c8a44a0f02054080d1100c943e04d51011070300d00801044200e00780f510801e01521104035407031022032000c0b03a009001038440340300903000e02d905e1000d00b4014603642d00d04100007012640c400442d0348a2641c90500800da003400c50104840c10344e500340c249940c07070600c0100068a4601887c0e0018004074074100001014000f80c0781c41d0703042e00c21440711035950703684107001c0c0130306003400c2d43c540015104040d9035400c0c50350042e0010368111402c1415292901d48800704400107034450390001c082c00c04017408018102d07524000392809043c2491010706404034091001c4040d000d9400094171448000000c0740810100603080c441039940c0c80c40074900c0c0d142600300580046458422440c046c02054003440400201007414011f01007100e03014941e03101c810b814007100c14004542c040c188403040b10503410240317038036440c49403440b100281003a04038110728002003424805020b107070242d401072005004580c3c1050816103441018580303105040300d030740c0d000300240c140d5084020162100281c020141640 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 927489379 1250 927488129 927488137
    0xe1809031315140f07020111070f140f030f03270a090207061103070f080c0f0c0a110d03080a090507050933210f0102040f0e06040c1d0114030903 64
    0x46440e2200b004041d0300c3d41d03204500c07a182207900403000c01c0000200541c000e03407807001c0d401100760440f40d40710380302c11110741c451500b5046110603104200d1000064070b804440d42950b004e0a50141c03420200110481e50380e40a64804c2441c522a5110003c0c016104c40c25203000b8581d00034001c00d2445c0d41d0b038030700400960180034192039543c00c140c0300040d400e80d032600f164010314560713580d21207060b008101150441406410103242c0e1004201216841a1350000b8243d1900f508024010803079580c40c00380d20494800c041c1030300a2001c1400032002c01c0d00700c219141c0c084003000c00840c1c800031918141e400c1103884d4001039800710260051091030a0040c02c00480d032011140711041050500c205041c254000800303440e401044210a400700b0900c0d240d0744807429515104480010080a00403802e90b00103401035058903407080300c108045251600280d4000005807007c000040e00e1079002001000d0100e0100c68001c0c68100d40005640b18554440d11032150b11480c5d0b4807404e01d06d5005881e944 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 927490629 1250 927489379 927489419
    0x1302100302031e04020a060c0609061d07090c021506030309030f0106140409020a030609150e03030601080c09011409130f020405240d0b0114071506060e18090313 71
    0x100070f8290380503000d4a041c60600450b0000e1070005501e161070302c22110314468403422198503445208410000782d55001da40d110120202003800012030b840d6400745031000c04d81c818540a42400201c0d06c105402007100640704120f020207134907a07591140440d180d846002941501403040801044641d101984280203035000c84411040128000c0c0403c015109021780c069071141002c503081002400a52006c44a54401c44810020310001078a00080b15009558010386030030000800000350303405a070442c1d200440c0d04e040c2d81000747d110002050705904c060141070300d400000d68048150390300300740c2c008100240b180030301103c070b11070504401a4002d4401c0324000e41410f034003504030780f10000010010a07850004230382404032440c030700f00103021401811410302c900c3d090100b050340c11240040082a002741800c408000342e0700fa0400482c0e0f80392b8480020841e150300f00441581e103404108100c5081410b411160717896100c0d60341d003140315140070007242808840c0c00040d0b20302001c4038000404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 927491879 1250 927490629 927490651
    0xd0e1c0506240102070f1404090f06050105131a31020403060e03030105010503040b0604020f040602160e100504020c250603060f050f040207062004170a0b0c03130210030203 76
    0x254000581e6101c40c5c0303019202005c4203040c01441580c3c65810042c200c1d9000810100384400641c03201c08194a050308151600c580f10001440305d410454010012007041040c1040000110241004545103c511161040809034003001e2444500d00407800440c0344050000300d01c0550f0325182d0001e60261204984040c1401503c20a4040120660703048420603110701d4a1540c9580e01d00a0740440200107961080d0700380030525000358080054000740c10260020300c15001111016044644c06500c0051000d6041d0104041d448a013100720f42116415203000da240c00300c051010703040000803d03080c1c4080c044079144d801501c00510854089a001d51410055030b500c07100303500d03010b00d02400b2309900804162030081070380c1881e900408500303004003400584560218501c84130025800580020748202260912068812000010a4800400c000c00d05d2201517500d45040b05401404100d01c02404400207448800d0071582c805044c1c0e00400b058000820a84058002e40098900c10030304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 927493129 1250 927491879 927491941
    0x1090c170c09161808060c0a1107051c060e01090317010905100b0f070516080708010203040b340203120105010f021018020d050c120d0e1c0506 63
    0x2802c010504500600e039041d040781604561000696000c0c0d4070048550000401c4c1000189120084c42060701415440e8003255440303214040052920340b0034114401c0710b40002d0010001c0350b0380d1142c0200d2568a0b10b4050449010070300b032403401000056621a219400e01118204055010000d406038401c150b20079865641c07a003503550304903003088400701382c012440102400004004000381c600030741002211450103006654041c24218500040c076201c401a01c0c2c01d004404c0288041e8000d820f00000860440c9040d4880ca00d1100001d4008126030390003040e10819401112101e02e607003120760340b080001207003030394000b5030300c1d40450f85100000090350004151984108441d518020155000746041d01016001c0300045c00f0030003001d400069000880001601c2e190b800c49492400758004d042440c50391414403964420303440e241c2140d80c0014003420040d40e0003010514680c50143e84902e0b624010302092a42d0300c10000014141d84506400c00506001e450780d01ca204103207041d0b00d4000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 927494379 1250 927493129 927493153
    0x1508070207080628020a08180c0901030609080421020117070c0210110703050f150f0c070809060c030a030605062a03130e1e040b06040b0301090c17 65
    0x1c0304520b01038560781e03420040104540a42004101c480302d2168030700790710110740034584a81264020303400301d07001c550583c2c108449206214040c0110031200400b0380004010320380040e0900c00140401050300da5110f00c20030600004c4030694004d00840190303c00d003c165021036800026050008a001030030b4005060088100075048030300030745140c0c569810102e0b056003001900580c0400d99010030440d09a00f4101c0b40040040d0801036000d240501601044503450a0620550307415140b00c940f01c220a01045d80035115680b607000340702610007600e62540c2e20701351403603200c0ca8031180d91000d03010502c04129000031005044d80485a141004040d58480601901b4010240c0c0041b006040c240c200044900714030090500ca50f41c0b50590380307044580243e0784858520798000415919030710082205240c3d0740d18010070102c1070f51010466610342035958051200c401000b04e0b004589a00c07609045072000d402180e91035900100109425813200f00b08803004215407109100d500c652074410203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 927495629 1250 927494379 927494383
    0x507170313031202010b0301051801060e06010c1203060302151809010806131a04080a08071e110a0c080d0219020a05040b12160611030a120c0909050115080702 70
    0x281e41c03411107500701e210716640b82c0c0c1006100c008804400d654880351044013644d003c1c0b1641e4400d800c081401d80f894440b170000103085403a142c00c0034000c007400d0024030210340c3e08142c2070301040303030b2100151f0310000d007168088020301850b81c4000c0d00090720340018600106000c0281c14903000102c900079802d00c0346810090701c60400e1080a04170303003202021541d10004103940380c00d468003465003464500710030031040c0c00c180c00844d0300350b885c1e00c8003103000e034405540141c0840e0000d610303180401c44561461280e00807900c080e10582d040c003079901920250b101e42030140200140d04140c0d80c41c14160b4502d243c540f52482d152800c0018002d08203240a21030005640c00305a507005403690100070700308001d1100802200f0b5040740c1c490380c031000c0130708095002c201000b400c010401d40c11010030f00e00b04001d0540300340341d481200d89400521103034544030b40c0070344000d500e030070012400b00c0d40300d1071054169000c14441d0055180e42e802c2000204805850032101076046446d0f44d41e00500f0b03900d84908136 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 927496879 1250 927495629 927495637
    0xd02150c19020f030a0f020411120906060f0d051020071112070b0313030207080d02030703020715120b04061206020418050438010e06150c25030b0405071703 69
    0x40103080d07030a4281b40541000c0e404142000000b510151a140404c000b002e041d001c2110400300c240c2c0301404001d10b5080c852a114101c810544076481c0b1010305903115a01d43d520003111010056680d4140b80c00a81400f0003101d4034007a016070b2581d1180e01c0c1c100b118980c030300c24060302e00036041d5821142080b14005040401c640e0711440c42815621110b6807501201c0a020003a41140b09a0101095491080c40030303000b90000c030380040d40c0d10242c0c4d160103420a09141d001085070600900e00250041d0424141c9485500c0b0b1400080c0c0800b1800c002070013401550441507040140503000d400f080520341c014000d6032720000d10f4610b6150407540803420303903104076001001e42c145806005086100d04800c91600c4080f907040c40e80403003c41c0341d030f07a842e80c500b41d11001c3e084002c18141324141c100304403007810511a8800440c986030440c0b010319983e00f10030101e0112008001d0b094102c0210043c459809141c1c00980140141040e0403e5076640c02e1600410450045a8803401c11041d0000115 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 927498129 1250 927496879 927496883
    0x904120914280b041706070e0108041e0c0b040e0c040b04060c0602040902070c06110f071208090406030b190204120b06041e0614010e0d02150c19020f030a 68
    0x140c0e00d81e042d40880c500000d10003004200702c0c4000b081c00807640007803c0e03020b0005410300209451800b240c26001c2450b000015024001f4048400c0c00042a6640b00e064654400d4229041d007400602c3c10200e000c0e06540d0f034601030404900740701c0c0410f10f90a400c00070000c0754800e1076a00180c1e214180c0d601c495220368400c2d41409201000300300702c610300601c0a5483c117405401c0040c00c00e0741e10440c0c0404c0c0d0b4860b1100700c07a240003100c0103000168011f05d121800041e03250060454041c2c1171b4455a03144054010b6041c4480c0c0f411130039042004c60400c88410b4000a0018031140303a0740c0c6400030041c0c4007a42c880075002c1b0042c0d5443e50400c2c0910a0300c0884940d840d1901d62901c2c0c545400c644444081d1906400540381e4800c3d45203807080d80c0169402d00030180000844502d80148000c48250300040f0b04e04006240103120070701e6507001040d42e00644c048846030720501402c4018107143c403c0303206184150152002d141a44603040350510b21460094030750195613003034581010740712503001d880 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 927499379 1250 927498129 927498139
    0x11030a0b120c190801090501021b01052e0b0c101103040309030b1b0c06040b010b0c030708090d290a0e06190605060d09060b03030c0d030203040201020c0904120914 72
    0x2002e40c85107040910f00d4049546030755203030b180d20b840342010f03030944140d5201034a4503074001401c0b44108110210003501004444000c100b00d0401450b40c00e141030081042400c20344040c8414100389480d2032052000380545040341d0b41d2440c0c03a03001c480e240d041050101040c41c0c500a1501d620b0b03d0590222071149a041d80c6200300d135425692407010102c0e02404c43c542c0880c448c07004019589031180144240c0104a000340300918040c5031101c40d4070816004600c1c236400900040304401400000e490742c881c0d000000544035800303180402c811101c80300002e440e910301031000a446541894049045203808d107800c8100f0b5030b41144242c1901d9804400028a84c415800a403c1403515002040c0340e590b40040403a44a60f20000201c40d50415100106400c1c0d40d03251000810010348a610780740c10040e8007440c180440080240e03150041c0400040078190000002021a882840000171b036003002000200a0b09103410302c918030920034035914000c01d07240744002c6002c0441318507520f004640100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 927500629 1250 927499379 927499393
    0x12030f0318080706090c0f05030c271e06041107030e0310020f0405031c020705062101030b0a0e1614060f0d05040317040302060f04050f0111030a0b12 66
    0x54100c00811050075020918401840c8040c006410310005142c594007445002c40c00001d541400740040c14103511005003120000010080b03030b14041030814100e24110b9120240098140c005240303c0d000d20240c0d89203010070b5040000904400b0000c6c0c0a040e840b0220b0243c95840006010440f40d45802100034543d061101c500001d1181070401056034024055a4542d0402124441641c010003003044c0c8540002c2401d00c0581410400d2043e40176450500303910700c40c407242c4040c0d200d030642c0c051140102c41c0005c02e0038030714544217a5400502c5044880d08800d43e541d0509403006c1c00242c03440007840d030500075050500400000c090764a4100056009a46490f000300c0c80c0110008400980e0481014040c0500c6416000c000d45481002000040303500c1c9010300d4002c3c01d044940c442000007001820500c00441c3d400140302c1e5201c010749502c0e651036215810410b00d040391075840c02c40c0960801c4903806801c41c4041c007960003040400c4081c010482604208401c840f840e1001140a034030020f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 927501879 1250 927500629 927500657
    0x80307051e01020703050d0c0c06050f06031506060f030c13030b061017010b0a0e121e1209060304110418140a0506040803130f1a0a0608030a230a080f011203 69
    0x8e4044d1f403000c116814114480ba03810354840050300e07800c40d0740d1501841b5074000c0241038142484100da04091221010000b46000f6000400d640143d0500d02850100840090040c0f2402c80480c0d000b40041001002c59070364a160030340a45004a544074000c044190002d85002c0c040e400c40b19001c440b0b4100b45941c0c2e800c100110450f50402c07512003040089003200144291506480d211900c0c50880203080d60640c14a45902603101205000302194414901d08045a03019801d0b200c041c0d004a400d5592a02c1c1c5003001140d0380d6142c000340c0d81c05480d249450701071001000e1460500341c498000300140b1980c50790007a0f00ea80e9030b1680508150050300000380020b90042c01150f0010102800940b800e8403502d4034220741400f500c040b9040d9404c0e82407020006200b010090340301c50481801e101080c1044140d0340ca9001d4141c13000144640f85903d80480c00c00c02e1203182c418404050a1911502c011000410808060700c0d1a259029174600210794090491002d6804582641311008845461 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 927503129 1250 927501879 927501881
    0x1d04050702011d03030f130510090c030614070809010b130b060d0e070e091603020f01032007020109080a0206070314070c14011205070f110304080307051e01020703050d 74
    0x30084801c6569581c1c103841030302802032103142400420360045440f850030524000d0020006403e01142c2900c40000c00c00081000419050b80c185401c0042080f02c0e2510701490050714030340004080504118440034a0561040390038030400d010750300c035032141d201c5c00031203400c8400750001d83c1c1d00880800c1d003441c001042d54103d40c070b50510240c8000d1070300c1c0c1580c0e1000d003106c00d0104c03007505076007100030104140d4940047d2141c0181882d005001f40f1906c0c04110f804285032440001e0048960402079821603000f82d10824003411041810b07280d029101d5103100299000301402c80c0842d5010030081074031200000c0514849601400d12032074120303152025520110132b2000200904410001400001c0740800321400400032100c140c0380c00030f0310b2400948008000d4500c00c002c20310701020841542d610100c1d0700c1c0c00103000e00301441001c8120740114218030036500941218840010007200704071001480f03809180031805035844d5101802c00d098241d1003622409000a202440041c50003c3d007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 927504379 1250 927503129 927503131
    0x209070c06051320030c19230315250906090602062406040801140406140603070312170f0a0509060112120905041e0e030a050f0d09050307050303040c061d0405 70
    0x3421240d581d590b010000f440102c24100c10350034050031038020482d4903800c0c241e1003140803207621b900200c400d04070007195171030000030381421032708004001251442c451017441c072500461402001039012f00c04c0c0030140c80707030702e89200d00000111503030800070b4814800710f40c06014a0b4035108404c8141c01168486407081c00d40e8400c0380c2c1c403034002c2000140f080000d1203120a4160020032840c51450142420400c54404509410711316a00c1d9040058942d03000c5900c00c01d507980900961016001c40400300c41043c1c0720f28031200d0058014017070006a1340003a5281b0f1240124903801d00855542c0440140c03150020302c540845401400c8034540003500540600d80740d962146054011540d952000a003900c1f00d420301c642c0c081c4007c50a9490340302c1c40b40940340c40a0306036402503141001e1140300078290b10070600080c10604000c101d1715030f559440d030000c18040d40c0100c2140d440304800c2c10728503280c0c1c2c01a00c00700d401038041d07480007680501451051110507064116a0903003078030038041c4005420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 927505629 1250 927504379 927504443
    0x30303040f0c0519080c0d02030d0305040804080a08070203010b030102090a03260301230604050d0303090609050604053a031a030f0d080a1103010308160209070c060513 74
    0x2c40d007020441c0d032a095140140c12440c503a0885540b803400c1305250500c4181b014a501401c3d40200c0400540c90000781200d60082502d0002419910760074410154001d6130011092801b40000040c28000e07058083c111340382c001c07002000140c044000301401c03031280e00425900001c1110041000c50128000d401c01325030307404183d07d07030360304ca40207440c0d0942c0c002d030082a070511400040000305c1d00c0d400700418241105584d103d00d0b003420030700002c44000d038203200101010344807106041041002e4010103001584030040b10900d0400e46459a00c54214050703040d240c4d4078100150110b91002c003441032201c5a10090b40f07113900c018030400c1b00a440300009141c02804842500c1000b600d042100c1403003000c0101c00350114520b000001004003030003170440e008039030a1041000d11070005804490440b6131045910f03070f498080a8500c000b003041d0f00300c0694041d100e0810848841c1d040884070220714070130320080240d0364400140c640c0c809400040584541e44100d4400c0b03e10014075003218a2076 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 927506879 1250 927505629 927505643
    0x142803120b0a0b030429011502060108030904020a050403290a02040e04060b04150e01170708070b0c0703080a050d050630210a08090a1a13200a060e030303040f 70
    0x648038004001b140b803c09000100800311600041012242081c1081a00c11091000e40340f194500622039560b40200c1503085c2c862613001441a007002c1c010360840d0011a40651412801e403070400f81c002c8405910751040700d001c13002d01d00081003680c103807080383c041d500036802c0c0b02c4140d00d1310f440381402413180402460300a40c0d40c561107416410b200004000a0240c820000300035818502801e001035030034000d807003031644039140a004e01903000c80c03418280c4011010303083d11000406410385c40e040b03c50740080c214920018100d4213241d803140040c401442020b00c180703c00c0d11400d0a019a0040c0901800740342110740720151021700c418440e03a04d40700700c0c00b000c4a802c103017802549043c80212030b5041d0003915000490098450b040302049501c085210003501016140f81c407800c90203002c200001c0e16200003940040c03500c96041e445030070700e1600f00f070411010740142c600c2103100c001d0a20455115200710040050480d1003607299102000000d0003841c00d41e11a580c1e10b00c010421114116406 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 927508129 1250 927506879 927506903
    0x51510180e010b0406063c02010204050f1e040b150a0e12010b22020d0c03020c0c0915061c1e06080d0c142803120b0a0b0304 55
    0xc0c05912896020001400c030000540c9040051031908484412480e80e00560070b000701080040d802031840360b04101210448240100a81041440a41c80d0212118161308148400307080641c1507002d07000390b9405440c0d030608204480100140314002ca1300e0181d60010320440c40c0350a041607048a101c0b881c0c0503012860902040134040706130f8000c50203d00029204811a40607841e005040407034200110000f00304405046000c0b9445000001c040382c1101104c0702c102c007140009504903034055140c0c6404002d0006d0798a0024040d60100e000441c00e1301c2a0004048a4508102998091210001034040e16108403080c0311071500305014220b103a140c9607820000c4650a4010000460b213040c07c1d00c4030500c85c0407a12030844031141c0100d066036200680c0b2948403500254100395254001c0c103440c2502c1c100e01419032400b414510340100c281c4640d054640840b00502c2d68103509486910303074056007240036600360120782a002c402680444a02010892215000700450b0014041d0100c0c03000703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 927509379 1250 927508129 927508139
    0x50a020c12010b0a05060406090e09030408061305061b09010c0203030c0d0903052a040506280906210212150c030717190507090302040f0510080a051510 67
    0x2000d45008045030459440300c500c100503113454030030301c40a0f00b01102c000b4141428498020118032190041084002c9580c02042151104006990050100d6000c0b94444d14225203080030b598404801140c1d40e22580010402d00704c80110005207401c007102c1a10708250007040116451002420203a8040c0810008562070890600c500c079045107483d111022010f1039844c0491030480c11140030f900c4002841c104200012904000881c4a0b02c2100e001c1655201d140c0003a4404481640000b008000d4451010f00c242c01903503003001f1600050010403516503290360002240e861011034480012500c3d4941c001860152619002d028098046a17502001c00d044800e00340ca043d540751450300340c01320800006c19805040c241c14003540c1107414103a81000d20000381d007200c140c001206c1a58840000800151040b070503440155001003003401140c8010003150001c00041d200041902c50320b000c04121210000b503c101710607400350040503602c00c01e1000320340c00040548185400400c0c5500010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 927510629 1250 927509379 927509389
    0x3020717190b1f0801051806042a05031914010b0a090e070e0403091a04061e05090d1b080c030703060b0f130f0c0806030a06050912070b15040615050a020c 68
    0x70f00b0304d0400024043c00c11400c3c20500c100b4048900074164404000c11002803404100c0403400021250405500805212016011440380e000950544141c00505094100c11550400350600817074180e580c1546490400d401c0c0c400500d495908280e8006081001c1c3c0c1540d40301500c050041c6041d240c0141e25503142c901a03400640b03069001481411081c480595403045004542c0d51070000c062400d803070f0400280c5440d407a12005080030b200305428076072181c020300440340f20050081c040b4440c082145031144d07200715480d90100c2c45810181d408994ad180014164200e030700c0040007892000d2543d0303140800340c1074034010a070300580701c2070322014a501c421012003541c680680300270411280e40c003c050202c6070210070b010200310b000f45c1031041640f00421600c1d80340742c2016000c106a540c8407207143c40c007014065040e8058000040450502c0b902050240c0140d12041800303201444000070041514154060b4410411541d0001803149001d14010901103807180165203404280e000003072 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 927511879 1250 927510629 927510691
    0x71b0501023001150f0318020301050711160501080f1b0403120f1806050c150c0c07090b010e040522030206061c05030403080306010c0602030403020717190b 69
    0x14040201041c2c41d6061641d442031400c3c00740c00c000002216400e0300361002041701008141400c00d150360341c0c021201400000c24942011034000d0000e012509040400410801c00b82208110900582c030140100600050340c1030200c0c0c50581d0342c017200d5101c0590145215401811400c11822008840c500c02c0d001200600000e50140d12034040c84101824090b103d0030381c4800079070400034100c52407140c44901c520140c1c1543c0851412076110b85950304010b02e000b04007031032801c5100d0504200041c010401d002044105880f0040d034036115a220014415106002c3c540da001c030b946003c0c1c1ca0302d2803c056005980c082a03d81801503600d1010110700d481000748102a40103030032250410100c0d0908420505032180c0c0e482c80004620786139201c107030f160b018038040106950000004501a0b0f84a020b0351100302e80c101004640c0d03410b15150103035640c0035602c540c61b400b00c0e00000d9012140004200c0d070445690b00d07600350214229a540e01c5130700f41001800d01d440c0c140e100c000c0541d0341440740085c1e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 927513129 1250 927511879 927511927
    0xa0611180102070308031f080f0c0a090b10180e09010f11040e0a1109090412030b011704120207150507020102010501060e1011030f0406170f0702100504050114040305031509071b050102 81
    0x280040520300010701011442603000300d8449030419240b0dd01c15200d1019500e40c81e00546449016110141c06245003210b0641c800001c006c42c0b501803241010041d440500d0110000c0c200700000d64400000301c58500462080301c0b240c4d90b4050002c3c1e03284516030090500702101d1180503161900407000036140400c259020750740001c08100b102581a0140705000e0400000d0801c503800240302c81004564000013003000b081c5016030307030294414074020449103015100c00308070300d40d03003550a200003400f503041180305038015828500001044d0307001e1003811080c400c001c3e0400080340f850135026180015404400303030282c0700400100f030191049034060000b4184558400d80501d40d00d0450104142c0081d1503518040201d10511a0081d0001004200a0080b1b00c01045680d80c905000d4010024049054a80400c4038100400c16600070010752040c510302820b9032040034803005000c10040111690302c04500c004c0e0301e810741c000d101c840d4141d100c3e10803c0090b20b80305041240255079420f070b0b511 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 927514379 1250 927513129 927513133
    0x30c050f0f0306090a050108030a0c050a051e1b062704050a0603021503060108015f01021f06121a150a12050a0611180102070308031f080f 61
    0x18000c813441c10510142c1c00030200310052240b541000d00164503403081c0000d250a100160015404105052015807039240d0010140c070200002d4080b010741c00c04803050700421500801c59045a850300382c1200c0f2110080c003404040c2001407010000c1c7c60012180c070450601e4015410b01080c0f9910f0340602445840c0844011900601c2c501c1071146262403409003010b40c94041c400c014459078001d03501811a0105589500119506842443e031800c0062102d0360444a146840481c001d500b04051900303142e281d4840d00003600c0020269152000044039130040e001841c100f00f82c40e030496803200301c05c2e043c00310006001e80e031000309500c05040e0003001c4503415503002084000718000046a5882400b8031807100c421940c1d0030004251180c2406069491001c810501c1d0a100040140e241e00a40c070450810000c08070302d00040d25500401d04c2c000804081c0c180e1071899500c042115002c80707078005945c41c00c580f1a6031403229410746c2505002840094400d00107070fa0001001400080b003e1000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 927515629 1250 927514379 927514381
    0x25210e0109200402030609040f020111161a0a231c0902040b01090803090d11090711070f0f090b01031104121e080316020115060210061410030c050f0f03 67
    0x10340d6000398010000c55603c203a1051041103515120700c080150700560180010348600028401628094005041c0c18035034481c0b2290070030950030469041042d1642040c0c0c522148140300d4046030300348528002d0100081720209100d801c44454468586540ac0f2100f14500700030340c40c6c0c40c0e144802c2081c940c07089020349517180355007035042030712991300840c0c0d080c80c0060215041004065880c410401081c0c050041c28024005001e041c0340700742c1401d1802005c03c0c9141c140214001c1500e251940b40700c025025038400060068010390101044800411280383c445107041603001c000d043c4007490351705140d180c0c0310346040400a0801803005c0d041520041c064644542805a802640c0d1300070790a880c40e500b00c0900c080741e58a4180ca07030001c2c8903c45000c0c0e1848900c01240504054900d0011442c011103005c2042500803840551920074603204004d00703907480420103c820f80c56010144c12560017901c10580601c20781040e4030b0f01c42c0ba400d0051406001d031902000c2c0e980006040070055078080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 927516879 1250 927515629 927515663
    0x2030337120c0c030c0311010b130b010e040e0d08040804030c0315060506040f030b040c08030316020609010507170a200703020d0f0e01050702041b020625210e0109 72
    0x11003500101c2d005450b000681c0d180694014044541c1074101509004900080c00080d01007504030ba9800c0001074140c154540d508000304018000c5544841e01003205a58801c1d4542028400ca54502d10b1100041c082d08031040c0c801c6d5440320014005890310302007004084081095044100021889070059030140140d030083e040403142c45410051286034104410400303800f0600440081c2d0b40c204d41d085425458600d411140351209034030062072400080300308000c0740d1000f004c100500e0465001c1d150682e0307814a206080310400c07624980447c0c80c6544014100d40e4003143d903a0303c40842000002d421002d031045041208214080400c5007a0001d036001c1007641c1070007003840586150038040d1001c0e9000b03201800c034a0410b42418100314004c901d40040d5555500300007416000a1034000d02c0000711640251035940860b0001040c1c02c41401009070459001041001d4624a584089004030729401c2009403029445400c100e554850315481305002003803240d0600c5501c41c080201d55a03041c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 927517985 1106 927516879 927516881
    0x2402030a141303051f02192303090105062d040c030f050a200c0c0d0309030b0702060f100509060d080c1614040203040203033712 57
    0x80038000003800000324103003190003170300012985594102982c46059103d40391801000c070185c0210110345610a0010000c01c0d0390740d40000303100e460700c104a04c809070002d40b1040c0f0346d07940d1803041c0003d51410f95031588240c034041c05260660040c0081c205040fa042a00c041e010f2a202c075460001c03e1310a07440000b041607869020891410501106401400e0b52401c031803180d0340708050700109012000542e600201c8201c000c102900d01582800013120011804405200c510000800000c100e48030091144c000c0703030b000b8003481c5003070306072260324200140c000e0103040e04007181840143c54503003055503c076a058a1040c99442c1d60701d0810803601c03506900314030901942c0d81c61050010500c1d000011240200205c58403050100100012072000b602e0007545a030040180c032504405118800e450b0300d0076220070f5441001014506034001f0400600c00c00064007007c0c80c5a200301403 = true := by decide +kernel

theorem cover : BRFrame.Cov 927338129 927517985 := by
  have h0 := BRFrame.cov_init 927338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 927338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 927338129 ≤ n) (h2 : n < 927517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
