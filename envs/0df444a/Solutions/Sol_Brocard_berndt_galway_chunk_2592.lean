-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2592
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:09:40.59698+00:00
-- url     : https://prove2.me/submissions/fadccaad-60e3-458c-933a-c1b22ae80609

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 466007194 ≤ n < 466187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 466008444 1250 466007194 466007231
    0x10203100305071a183f070b121302030601260d08070513090203072006161115090d0e0904111002030d0e0c01030515012c0a0803040504 60
    0x11322408101c001e126a44460845020140c004d95000d480120703560a807841202104c803080b40481c1082c1a102100009801540039410140001030024007000d42818040c07205401608030f0060b901d540d01c0005940d000c0300e100d0700550158050100c0390156183c002800380c43c084261140712440300719045190903074001480c7c030f00805058440d441d15441d840c50494007940480c010b00d81d4515101c03400220034072a13200851240384a03a840d4145402c440d83c80645030702d007041542e070b000e0b40044140000d422030f02c0342e1582c03040003a0412059600141c45480d0520801382021703110341c00b1580c1007000f4000049a41200010580c2e106010f4038079000c02c2101d181420b55001c2c0509400101e1500e181c01c052800e0104003203a801100c0c100344000351108142c8125449018480d0024584080c555070180103164224044149000c1c0e00d41c4e400d000204102ca00111000e58024038100031031a6a2000980022005014103c0c0380280d407505a40741d40c036840b42c03080c1030045142080400311048902d8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 466009694 1250 466008444 466008479
    0xa0f03050f01030201081b190e010203040b030a092102100b030114010909170301080307021e06090f0a05060c0102041706090d0e03030d020a03051506040f030b0a0e01020310030507 79
    0x1e2003101caa42540c00441304010b000b05040c1d40480030459690480303518401906c00e036200105003100003403102c0f00051903480c100316060305550040c04103010349020721080d00c2d804012002c1c00501c600d01c6082c03050111030a4030703d0305002e05889110350b4009a0124003802c400910386010310001046800345400c96881741000312a402d040d100612203010690004038078107000340358000c0001d103032030750085003640280e200055a61000607039030118148461840c4a18012840c9007081015136000300cac049218070403132580b02d20241033314006141d071141c40740c101504000e02529100d0b0205001c0354000d41c4103001c0e00000e90981c040b615110040002c0c018810a40e10000e0007003095102d40c01c1d5130703c82c200f83e5403507070600052100ba0410303c810302c05020410304035600440c0c2410318416207558050082d58040c02907100b04014810000c0b40300d03400d4101e90f84281512841c1e6100c1554400401407040c1c11301c1c07154000001d10000520b4070780d0940544c1d0054064429465a807000e8004849140303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 466010944 1250 466009694 466009711
    0x31617060a0b090d05120a080c04060807030e0f06010b0720030a0213091a01091503050c010e0109170703020a06260405031905180109030206220306020409020a0f0305 73
    0x40062044402c0c0001034407802002074020394801919075190703800d01c3d20154030b0500204021861402250703008440319004164140111318107401c0003002490302c4801441003042c1a01c5050400c5521410452003411100c41004c0e12803658581c0101c54642c1c0c41445d00355001c0010004120407101e484403801c074804001002044255a141c0c00e20180312414041890056aa0250500403941c03007070101079070008116541001d5030500c0c0d40e02c001c44540d00345090400c0a41141800020000180d20010360000d0030304418504198004803455070041d0401c0c085501000d100200c00d160008400701540d02c2107800901083c0c40341070031034910b0100c1c000f0a4085402d001c2c2c1200710640160b001d500b1602481c1036910b40381c0400703a0b180902c00c242c01858005003002030840321221b0759040c0d4030003a420911340900b020f49190000344a0340249207180002d0720400311651180410b52000b20019548072005544440d80c075990400250804440400840d60403c41c02a410344680308162040a41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 466012194 1250 466010944 466010959
    0x1b15140a0c08040308030a020d05090a020a0303080c090a03080405030f06240a030b100609050607020114090a080d0c05060a020702031b060f18150309060703090501090803161706 78
    0x4003204072941500c0700010b80c2c1c2d0200410022001c1009a402580b1480341c0d11805641c070400703100d98100f140d00042c01d01200360491144000140d403045280001c50f034152410240503240c0002c504030611607000b47c41e81c00780c085070b000420486000c02a000712542201078903c204c401120f155105c0c1c1d4210759801c250003c401d4406007240d2030a83c101010180a00708405098a80e5100c200d08581550314448815240f038003004800d0f4091029809001c0940720281000b05690002c0c12455419060203d0100c2c046640700c0701707071200307810107008010820803a1072000c400c1d50003500d0718040f0301781a110307801400c4c00101402083d000f1202955805801000c40d026400114400002e0b075000c110f902c02e034100214030b441111440940102e10f0085004c0405000700410030461001009400205c04001c0c010400e09510200304507030f011001d82000f1070703c0b25035460054010410054000e000301e10100600c0a100c084080a07001a50b0702d8032201c0616010400000454070304890044c1d00c640b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 466013444 1250 466012194 466012207
    0xe07081b06190e0d0303140a020c0d0c1b0b0a0806010203250309050402030a0e1911150706021306020d090308180a0f0e04152906071b1514 61
    0xd03007000d00882c0e0003502c1d21103102d81100c0000b0b0030141d0303800c00540000f9181d00907000c800e00c54801184c0c01a5100d0303011440e103c1048003207911100c400c2410342c00e01020031070610030310400e111480790524482c513021101503120b100b52041c0b5084880c421000a5491002404650000085030103d19020004168103030600c0c080321041040080b0403400c11914a000245a40fa60b001950107805d40d400c011600740000140c0d03130300d407404070f00d00112150817400001c0089510708900e1005d04070103a42c81c4252800b1f15401000354410040011b05191001034002102020241d0040960380158240e9002d90000c5400300da42001e2808003601480c001c109440c00500c5080a03c842c42802a2400010954540000046034880c4e44000c1c00c0104980070402040a58072100d080f029004108101310b481310910308002800740c0d0a040f03091807945840310030725581d01c001d4036003d0780e0016156a001d030100c07507044e100d58540e110723a1040c485507010402c545801403203c0e110401d080c13075a0a00f01071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 466014694 1250 466013444 466013467
    0x222121a06010905041d0703051b180a0b01051b0307030801060215011509030606030c030303180c0b03150d050115150822080d05041104090209040201030f0b040e07081b06 75
    0x440403100300001ca1000c1401b0002c00014000c0800541c09034010700103501d45c480000c4c80d004200c21002e8410700304649400036006d0030001e46900459092800502c1032400d4005031028803a0142011551004111010140c0400402400510f03c20f5440f1440c0381d070b850344143e075544030340b41b1510840065100180b240c4451200e10030304030b80700d900c0c3c4910a070755692141c50031200c03103410644d02c102c41c2d00c03014028103806026140c00195a2141c1c1c217501c055a8803654003440300c60040c00d01d40100000420305251224960b1070001364000c20440d40041e0340d1a0181c000c013140c40c1104031014810b140001c03100740c031400070741003d0440c1c1c032102441d41d00c05020000f40d00101408146000e44190402c01080c0340360301401080102060000715414241000f0f2a1500b4811102d4031842c04c2008203401030f160b1400c841d400c981c0c207080c040b6440031001c1e18803016000310020584c11134541030180342c02c61302c00142030702100e940d0400d039807140e8000c6840b4901c100d0340c04070361a0043d800300540280603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 466015944 1250 466014694 466014701
    0x6070f03030c021608010e01060e100608090c180403030b061306030504080c07060f020c10051206040b12011a09060901061202040b0409020d0c0207180222121a0601090504 75
    0x1ca4907205441c00b03401c4c11400001202c000b0740000b01140c0d0f548140d00c081c80001d110b404054062030b0041d90f1949028110254224154001e0404110b042000704045900800c01d40c414408000c0103521000d0401c03130b1001c00810300703d0b03050740040c0c1884a07030901401c0003800c45400040610a4034480381c1800c200350040e06001e802200c5007071040003d08461503003448030030003500d540e5841400218060714020f14058110380e00c5445481c0c150b2034408899005011103001a000c9040200306550b00c0c40018000d144020326a904002a64031000c003209043d402941349142c00c0e0740d03020840403e441482401c4004440c000e410040702c0b0010b11005026041c0d4105500c0d6604000d49400c0d25881540c0c69500150722580200783c02140701b41c5030213aa4000c800c0c61460610003014500d00e808002c0760241c2c09840114003066001502c050b90081c85d020002c0140300c80424942000e0b84d81e43e02d442218600c5900362001051110309010761064a5001ca0003190160b5034140040d040c041004002c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 466017194 1250 466015944 466015961
    0x2090a153005030403050d0e030a0b06030a05070807150305010b12090a06020d0c0e090714030601140705060a1407140a0509120609060a110706180503032406070f0303 73
    0x2860007906507215260740881110003240700c1c070081d684803440c501c5e0107440c00000c0810f5609000c101001c8c4111a24001519003003079820548041440d00d4010102c0d00340455058086e0a5015108000c510350300000350320412200808207001e60460b80340003c03001c4420a000f450005035003008000c80d6240d060b4005904009240191455003201da52084201e030300034031008030140c0c0c40e503528502203908500e401907104401d41d84203041d4505004000d2041c1e50715070840d5030003040031011403100c1c0d110b409588401e02c02c1c001032554910041c2800399540c01e044420885443c200741210300481000d103201c034080c1d071050700c402c40d811001250400c203980001d0a0703401040402e000b1580f5035992031104955401c03001c0c029104600f48504580c0c24950003e00340c285442c1032640140b01c04440000320740382250015000031302d0803094401411030303408010004d8034030720000c01072181030f0b200031441d060300c1407140c01c805c075201a2903010701031079009440b03001c2c200444030707506080801d00036000300c0d10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 466018444 1250 466017194 466017239
    0x50f0c09010c0b0403031512050d0509030a02040e0316060605030c030109020109120201211b18030b060d051515010c0b0703180c090207020306090c1f02030c03070f02090a15 76
    0x103003c000300c8070601f1868041c2e409a80700746d1142c8504401e00c5130900012810181d240740c102d00d03006160700801d03560588400001e008550300c0422001c084414010340c0d0310311070b806040d503002540504100f0054980c9008152203405240301503440c0d0314051140610560b8183c41d0305c10032929051502d40e0341c0c548041e0981c107102c2c0c2003c2480079040c0714814900c181c0e5015a00140702e503110780781c03410b2041e203480009040c000c0e1804001c018040d01d449040c112640581c840701c0d0303a40d03402e020030340282180c030000300a4801c0c01c1d2001ca294050400c250710034222202c02d010841c69500045840d550000d5010704480b2204000c1078020f84039400082c0c14103102d155200a200191307548039641855030340440780d025404504401103260070321007207400c16640002171901c6038203907000481c1c0908141c08109072520003a0620300d407a00038000d03079038400d084000340d03a100d03017460401c803140700302e000c02c1248540da9074000118803032010701c200d98902444003040900c907402e0a00300308014200b501c81c41c0b07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 466019694 1250 466018444 466018451
    0x20117070f0503070228030e0103090206040b0c10020a0f020d03020427020c0f0d090b070c060807120c05120901021204110d0507031419080708071e0303050f0c09010c0b040303 77
    0x701b16071128038041c40c01c000c54558020800e07020303060041c084804841d040e81094103201c400c0c03000da52007400307550940c1c1e101040240c4e1486846904c92903c60b000310392102090000c9464492107030040c0518812403031a40a41d0307810500103c00f14220300c620300614104100341c00f818107035060a9070350088882c810b40d2005181c1060710088510b000118000d40c00c0c55480311802071402640004520024030f07960401605007069590340d0703c14803070079000340b50401c03203203400043c01c04c0c0c4a014000a00c1d0580c090410001007800001062030303008008004003c04441d002c143d20000510850b44030380444080f4862903112070752a0030380c44050141c0c056100546450300c03c00308205028001c000c61150410700e60403d030742111a41095481001901c90402c1c42811401043c21207044035040c07640507010b1542c0340c00d185040c40c0a4500c54141030f140226450b2900d08141c0c255100a001d040403c1101099954810f043d036043c1c8100094680000c84404d17602c40001d00514025070020710904020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 466020944 1250 466019694 466019713
    0xd0b2d010603110d020309071403120304060f090209090307120906081302060c010606020102090a0608070c150603060603060e010e010642051305060a0503010e1905070507020117070f05030702 84
    0x4e00c180e810949600f200380c0c20441041005002e2400c1c081480e80064010b4000c0e9070310352003078840d14000100068070054883d09443c00a090903841161590790083c0700a0a41c2014a05d03143d49400050f022180300521804009600d409079200c9002c98a0580c0c07031300c60695079510448198507040800300d0300700109204004000d50f082c0102805055154001a00d500703100040110141d000d60224003400104003d016426034061102c3c801d9a8010640c414400c0b506c0b60600010714095001600c031600d0280040b04010198020894010120000340070902d4448840ca0888803907100769000140c0d10000c980d00d5203d010b050411a40c0d49000300b10b0000030340100351042c24041340604000410001d180c5a400f50108a50380c0900400d8822600700307203c00d000944103100c18003d12008170014800035014180d030003c94442c50300313291001c2c42039041c4980d000d022038028200c01c9012400581501040d52000d00c105031140721940c0d156200550711b05002d03102540701402a104501070f280c1c14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 466022194 1250 466020944 466020967
    0xa0204050a0902090c0a0e0d1e060c030e0d0f0309020316030311160b0313060209150c0f0a0807020906030f0a150c051602060d06050d0b2d01060311 65
    0x49078441c00540c00003103031101c00743c410007480400040800284070303010320100c10403c1d0301c002a0a0320100c1500c0d41d00b00421203007021342c0a6200001d1101e00b9408020300042000070b03a8215a130204481c2d103090003101200101d40e9100d4034030a10344400540c0d020344030f1030498400d4001045c25070014041c2c5a80303110f41600d140b003605140e0800c0d00071640c80e1190500e04c036410070540d070a044480c110000c00300d041034240d00e240d02c1b000d0580741c403d0a00c0a00c0406001c49981126401803000f40000e0625402123004425500005081c8040e40110f1040c40482280884c04003d111362100d2240c0c07400703165608018240c82d0261036036070144221058000c24110401ca0b86031041d004004041980955100302c0013039845400001e030401200703004914104444c3c2519505090381200d006488114006400c401004282c9c40264000d2002d0340d004140f00c4e10202c01e6000d0901004050380b07040d48442c8410f07a0140d1680c10000e440303840c80040054034401e44c80384c80d401040c0380c03000c0d1404850900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 466023444 1250 466022194 466022201
    0x31211041205031b03030f040206090a0b2a07050a120507082a040e030a0c080c030d060e0f0c03010b0f040b0d150608090d0305060f0a03030f021002090913050a0204 72
    0x2202c07241d1000035541d403101c42460180451001c00c0303005600d18500300c42e000d221000040c0000f4003400c00480c0540e00c643d2040a40d00150041082c8103441e20100b4401d10615840d15046c0809840c1103046004454404502c05060700c4000c0c002907541d61512280101e240030707540c1c0585240c052182c02055003e021301c0720340340c481030180c1c510518480501050001209041c41c05100c2e0b40342100281c2000004004d4231020185e0f0300303140c000c904030350405071a40d21400c20305140500000680040d88001e640c8031105540d45500907024035542c3c01c014554100c410b17200d0076004901840100b0014900d400240300124400c65450f0600703a83d9902c008094011025000303100351501205410703541a02480c00c001c0106240c520514103000c1d0007151a1115284810100760b120750024034951290980683c010801404686204c1c0da2418000c1106108821500050141032196020000d050003521115807000b4503002043c0c6400c4498505001c801c142166071b40104400c2602581c0c0720710 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 466024694 1250 466023444 466023479
    0xc03040509040c060801051008010e071e1106180a080d11030f0108010f091e062a020714030706050c0129150c030706150b0711010f050703121104 64
    0xf0030407801070403c10050130350341051300601d001d5100a80c3c407039820b1780d2002d0000e0440384060b18180450b02e44800071150610030028400c250505d43d0000a0a25845007000740003505110603111192a042c0c026030b80001b40d00350741103142d4881c1510601040b070341c1c0001e004003145813000060100d407c4040050306d410032600d40001c20781b24001044a140c0c00c1c011800400c0340403000308441010740d034580e144003610042e451042c4a40c940234000700320056102c90403018072400c2da88002c084140b00c0040d115045c2306101c00500800d000041c1600444bc03030346400c000000d0141c2640e6081060440f0250403081c0410601d6495155001d0510300d100348541043d8052003c1c0b2000f14150f8084c40b0740d44500440b581c00443c0100507100d601e8201009403042c49174807850200c1c5040664040e80d19644070340c1c200c050650400a2080b080181500c40006280001c1e01d17103012100001800b621309001d40007020340810306611a60740701c1042940140000e84040b500d030b0b420715855600b0446c5007038210 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 466025944 1250 466024694 466024703
    0xa060f090e0702010f0c0203030f01140406210c061d0d0c0504050702010902010906020a0f0213020903030d09062a0809030c030a02012f070b06030a0b480c0304050904 73
    0x70806000841342c80c6c000d0050002c00d500040d85181403100b00d1241d00101441050302c0d410300500708c1c50751552260000c1c0000d10303044411420f4141402c132841d85000802804a900030300c00d00001a159004440303489411030142030850082c1206014130440b1100381e00200d5003a0f03032244010800740e59602c50b0a004603e40e134000184c5100a100140c13107400150002000d40d80845440342c0050051301009412542c1680c1d885501c80e903910284020380a8900c0742a0716000c0447c0700424851903074021400103010704401d01c0344054202050808000d00369000480b43c0551607a18000c0703002d217094641240c0d91904803850521481c3e281407d642003a0301a6005075140c0b4205c0042c040450085445043c10042601c08416036840901c9244517081c401800f003c40e840001c2d20554041c80380f9851300d500700c0015000d500d080349400d20310b98449480120114079426614005c0c5024082135841c0c00c003846030f01d074045412511038a28903002640c080c5000d100c01c10011030136441c0d41142c01e0060f80705 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 466027194 1250 466025944 466025951
    0xa060f061a09030106061e261801060603090209130201170901060315020a0c030c051510031208060102061f0306141815041e0b040507150e0a060f090e070201 69
    0x6802c105400d45000e98012410001405684c01d1000440c4e0040c0880d0180c0d400c0c8660802c901c4031000030440c4500c2e10403254000030004100a03c0d051a146103500010741c4020000962580c0701901141d204103400707508003051500240c0008444841c80c5662070050618000c0925000c210618a620803200a5407a94541c3c07003c2080012002c40d03002d40c40d6100d2025030620580c4e6000400d42c28020001501b04000e0311402806c1c001c040c041d0840b41043c100f80c1c80410b02c1c2c07068400003035134228441150b0412089010101045c0301d41c54035406080142c0c0644640c2e242c02d04480c01e11104401740c09103000c50f005e000000648244620b040d80055051950a180b600900c01d00030b4444410706212242c20201c5100203a000300309000d584294020b001480350400c04401c1408103e1191000b00f0281403001408207109001903101c0c2103607050400880610008002100e0304e480d00000320f40c01c0000c001c001e014560003800c50000040c081d00d025030840d543c031200c0040300d2400344d80d80c00141c1d56 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 466028444 1250 466027194 466027207
    0x11031207020318040605033403120815091819060c0f08090a241503060b01050414040203070e13051b0f09210321060901080a060f061a 59
    0x60301d0003c0e016400341141c08003c003a00c1c0034046510754000b2000e120310801c0380c09107010310307140c0385503050340418890038180710003512071070142a080100b00c91100850265800104400c40310400795803220000382411800351206042070300c118802084982e000e008000d1003524a07048c445108032404d00402e00845c6110b003454000d004d2510811003002081015010480280c1000a4500c0320030303130155003c0d254600743e918140d03181d25944107030038280c0e080020305100042c003100b42c203060fa4042c410800001c011000190707040d00c144d21078400a850300804404032841c003580036582c4903400d424400c40c441901400211440031041b0110700d050343d50001c0c4603584911501604880e200c80c030485180100300940c1345e1103070184e607459074883c1540c00e030708441002c00100480309040d02e85013226205c0040404400c10440c0c584034550224004400048507031400c0700246040f51a01c0c80a05410070054450b81d000e4201d40a05501c1292504c4001400c2d2000d4440d2907444c190400141351940b8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 466029694 1250 466028444 466028467
    0x31015050f04020406080708060d02060d0903030b09060d03110a020d15060806040c0e091203011d0c19080a090b0a050106020c030a020f010e0d1401020a120603030f110312070203 78
    0xc20715054980200d206000038400c41c4d03003202c0e05070707000f40b405d04041c00280d4440707002440358806000c00039000480851501c0c060900364210359881c910a4409005040321801400240e000868800358050707400c94016000c20f02404042103150010000e50384080c4507034020440007040c501040741d84c41003000c1c0100100381c0a110307540107440228040c10390b41c00c182d100c1030624840d6002e1084661a90030101720030803801c1140800f0082c5580f01c107500c07981e541142e40c03070949001400c0850304100341c0c00540e1103251241264098809010821429500c0030030481365140000c0c40355235281d64900c507020200750415035807482442c5808000c00e03c1e42c10424000c2c101000c1c0c060007070007680310480200041c0d5904444c5510a5020b01c0e1806e40065480e0000381072403043c01000d07184841c0010503000604041d0001c1c800350480b5160070021a070064180c1040715810b2001600158000413a012a10f10075010f04040c0d058440032030f8180b5010110300c4c0c80343c034401c0d14540e000d0b904c0040c10f4007420b1b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 466030944 1250 466029694 466029709
    0x71a0c0607080105090121060c1214040b01092c0307060f020c0c060d0f060305010615090303141305060309010501060801080a0c1a070506040807021306210203101505 73
    0x81d80d1400c07030515450b040210350b10318018011706040c00900d000410382007204e00002c1000390740007502072100b00c0b0804005000c000e92608441c8500b1300b01204891203c84640d8001c0c06030707500610001407607103807503c510010301c1c5405810b040188441280c41c0304002d80505210f50340030600c060742c1c7c0c0c1c0d600b80c03800b20f0464100404401030306005001c6401d5215001c5100b204200b000c1e00c0c515942c94200d030b03080d401000c103080c00190302c9103400c00120500005600940659481c00040300700f09400443c1651014014031001b800254044442100402443d02410f0f00100780c208104000782c8410000e2121b030001c640b61201a0b668800411260764032403055801004264080c141d00509070b00e60302c0074402540204405000c89011000e81e0580104c211000550050309950081c24149050400c3d540000026881190001e0024400180034401e510071500201d03080300b07103d03009200d00c0c00300000c25503080e60f16000b180ea2280b02c4014900801418648002c40e10301d24504110800c5400e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 466032194 1250 466030944 466030951
    0xa030501150804080a08060604170105040611030c0412020f04062405160b061c080705101503021012020406051c05060109050909030903010f140901090b1602071a0c06 73
    0x2c0040315001d220100707500314200c50341c00140d0300d0085440c3e42c2c1c1c0808680c1030700c113a43c80407180003611800041505010750000d1301a0344200310910051020303000b820890701060719182c802040030001000311020780c10b0f490302c04500c0030741581c841c0550710380081d0803580c0c0c1d0f50000700b441c1954201d14100204020684800044a061160604c1812114440840d040340c200410703c54121000c1003c0ba40c4080c00e0303030105442c440d1103100184c40342c90000e555070041081166a40320b4030b008188500c203d401031404213606a412500d1081c80e540803c404540e0007500c004c18400810300c0c03505941c840b80020800391043d034840130354400000419001d2481d500da0289691854001030110b80da90002d403000032104201c46400b16510364035001405c41c812243c4040e8158a042c041c4880d48003542c00c0702076040c2c10904200f08aa5466a240c0d00760303007400c0e0009003000341c007100040790540061032250b000311061048070640d94a0390701560700c40e106044ca0b00c0c9640070104006451402c1000b0840c0d2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 466033444 1250 466032194 466032197
    0x603110913060516022b0f1202070c0f1a0f070303020702210f1209040914100b01030e0f0d030203090c040e1c050a0e0d060e01020310050307080a020112200a03050115 73
    0x40d1000c0b02401a002c3c620102010100145500c0c10803603503200342c0109168008c03810f030443d90362600380f81010f0110340c0d03071088041d8000725880002d01084007064812175074a81401a034a800c072900044040350780318800407002d140d800e015100c050f0f01ca80e0082442808051040307645080c085400e075240643c0c581c9130720140d83c00508082c00c0c03c541c5000350303582400203440114452403103150040703101c4241d0280084c180306540d1001c0e5003510320307005202c032860203072010002561308140c580c0e00d03101912403802c2140e02020b00d504005100f54015680541e91109640c481c010701c1d00000c0984803220171001240c0d0110f140d2030308210004030010003201e0740e410312a181148103040540b100c080204c3c00c40c42000d1002600080c441030340c1103807900103540c2008560700e1800560f4108424814002d0500074401d0f0000441c2c812000240c4140942d0140c5621905440340c02100c03020708000604035605a0540c2111030204894a0191024042c10307240840c9941c1080c80c40184000400c42880 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 466034694 1250 466033444 466033483
    0x1505010f170316020109052e0f0512040204060503070b04080d05041505030403031d0319050408032a121206030a08030106050d060824060301060311091306051602 71
    0x20307007094008200c03160003110038602da100c454507000583d481d801c0c40d8881a04080e048509501e00382840b44030004000040078000d05000e104942140c0e1410705038030300008610100040306102e6612404554424070080000c1800e07502c46001c2801c01c003d0303600500c8a0003002c507091100501c14480550502d21501d4080d041914095130300080c9141e1009080c00d0010000100701814441d802008a0828402864206032a50700c601c0c0d949920002540c40040e02d1014445802031140c000c0720100c3d80b50000950801c4000c1d500070f0b51100d41e4008410216904a908900070700c02440200341c0803046541158980d40700c1c001d00303e05100d00906451180e00821040780024104100b81c905407885440e01d1a25020200541401400c040c1c0229040d0710511b11024002c2d240340b06101018a4003200001481e11081c1c203040c2640c9842c000109210380100b00740c40c007400d0156a40c2c0e809400c01161001341905922500101e92007034a03041a10394120803035441447e010080c0000180a40c072201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 466035944 1250 466034694 466034729
    0x209010b2b0207061a060403140a021008010501120e0303071803060e0606180403020d051620030106080102040e1501180f3002040c0905061c0b01090b040603020f071505010f 76
    0x51b419120b00e02000300580e444815240c034010040000b50b5a00ba4090040f1700703112070703061000e0180380c0d00748240c40c00030341000c221016603001ca000d00c82c2e03803400c00790045040da00c070440c050f5038404003807882c42103000070048008041344c8240101d21000e013a50b0090051401e02c0700c00d10108117413001140400c014440288000aa0b000030240c0d1000400d24103a5100c1807004e0180d0007411403400003403c0c0000000c03000d407181024219401404030700700d0003004103540d944612404d1f8040d91013440d4180c00d050300014600008500020944407051501007143c0c0c1030100d1206007141c1541025490262000c0207101c0c24501304002c0c42c8002c1d4200d10025080045104428442d80c0d040000740155219061300005a024880d54006420020071b150f072a00311b00c808040c070415035601010805401c100103006a07502880e008802d40314041ca07124601400e259003940a94003e40404180c10010065003003c2982049113071a104041540811154905280d00310610b0701c0d41c04c10000c0e0924803900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 466037194 1250 466035944 466035949
    0x5040b0409440a09151b0807081215031b090402030f0d030605032e0b19060c020306070807051207020c0418021e060706201201150c0209010b2b0207061a 67
    0x1900c450501c0c60201e00c0e01201511f0b0032000d0340145075004040e0704021070210b00e024103000d01184a034a5038000d440076501c0071010035a450080414a0110743c2c140b0f0300f014114104500c80c2c90f80300b40054101c0325800c0c101000d192411640d81d100d4000255203003000d018910b000d0040c1300106000c0a2101000d00b000c0d151288840182c1c400e480f0103e5807210116429100d5003507030141000e4807101903c0d5141c1d0b4100150001e20256822807090181c10005185d15000f01110f81c0079503801c0d65079906110081c0010440c032100034140900354401c0030207407801541c40b40160000d045000b031454009801074818404400e005862007a02c242d401a58501151101303015a000c05411488c040740b01c041c280490305082c10742070300054107010b0000b140e9500ea003541d00d03914101d4a45800d0030360320140070102101e40010303400c4000d5010040c607004110440c0303020301900e0380a03110080601c503805a103402c010080500480c0344800b680109085c1e061211a1140704404d0820001c0c034400c05030340100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 466038444 1250 466037194 466037207
    0xb030a0b22032c09010b09011713140f060c071202010c020606040f0f05043020010b0d030207080c030309030d03020c10051005040b0409440a0915 64
    0x6004000704218040011a0941480190f0103030042c008507840c3d610b0b88000c144960090400c203000c40c40b2007001c164080c440300038003071165817502500d2003450443d50350001c07c260441142c41c9144541e0006442c1c403c003c0c82000d0048a00e03280340c03581d5007203c0c41c200b96600683c4401c1300559140c06580b401440d004102180d000350100da000644440142e0410014807003100c02d1043c5514205c1003000300002c000620720101c0c0d003402c01241c41810041c580c0d440d10100b90031074000502011805111714901200340300341c2e030040c400200e031071158440450101c5807500000d50060f03118007410070150406200104a0010582c051480e04c0100030100781d036441c140c8201ca04040c1e001a5910540e00c040c42400301403a08501d0600c00c0b410f200e04001c0740b00c641802007600c00c9203448015800c9103424410071500691001506080c010001c0300c000f444802c050b40c40c0c205402c05030004040172007a90700207a01c280b00d043d0054550200c01d200070410b5940d90048410038014500c144802c50300500d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 466039694 1250 466038444 466038467
    0x708060603091e0102030a111305150c010930050306060304031e050c0d0c1e020f060f0c0609030405030307110307031e0312051005010507060b030a0b2203 68
    0x40e909603482d150700181038648245810f0344050750b070780310490100e104410b4008501560746100d0510008000030055001032040c850403d0010917800410012420b00039001d400d00e1149209081c1000c082c100c441d42174901c03c0030102d58071942441c1003100250144952080501d4104080800803011240508a44406001e01e0f20955011000904152041540d001e0240502d41070010054803024040e000750000506e02a50303008209c65030212512809012010300c3e00000b0041c1c552040d520b0120710301d18034130300580c0c1020360000525400e0b160f800c000c165a845440d0b0065441112240c19402c1410140c107078015038100308800c200a0f50000301f0f856149400084554a01a03e20f00003494255564002070000d2924034080c1c41c0c0c0d8030001900540c150007510303150407611000089000322102212201500e10425400b48142c1d48554080c0200502c2040000381d0744003002c002034076100302040100c5041114104000400c500e00040344402d003103035096120040c207141e8001d485080c040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 466040944 1250 466039694 466039699
    0x61614120403031d030d0c1202010c1e09030204180209011a09100207080d030218090105060a0e1c0c06140a0f0f0e040f0f0605030a0804120c090e030307030c08070806 73
    0xd00b0072081d410b284654070041c5200117044814075054058003038440001b9100c20388034420642c80110b005401809a607003450b189590740d41031400300c1d10b111000c01d40048252000c00225410220041e101da10680c8400345031041d8480103030903140704000782028141c00c10141c10746511803e000e640c040f0400d0f5141d110b0304682d48150200c00f0003003203160690a038410f024a1007909121074905800d60700801e5008500c1c0141c91102c2c2c40c4c2401c0c040510f501b842419000001000003482061050310240b00e1008010074000c511407076003c0b2800c082607004810b950070410310408209146e04a900001810070f400c3c13203142070604220018001040c00076150082c00b14180000c0380c00c0e0711400c103140314010014800c100b0344403180c1e180001414030110901d9082d140580c0840c00e8a0000f034030500d400e600802c6603191500f481080031070009442412030304000700c6003010950341c0c120b0244040c0c29051071700039512444c28020080507910140080700c10b100612060044440d0f01c0300410741c1c003840c203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 466042194 1250 466040944 466040957
    0x50117070b090103052d04020906120c060d020417010b100c03080c030a23090601081f0209040908070303150b030105090f180a1b060908100f0b06161412040303 70
    0xc000c000c0111141c14032906e64416000c08102411020503018640943c0c000d0741d100010390389000901540c0c04040c0e051804642c000140300c03031141b401174010400688100800b40c01d06c0d0350f640d48060008042c14081c0106c0e5102e59007e00182040380b06a8071081c610320301101c082080351000b41801d44040c04801a8040010015034103820b05d4008006800f46840e181c0558400321200541c2c916060303500391411f009000002801c9000002c01d40da4580c455000c800d0003401c0f0079110b0009510058032940c1003a180d1903100041000c41000c3c0c604035001e601c0c04601100180d01c00d0b80308201c2c50300b20034542c110038130040c0304907150902d1513076200c3c0384240d0301d06183d1103004403101003200010020b03041d880340911260400402e02c11052550740301d0031100c03990340c1d25144c4c1581d03590b4150090a600344d210703004018504040d44c0007280c151544540014900c459603001c1401584600e85120000f62011068000c1140b03600070300ba07541c2c1d10030000c0c010441802e4405e00b15440b442c40040c080080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 466043444 1250 466042194 466042201
    0x81519020a0201140c12010807081005130503121b0403030c08070312061203080f090a0b1009090303060825060e0f1201060303020d1b290901050117070b09010305 71
    0x4d600c485402d4090f51071511191514000502e0103034420684485401c10020000a00303550000e8070100350364410300901a04440c035010440107000090102e203180341042c00407404a01c0c00e0004126405411441c400c0a240035a01050440783d00514440500e000304810008039500860304041c0365400403405950300d0301810216074101e4194030b00011213142c10070004040134403440d40210240b003a183d5690680d903100d20102030172000c94800c581500140b6009002900041d13011741d100c560040c6a416441c0c0b41c1e202c0c04c040350380e4100b0403800309950301703010702002404001074620686c1211242130704007003c00211122141500c1001c2c1030004c201c00204481c0d44100400340c0c0142c007c4e25042c50b001d42c01c07240c5070103000640b1080d409401104e075680d907080d04c40d10300c0c0070019035a10f04209065140360b840d90800510b04420040800c404140c180c10202064542405611b036100081000d50403d5030682100c6000c0d0903e5250b0742c40184200048815402a110404000d0800048655 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 466044694 1250 466043444 466043447
    0x3080a0f0e010c0e03031303140a0b1f050306040201090e06030a06021914040305120306060c010c021b03030a140304030311030405070603110903030304020d03030e16081519020a 78
    0x20038040045181400c01d0486151494154044034907200c1e40d940b0007030800c2c219401c1c90307220b208034a00807800040b011420300201c1c444c2603402500d110400101c0d5100103090300c85a0010764203840305041403134000340c00002408004070a0001e400210080c0c03145082c80d50010704500420320458040e00004400a111550280050300d82d5581040d010765071054402150b00e0744070011100080070852303080362440c80d00101025142906e80c0b001c001d1509400700d900e000e500e5000205800c0d0312113401c00ca40c400c0c2c3c0a01380034a510701d16140c4c005250500307100d0340012240d26140503090003a4414450541d03841d91284103080c05a285254403941d0341c032141000c13406021001e0645a0781c0f4000802d200800000165040444205640070440b0700f4414500e85e0313080c4101603003181e240c8c1c0f051007c5809440d1242e07548002501c2070400044490a40000c981002d00036445000b07511308020f4200145601070041c48440103681c10310718040d18000305000c0a10448014010005501181708090389 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 466045944 1250 466044694 466044701
    0x2121513151d1905010515070203012003090c090702030702010c0212070303050c100213050f01031b0203120a050702060f0a200703021006030503030105120102070b090a02030616020a03080a 83
    0x4080c05145840c0802c01000781d00350303005003507408078001d400c80d01601c000750780035200e01c0d81a00c4000b0b10740040c0310a007201d42d0010303401c5240d080c0c0c0c0c19580da40040766a00340d0300e0018100708160507030413500d074036124a031a0b043c6480c00701200e00903290303070003000f880541c003104070740005a0900300203003843c400b40003060511340c800c2501c224510820b40c01009244d080f0015010308100241142c80740d9507592048000c2c2c1c081d00c900080315410144040c082446e0211a5448484040c5400959205141c0450600342014104403026820004d91441e40f000c4c4200402d40c00402103209014a0074041002540d44000400d08043c03440e4200128980f1100e5400000e000703030442d80300c55903091680d040071610b80c0c05400101c0c091703c104000015100941d00402c030440b030300800554216860b10051120196251024072007555080000c40300290680c080076015271090300091101007403030b02c14145001000f03041060303856580c00072040d84640c00114189201c2d49407810f840d440d2103015034032010b03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 466047194 1250 466045944 466045949
    0xd090503070503070605160c0c2303010609050601030c050c06040b04080c03030106080105091e01090c020f16141903020f010507051b100f020a0818130212151315 71
    0x6a000014003501030080386e402c4540600035481c1c242c101008a0300c42500e881c090010011f004620b03a0300204146581c0105c42100c09001d0b01c01114450010350000342121071540081c42640d03520700c01d101c070a50b418407480344009040d0800610f4a480c680d1200d5403500e00074030003441268031000080c1006040c80c01d588a6850101c00c8948030f5840c1d52004d48080003d000311805490100c00103203421480080700c3c1c4910f02c8c12000c04900b139080410060140c00038190700000d510a940b0320750440d080801074030f82803070f840741e07441010b0700e0070f20070300198888580c0039080c81070891a003c40c58400c1c561700850122541100c4e04c0c1c0d07003103540b11b005940d14000c0c148017401c54050000c89441030ee54842c05203040c084c0480700e44a080d0707840401500c850316241c0c62000103900004103000043d200704014100248414440021070010000140e24071007511001000150003103140c05800d0101c0d81429041085030003010507141644c80403034805d1850480080901d911111654001403c03200340402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 466048444 1250 466047194 466047203
    0x906030a09080c0c1c02130507050408070e011815090921030e010c050307230c0609100c02060f040f020f091618150f090f1206050703110d09050307 65
    0x3c490369031040c000e1301ca00502104602511024420300422945260707850919940100300e00b00051504000c1e03c01054010108030600c48200800b241e08041000800014070050500b41219810300d682406a210001400e160181c01c003c666400ba171040d1140e5010307240310001c00101c01400d82015400144684141c07000b006010001003203442c1e03d0780280380b82c0700f9040000e010340e0801900c00c40c2c0c0d0344812101c1000040d1031440148280c2d00c00c9028600e242c9030000d9584c18452800046403e00e80180c0e41031549611001039104020380a0040782024042400034042910b4020180a84410002e00003000340260700c02040855403079151002d0000c4000c0c01d40e4045240981d030000c1504020503403140880d1401000c07640c080d00c140095025100c400d1004500607104400603962242c90348000001c2c440010000300da01c0038030400c14001030641c10103405c0030000604000c0c089440150101040500307040340c0c5100e0340d0390142101c0b200305400f140062090060f040090850050400050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 466049694 1250 466048444 466048447
    0x110d0b06090d080f16030c1214030a0f0905030315090109090804060809030c060403120b09010b04030209092e0c030b0307030212070306050c0c0606010206130f241a0d05030906030a0908 81
    0x6086c1540803c1d004081c9114003071084407580e140300c0903643c031050142006035500f010000078100d07180e80d1b04250f2004940b00700215600d40c05903502420364008031110101581000c10040e0289403540038540184494074081000b010b064803440d15074415809560107004842011401c0c10008004070b0700042c4032201550341c942001d2030300400c42c000c0011901120f0303081c0940072a192801c45404c6040319981d50005140514650070300246030f10040441400c0e0207691007880420206d2264500101c400341c1d4040307010403c00c1c442004035600040c01604141c0750021049c42030310001060700a42c0e80441e015515034800d818943d11b0310b145508002c0c801c40c200400c1c0000d000c2260050405021544191649507681d030300120b07a00d0000300e40c0200716002c0ca21105001c9607040c030000c00100c1c046e500d038210000321810000344da8010000d04203000b42d500d580445149030400306c40a054442290051040e5034540c0b02c2a550b0300851015a128040000219251403401c3e4401070034541c0c00348205 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 466050944 1250 466049694 466049737
    0xd080601090e070f030f021204061d0a0f06050c0403051f0f0c03020309070806070801030b190e0c040f050c091306050418030908071a090d06110d0b06090d080f 70
    0x7030084c03d140300881c3c0421b0405821403c110b866000b0f59240d070003c2c15500e02d036990b803915424003510000c1404001d0b50740d15900908401010302460310054003d11a101c9030783d0062920b0b500316040101001b40101c018001403000600100b0f003030174120400b90529401d004070041c500001c0104142c0c2d4000185440c3c00d0748100d40d010740180d440360032004140e46410f60790f0f080c40f98035514102c51003800151018018800520900c0900b0b80010000d12040250000c138985102164002c0a0344c071407552011000e160103142c0f500543d6402c1ca850f03078082c0028201010410b80c94010704100ca4815030306546480c0d01e002541e4405030007054000c2041c020108140c0300309c425281d2030301c410342c0020800840071a40c5000010b46d1411500540708801c525200d036072410755a9004400f540c2d80c0a4201003e0201042460107142006040d901e204d5607a401d0310451582100c0c428148a8052030040c828115241d41c0c19130801c80140d0842c503d01d42e240707411207806045201d2101481c80951070807801 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 466052194 1250 466050944 466050947
    0x11270402041401020f2d0709060608250f0c030c05060c2701052703011d10060b0a08060d140319030504050c060901021f0c020d050c0d080601090e07 65
    0x41282050080c0c00781c1d05d212110030606a100c103411010f440310001c858405103011210000c8401081c580041074440f040d0302d44007441c085c0d031096030000700055030700c0050001c100304040740382c42d03c0040e6a5003e41c0d07540ca0182c0c0604060f0756a42200d0500480d41c80302c20606015108103104182c0c002d0555006103400c4c04076400d00d4206c01e4400e90a0b07100c00201c42000e020401e15080c0743d100584810341014030000c3c2c0ea028000000e10002681c82c01825281c0140d1000d00425400508a132503040c070032401c5014140c506000e000903038a2950802c4020020b50541104a5014101508c1d100b101c50341c071403000c40c1c41c0c0c4548140c020070180f00e0b076042500c00b24011028141d4000c0c00310341c18074919403010080341a20320641e009021900003016601191074100b00a0840c008180143c3c5c0c1c10a80ba1031304000403000a0000200c4107884070014805107a0500031021003600c1420300c54140200103600a65900880c48010107005d450004101980e0250484000608a40c10030607180d00c0c1003e0f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 466053444 1250 466052194 466052219
    0x19020616021210050c0a0804110d120f0e010203090901030825030302120a06080607031a120304051804150b01030906050a0c0801242106080a151127040204 68
    0x449242c1e0f1807400380810301c1302074004101c0780142696900c010042d191525001c440f03403105d012480e803181c001401c074800641d2520354904410002c1d2101c80c031186103400040c0444012400d0141150410420030255030340d1000100c0c15aa0040000351302e4500c0c1e011141d100c250b034500548114400ba04040c020507a05030010802040e140c0399829040d21941400d03019200f047c003401010340c01100008610900c80da001030300303116003140380d000504194030103d0f00308920344a0300019600300180610040c00d001c600d00c0042c02c6202040c03005882c1a88911150002070300c41a0501521a91019081d0788aa0000702040741c010408110600304003004030024090004200c0200b0540400010204046151003070014180709404070800b666560840d00211140e5450f000c41103140c454900344140c07807203510058040742c8000c0410305514141914111041c2500c42c1da02414140681e950781110000d4410802030460985214000700c48040602003803540c0842d007141c40030500080140c0100f6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 466054694 1250 466053444 466053463
    0xd0605090d030b0406060912060b0901080705030106080606010221040f060305040b13080a03020d060803130f080a0c060f1b050334030c05070f06030b09060102190206160212 76
    0x490402c983e55810040c0030944281c0d20030302c000701e0a80281001262007589070015060b2040500050007424100050a0040300380c10401c03455011080600160800748280c1000e4580b24004018a103000e20000b90b039480c81071540240c2400703010305075044c1e4240c5c400340c1e07010300340600c6507085440c0c803901f0040c002c04081300c00759400c0e031300c0c5804035244024119400c20030750341040c0001d240000300c25007a0081d40c4034070304030308030385640d40800260303002c00b480a0b05100f00c0b5480040b101c14a44180c085100f075040d0420156030300070440c0400000c0000c1c0354081106c0a074104000000254541514118410464009800c40c0760800404000c0007100410403040f408583d1103040c0008296040750341c0e0f039242d1003a8048441c94055010034041e508805805215600300c07010151540c880d00c006140550203080882d03115904a40c40703141c103010701f03a48004c082c030050608021001d00c00b141140c2110011b405044001019407030f4000e0b010107180070980150070320041c181e16046090b500e10210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 466055944 1250 466054694 466054697
    0x4020312130b0d05100b0c151f03060504020109060809060115030e2b030902010507020d0807241404030503180f1f060618030b0a0207150e070e090d0c020d0605090d 72
    0x345d4049400300ea000c05450554002100030802030060a0200403114070103401640b00083d11031108000c1d5013550041e00180d0300c03031b00b0080354600f0244000340c82e110b41500b100003840340b61000c102c074121000a041d411604021910650f80b2800581075005000301101090180200e004080302c03c507990804290502e10740381c8048d480700f011001202151b4903070800900203002004a000946060705030220458026001d20b0b03d403040c6952503000c807540b0318540300c81480c1a41d08444d4455050b105e03400c48042c0300520154649407940d002441403100038065032907400d1401507540341c480c082180b2141559140104c2e051080411120074403442d59852406003241004000308201c3d11450320380d940301c0b400c806290802829542e581e002a10300a1920a916070709125200c089031441c081c001d02d107414004006200380310341141c0c13801d100054015608014101052000c031840c000740210311b451951400c82c42100b00c6100144500b10f52100190034182080240b05180d00040f03201040c69a00d07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 466057194 1250 466055944 466055971
    0x15010e0d05160611071e0f0e040b0708040f06051f060504031401060302010c1712250f020d20010212060a1e050906010c051f0e01020304020312130b0d05 67
    0x544508031380d114903042d00320307000e90000082001120003141d443d18001e0100e0b8115070550341c07141040d1072070300700c1070f40a451250055000e0100707102d24200095000102d91500d80628501a22801000e1000c00c4000700015901d00000d0071094000841200e1404050780d459449a80c4a500408a4005000c1500e0700c079004a11201e44143c148501f10849070f0603190b440c1601080e0710390070b12407042034100c0d54100d030041110b411400c002206081c41921080b6000912100320300302c800742c10032065000d400303100f1185100d0140c4c03500084c00f000c4000051401c0340285280021485000f050380c04840d80131360000c56980c03040c50643d201c141c80782c042554a0840d4a45c1d03400d1010720031b030030020b140015200b0400240210b0602124040d0700c4101030408040202160b82c4451030170701840d00c84e20030b560313000c4149100d00031280544520f1244860095085043c0b03900069203c1d01d0804901c0764000340000d05514540c0c001500600400000e410035441309900c110010191100f00d43d607c998a12 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 466058444 1250 466057194 466057199
    0x20307030c1b02210d020106030c06180e150d050d1b1218050310050601020d0e06090f01020114090703170304150902041b021509011415010e0d0516 65
    0x441c0c441103500c0c082490040380c5504154007841007003581c2e980e400e505200c4141c0e91310384203002080000a103807040e0b8000180d1502d9070074011142c29442e00406e0800207541000020104200d00030310075581442010712054440118460203000c1781c081181d001140c0c0000101440008034103002c0e110f180c0d0b125403040b010b680d100c02c41c5403402e00c800100b6a105400360040340600c5407482c850042c20340b83c05a01c80c0f81d2154002440c201d01040e417101d40c03603111400c019076964144030210050000f4242507010b4003410000801034068802a2070040000c0001d0011580c03003500030084041d0f90701c0e902c80341410308141d4141c0700d030210301040da0b14100400c440d0022006540c00c41c0d11654000c00320402820106045c0d002411400318181d90080c0c0301c90044007154011403003180c42204a40042c0b0040491803c0c031118020018061100350345442925040340c022200c000e9030200741c05000c507078246840c4005840050380d1902d059040038944210030100400003038440746800200781411000396 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 466059694 1250 466058444 466058447
    0xc02070f061206090b011b050a080f030709060305060a0b090a031406010303030e120d15080f0304050a05100215100902040e1e160c02030a06020a03050726013501020307030c 76
    0x4145c1d00307900f800502401c000c3e480b420b0720703030b000105081c0c801c03415a0113010154556603031640007203452103071160780002400201a000744007540100040d05080c0041d1400c040061400310b42449410200c00c400170303d07a01c05c0c1e41d51710301d188040c50b4003d480c03240d030071070b90803103103588000c02d0200f200031916115032903000c0840019182100748502e1044e518120502c508200500001d501d0805d00101c40203002c0fa5064090003180390600010300210b8a0303510704420441c09941c1d90748a41c1c0142c1c40c0c0554005401c0d4003113002c190301c1c4900c0ba14401103865000c01c3c078401100320f41c8903908103032000c01c010034a082d001180d140070b0040c0e12441407100221654100c8d0800c13042c0c6012261084040704600118000c50b02e009560b030004044e40e8858506456030020380e400702111a0001c2e50306e03410495050303000340140c0031542c00ca254442c01191118000800710364103020f0320051404031030f0800e010b00018a03403070b05501840c0404031084401c28042a020f50002e039a0381d808241005813105019 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 466060944 1250 466059694 466059701
    0x705011b030603020111060f0a020a120f020d0c1115072303010311190e0a021b0105040b010b0a0504050603060607080d052409190e070e0a0c0f02060a0c02070f06120609 74
    0x3082523106620300e5844010407007000b58051100d000510010300040b02c4080003a200c0d810300405840005651884000081001c0300d900e04c1c030301400d024a582c580d92109800103001100e0f5805884001d4480c0c0341c003c4191000c08983c0b000e0425108a0a007002580b44100c0143d41201d108091040c00c0c180490208400c1c03001c9403100d0a40c8540c100e000f08441c1040c444401c0d0031030300000b0018580240740c480c60707502840c40004618140c6d1100c040c042002001c0c01114010001c0c00c420fa030824082e4080109a8412032242030722980c0003001141859994070104d400c22070780240020380da960350340600e801030201181c3c002400561b2400070300760101190303890a01458028101c080683e0749848611071444002c148054056179a6800c0c901c1d800100200c6003e01030010080d1960b207420300d0b0345401d5524128120080103102c03e41c00190760b400113003254210b840031601290781d000b03401c802c81c9030006640c04481c030160b40300700004215130400c11007101c0039060441405000d48a40144040c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 466062194 1250 466060944 466060951
    0x20706030207030e2b050c09090c06030106030c1e020c040b0307050604030314120112170a090e1f090c02070506030402010f110f030711100e010206010b0705011b03060302011106 78
    0x2c070b040412a00d01030319080c410085e80908211001030080b0b0640c0e44003101d6510340000b203409900043d1081940e28010850a520150344001002e01c11618000b1582034081813040c2420b060302d4803004200b450103403022442070f050b610010a0700c0e8075400070003176030b4511118109001d1460000c1d171a89034103010a80c0c83c103031170340500341501e0a8950703030341240d15103141e001490903164144050800b00084c0c111090013401d00003045541402c080c1001e111403411801c0c5414115410404480050f420010030703c01c0301c2e9140340411080e80ca07035440c088541583c0f46e00a146203480ca1011a079401c4c00d030301803030034140d5690031110302d9034842090001034403090341d002e404510301c0311181004520684400380b407a8030040603030326002c41080c0500d1440e08410340840f08104102d50f035001c80d04220000d01d0070081c280c582200c0f41418800040d4542c034040c00394081c203c01c0041c6842c00c1c01001d420562132068451102046d8000004004004001900049001912696070080400c1e40050302d03900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 466063444 1250 466062194 466062197
    0x40c08060a1802131401090e0f13050f0a05010c020c0402070c09050403050c060103080403031412012c0103080d060b0a051c0b03011a0f24090f0316030302070603020703 74
    0x22054140030000441ca2100218004299000c10030020040e0144d00120001c210082c2d400c0400000400058000b8038170750000400203c08a04000502d00e460408070380181c0c4078185450000e0041c05c00ca0308103202d803081205240704642005041010550000210004540c01d44850741d041c40c0401040c1d2261802c040c150303142c2107809024441c013030341c00a40c00510031309046280c0101c2c1403105081c003101340e00998901c440801c041050580240c8a000000320410030580781c102d030b444e2030341090314060017440220391040301592140b1084400000880b51041d44210a540e0b403443c0c44816540300010b02d410741c81c201075002841a200344142c58205c50551941824260040070000d80e50380da2600c5001c8032030303c81c1c040521a031020b2140036a001c5068046c02e03151303214002406020403603203003014020502090f25901800300315007050894502600d0040e80e60074040009940300350289111356060048142109191100c0c0001d03e044900c06e40a944a06a941c0b406034102d0282290150 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 466064694 1250 466063444 466063459
    0x50c01020c0108061516050c04051e1302040608030c010e12040602070e0702030d06090504020f030d120f060306020a02100513020d14011d0a0510060f0e0901140f0105040c0806 77
    0xa4545c6812000d0400031401c0089a80c100a01e4020fa0710340260030355001d0342c09820000d802c1403a03041034010258071914401c403501c41d407038284410b100b99078801003445001108145180c411541e86400c0b91000f07000d41c3c0c0440c3d48801000072968000d156a00d0402d84600c6a050300b004035402c03c5040e9000c80d0881d4003e0310045152100f5400c400400030b016800b1070204220b245245010340c0700780c3d4090b000ca100300103900e181c01c3c41409418625002d00c01e119600c00c52114980551026006810504034200403544403400e4a402c0c02501054100920300303070000c00c060710382c19030004002c083c0c0e030b522200a00240d110103956031a41c46c00004081c0d0401058507020380030070907040e017483c0c140e0f07030500001460500300e50b560441d0b22012007002c200340c0c00c40c5140505010081000340c401c40c154240410032107103403581620128045200b0a24105511400940c50450a42c007029020500440701c4c050741c6000c4141081041c0e00b4020315100350b14040580c1d46880c401c007401441008003a1054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 466065944 1250 466064694 466064701
    0x6030b150f0f070605181501030b1305070504050c030613060e18030c120d06140d2607030c0b07050a120e0c0d060e060106020a0f03030b0a1d04050c01020c0108 70
    0x210502c1d0701c03080c1046210582000400c000880d90b11a0b94803e91090161100b4010255000e07418000c0060030142c008104900610110b00c0ba1040c070b40d0008503102c00584101170524102d0b04040642d800140d02c1440e00d8208250f01c3c40300d4000b144101d0044540041c1040e8044e56001280c00d0f901a400484030076000044144549104102d4140240402c507400c040c81c3c1c40c190351410110b54015030010780080b0311020b01108030300a09015050428503a80f2481c900780105081070032841001d0905020b0000700d0135854200640b11032504201a040f61f076071400d900b809401c1d188201404ca420307001d988001410f0522031401d46003105540d980d650303200b110510025029007070700508401203003e80302c2541440c3e6242c4242d140c200740708000100f10039030003001080c24014164070003402d540100c0591800907200c6070000e0f90b01c5038182030003d0b084049001160b104c900780e40000f00303a1400030711022070300c3e6201a55140b06510a804540d12030f0b40c80c600490701d41c500030034607502003601c5a021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 466067194 1250 466065944 466065967
    0x9020304060f09030905090c04051c08130e0106021c360602060f16051608120a0209131e050c07060c0f1707050a08280606030b15 57
    0x1950800d00428010408035100c1440754203c980800d0220080b4800303010030021424507610f60703079010702c01c20802e074102440c24000c50b105208024065100c1700711307040a541040000002c1c0c0320042e141030b1500c09000d444007141d80c5103440078000c04026100701012501e5107100d0b1102c1001d00b0a0668841101000ca558407204c1c140300c0c3d002040040c5107a0050301e00c03c450402400c0000d0050394010003850a081c0a6841c510802504c1c0c142c2c035064007868600c90507002380032203500400360182102c245401d818025031a0140c114084007002101c018000c00880315005448502c000320303100d88184011041c1801198104540a01103564088800d43c1040c0542d014a61021100d0710191900d20a603441d20308a03441d14507007901042041220036106503010305906642804a01441c0003401c18540c040c2c40da005000c865410030a130200001c400411402c4259000c00b0b800071603100c50000d820005002d4012401b9076400646270a44007040791804040841c03006104030001c0b460014001c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 466068444 1250 466067194 466067197
    0x5090d061506181a0c010605060c07090605060a0e060307020102071a090f1c03020a0513060908070e09060c091f030c1101020f0a05091c0c180209090612190803180a05070902 76
    0xa05c00240d569811001030307951180c6000301013031180c050203010f55504200c1c1400c04c45400e500643c0c0140003d01004c0e01e41c030b8000c07404200c24902101e01c56141d0740c44e902c049002e4841e0340d000508160f840036030740d10380d0706000071181d00035900385080ea01c280c200c0c5003000d940c0e407481d9100192801e41112110b400240a503004002410b505d1909900d000b40903003488418241544c0120001500c02c0020803034a0814003114015000d0303801d0b600308605041c09843c1e51418040c00100c403100d0001000045a61408a54030305510380500101a8458082029000303120b0400c01d140802d52154914040300810300c2116858110704080c1c0b401d22034000b40443e6241c221220264000c20940c480c480300c240c902403000841c41c41001405c6000c2c0c10b00814950741040f4000b04514240180700d40f40b0079603500c102c8158448026038140301c80c071381c6141c00145050401805070078001c1c80c00c4001010f000c0c508004600c141e06c443c01d00000301c2c2004c0c06d16650360440c820050010b8005417001e0103510050340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 466069694 1250 466068444 466068457
    0x31b080702030d0216020a0512030913020d050a0905010b0a0501050d111c061e18091e03030b04050c09030d0f030902100e0306060108060f0105090d061506181a 70
    0x1044a09083c42c18a401080fa40506031070408415654003100842c030b44002c000c0082c0c1005d8668036440301c0204c41c0c0c0360341c80c061040500d1007816060324038403c000e610b6054a1a040c0110004d11a508041d42c0c124020882c07500151025400d205d188180343c20300741861401c031101a0343d8146442c0c0d0a203a040020a43c0540392100031208200d182c8900013484811100524101e0300094101c0c604841e0540019140c0b2090703201d00007038002001070020200c860560701c10b6803680407440f5101440c21002003038010903514403011001c0005400d1650640c8407000d1940159405c10040d104d450f04080035009106c102c6505600c4040c0301e0580b2403280540740d082d1b034600e09001c600c0442540c000744d0040e034440030f44400a140714200704aa0700d400c110440d009002800d151a8038105000890740a40c0d80303450041c188100000d5407017581d121043c6440196030402e90400043c04a9483e00220210521070003001a44003400c003c0e0141c1c1000c406402c9605500030220800100302444040c2c0d000328 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 466070944 1250 466069694 466069697
    0xf0c130e0a0207170a18050105040312020703151410030f0f3f0f021213230102241303120e0309040608240c0c150a050601031b0807 58
    0x1d00c11075001543e81e5500c039542a1036540b0580d111704240c01c000305110702012031401d45500c40c080411043e43c21104450540e5000111044107820498050385003881d40e5100902501c01c901c0b00b188c01c4103240e0b2095100c1e20614154078a1600ea8114400d90596940000b030080e6032214008000944c1c444041e408180c4500c0c1554804d81c484030b0300071007110b103c004400c0c1120110b49014100881c0c6031b0b1500c040a094180b01660100009000b595102540c0944103c51000920b030a00301402d42d403c100201074945181d0100c801c0c940d00220036521300c0c01c00d01d01600c581d0000b48004030720810004141c0d04c0c0c00704d42482c280d0b90b800504982c030019050941c20f10a5400026980c0c0c0032a01652101b013000600440e582c0d503d2200b80011510590700c480e00c143c01c0114104a01c903480202011130100104a403d01901c91400303100c03491203407400280e414411003045040200c14648100e105410420003006165244001541503903502030300358048440101441c05203900504a554000c4800e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 466072194 1250 466070944 466070947
    0x120901050c12030118140907180f02040b0406030b091b03060d0813050109050f0a0308090307120309150507050307061d0114060f10050f03090c06040902030f0c130e0a02 74
    0x1003584032100c0d43d02c00e0b000042101300403c0c052007034a2140c0100c900e208100001e5407458501000040d0301c41c41d4500403816011000650000601100d80228280100080d02191307160382e0b90f012030545600c688500b402290170039403190000d00d04000440d100702c1c10310f2a5225504024034040e4160791000340305950118140e604180406c0d4480060701941020260000216043c41c0001d0641d441030b85c0405c2c070540842103004a2501d030170a40200303c9601c482040d85501a190000b42008060740000b003401c07031a02004400d05501010b000b045466082a130f5600e038116000c2110180304040d000380941d442002170000050866000605840c0d16048030901e03011403000b400c0c291001b448030b00714a180001c090100c146032212980091100444072200c814909250140090240708900c000a6a000c400240c1d85c000078000700200510003080e0039174070b5442d409844025042500c000414074081c1d0005024080064200c1c1c10200e02c00600003049860101c04c101c40c10001081c809a07140c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 466073444 1250 466072194 466072213
    0x90112051011130b040501052505061e0906012714090d030b031c110c030111030f0603121e190203040501121b0c14060702010608010e120901050c 64
    0x7076032054040d03030080000040c1d40e443c525407605100c6080390300a1a001e100401080216a801004480314841742d1401e107400c80d100002070b8a0100c28001015026000365410085880351f46a03401454241c0000002c1454543c000402c3c1d594030f00340240074801c44001e4401c00c44945014600900311440c000c08944904084000c0f90b1800741941e9480c142d500c00c101c2c0343c8086400d4042d40140c00c00950007000c0c0080280d1144003040500241ca90a000c3c0c84c481d10000c0c42401d105007444560050028403000e20040945141a481210080003038031203a00801d50320b00d8007007001c0c0204446000e1131401d002424039407025240544000100c812420400981200c42d020140701d04121590061a01c540ca000c001605640c10f40c041d5420a81ca001c0c1c01d09070305d03540181800c132480361320300d0500b171542064500980500e01c04400818070340b08000801641796030541060781641c200720f000384600f0341072500699030790300328404401160009000c0c507001548140050708074402c030311017190700005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 466074694 1250 466073444 466073473
    0xa030e031b0106080c030c0d08090a0b03040f030f0809060411061c020405100c0827040203040c060207080706172d100f1206050a06081e070803030609011205 69
    0xc1c40c0604018107a51150410130a8900c240f14601e5652010780151510082800c00200a00145e45004103060000f00300c00750551070310b0380901c1c054456800340564034202410301c00c2502541d500e00b24001001d825400e80c043e88190356003405042c8070b50043c5029180e07503846c0d0100490090107a50498024018141c40011580f003851212400358001030341d4500b040184900103404100f400f050000b210702010000e5083c10440700c5e0300ca00f0040500000040085002411310400a0598403034004010f000510441000400807203a0b56000c0303501581e91000a075464000e18030a2402040d54640948a10310701c0c1c4002c41c0e88451030703c000340d0710f881c9040d0742da107414046001c44e2121460004200000200001d02110142c1790401d4100d641a10780304401c01601e001e10310081400707440c0d80204544207106c7d041030004d48100d002340c7e1104062252a1203c3d40d40324007000b0460322486070009488040481200e0180c18080d010480c079a09000540d41440103c15045a50380300c0c2080305803503207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 466075944 1250 466074694 466074727
    0xb0604030303050a1803050a08090a02300c010c06091109040507060801050a050d0609140f0a0303050f0402010e24040b0301090b03010c120b0a09050a020a020d02010603080a030e03 79
    0x4500c2510000764a060020104003102c901d030044e845e01140111503800402d8120083d06c900a0031850002800d41e5a04146810582850b07002500000300c000281441411500201c0c0c90840d42104142013904800c1441d5036120031602c40b5002c95000221000810526002542014050010070003d00642c1022401e00c2104030350591f0250084002480101e601c4014240141011501c4400090421002503005034030410004c24080e50b901c008400c0045900070f003d68901c05a040e142d1001b881c00c8840d031136240d14041103000910700030018400d41c1c090440c0c80c1c011a010f0f51080510444c02c8140946400d0031072050344d0105000c01c13840d805100c00c9005002801c2c50000160301c03949042c901400365800341c14070324884e905100048442680c042d039890100c002034180403a07412150030110b815038040c1d422040c001d03410f080c2000450486d41e0014940008140d080f548100b014120807800c0306c0c507a0100500040c010403000c17184611a8000345014131221050740e01e081142414903004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 466077194 1250 466075944 466075949
    0xc0506090105160c080a0f0c050706020304050f0409080d0b0111011506120c23130f170304030f110a05041814030c03071b0f090b0f15070f03030b0604 66
    0x941c0e440b50200081c1600318081c950101e9424104080595100da6030020180a04007100c010468890300c00340d0841d100387d540150041e04401910b21705512010300a459074041e000b0305000e04a845405106410a03120342c984543e0890300085c00d103078a0401400191000420b0349040107560702c51050400c00a100d11680040584542c05c40b4514011000e0300c051034102c0304000352450012072041c481d41080a0268402c00d200748503000c03445615800c0e1050040d01c0d80c50454000700c12001c034800034462681c0d41642c6007040722002120501902583d05c0c415400001c14941c007251030f00000802c140d144808024000389a00e218a4955021804032002c0034890b020031006c10546506000901511007400c90894001d1071400c104030243d147d6034030884000501315200740c4441d0402d00704501c91603001d4241d20a00340450356407921103001501c1c072141160320a44032140084418034242404018140d8101a55130070a04281c80d46880100411015000e0540b01c0d051007032140e1360358008201 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 466078444 1250 466077194 466077211
    0x1d0a0609020303040e090c031207080306150d0207050f072103120609020f03160e012312180709060e010308070606050a06020312090a0507030818100f020c010903020616030c0506 78
    0x11f2090242c41014070b40250000c20901c040d10410001001ca075003141140d41c401010345071144c6483c3c24501c010181d109001c00c4203072281c80810100104440400d03400082d070002422240d1503a15044202144444c081c41c801c1d00d442c0c0c0c0c400b043d0001c0d004640794003880030f060500040460f076946031002642c0c849481e017035044000000300b00030075444003413a030141c400515015600c0048040040e0600c188814a00040e0000041801040d29000106c4164041c03a003148029810072810f0382190035808884131015011701c41e000b192211071803103004d0843c2d90701801070300d0316480d58072044056444044152400394036040c02003500c0d281d811649006001d56402103548000e81588160382c07003005404c2c50383e19006021400003081000604030252900000c8141c2d56910000c000e03100718080b11961504203010603006402150411001420110103800b520078102e1075900454140505000c02075000605000ca0b010142e1342c1d080b02d640c03042c401e040c50104811540c031348518251080300c1905 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 466079694 1250 466078444 466078453
    0x18030c0d0e040c0e10030b031c0c02010f030207080412020d0b010e0a0e0303100515190e010305150102120c0a051006030501060f0e070e0109030f0302060a1d0a0609020303040e09 78
    0x805074241841010035880d001d2404440c1c1c00b02c00c4c00003c1c030070100040503504050f01c490f007946a13540d0070300c2038006030401401c2c0c0c40c0c2e100103040005041800b50705801ea002c07030510b01c0c81c260064003c0c000c40ea175199000480d0741c60281810b10900d03c403505401c0680e040662011305600048400d0126400307131034044107a2400d03182c0b18201d40150345081d181800142c10500920140b040f121840f2003d80380101e40c0d5403801d21201c0640180c60281c09185013841c802441c1c1303080e1035a041b040300b1140a00130b80e00be001075916403441e101024154914180140e001c5010202d8003180c05024001108291040d260440855209d00d0300d00600c0702801c0d112183c0d00d550420400400b481210002e2666915404500c1d1078201074030024540285100180120001c032540603030301c01c00040c0080d60380401c4068495815040c020354801080b01c0425400c1c0c5400d080c0b6445400c0808100780b0181140e0003000da0a0440e510540030341084401280c00d03200c2403001241c00d01c80c0c0d421961040800d0710041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 466080944 1250 466079694 466079717
    0x905030d0e0f010c0f020607170f0d1a030d0807120c020f07050d081c060e130c05030712170d0606121103060901030b0403020a0618050f1518030c0d 65
    0x2101d041c08071030340c50500c41c0140d03462001410419541500f243c041707c14944a010604150172034000c03c04a0000c1c115002940a01c21280180a413441e540d2a80c0204a541420b0a02c10145c1a03c5030b100c6906a000d401c207924251f00c41c0c5440343e07100c142483c2c42280440d201131104262040c440c1c4103000f51304070350030440f0300a10400c0184000e1204440038a02d18100f0784039401d031803054800740003481a95000304108a032440d04400c008050b002450603030752030074805200300d49598440446140e20034850000d030320300e000075030300061302c007074030180c4840075a07641d40c0042c2c081060b40029080340c814050513000b5201c0d84504c0000303105e191141c070546908518524100c031010b000b0494034030804d2050124940342c4a4a2905403584640c2214094407123090991414407604002040709080c0105003414403214090000103d101b84112400c412985c00c440741c0b6203043c8040f011441c4900c03400a0b1131424100d2040c042101000d017036901d800d604403152400e0410781d40800d0301241c40c3c078003407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 466082194 1250 466080944 466080949
    0x302040203250f1b0b1b070b1003060506190b070204091a1602030f07120c0c0609171216020d050a03090f05010c0507230a14010311030408030f070905030d0e 69
    0xe281850040900c03001c4c1014241da80c00002013405001224100c80c0040c1c1d040202d140c00085070402504a504c1c204189007590003500d60360b503d804201c80c010305203004103030141064400155450201d031071040300107041c15411102604401c4050340e0058890b101d40d4041012a446071801140b0b10324242c00320b19202d403c04203244100c556000841d8401c1048030010002402680d179079030360200c3c4c038020781d09082d08100d5820382c256601900368843c1400000c0e003290814286822035403480326404802c001400c0a5440c2c417250144047c2c40501009442d0200c0240c1c0c440b82c00d1a44000c2c01440c131344199884892400700340400c02c4000c100300200501c4001d0cc0304039150020311091814000080b00c59498a0320380c40320307228810f84100c0a921030303000641c450038444a0420090b0200681325900c401c0e14800c20740fa0820039020034a050184508148107400b140c2c0300c1c5030050390329440e68980c09940b142d541d41c000d01031380401220000c0130800795000e0002d03003d10403166407034010342c0481c03504 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 466083444 1250 466082194 466082207
    0x20318010b1c0201080403050706020a0e0a050609030312040516030605100e15040c030e16050a1a042c040b070201061707090b040e0a0305030906061503010302040203250f 75
    0x21128420401d21401150340410361400c82c24a81e42131922245a445600d07055560f4041c05800030207250000c91038805d0315501540700301c20444200c030f00102d803030380e1242480a144035486071640c16401c02c1003144121003102035640e4005218800f03e826200014013146d907a400e85410885a03d900c41007409421505201550b0142403402180c4d052820540074140020001190b00c1d03020ba138071641050041e60007544041c1141403e001626010100f0f010b04100c406014011144580000000400e5000500b500f10002c0b54bc100d01140c40c2c0342c28088551a19200b80000034204442d960191055117070300c60000d4007481c4943e540c61243e0405c074102030309460094104070400c80890720302c001020703800668032044801c0b8400c0001c18076800c101080c0070340038800702d48d6810720850318401c040560000c0154070881c0c144003900d0310b64494004000c0014044140c082004000303000510140c6007940c000c41e00090303000d60150f6864040002001200c06803010440481c11850050324110340111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 466084694 1250 466083444 466083461
    0x7051221270105160c03140d120509030921031602100804050c0103150f081509030307020a0b131a0109110c0601030f02010c060608010c120c1d04090602031801 70
    0xa26103041180c000000900f9405692134450014500140c95024030022840781406940c002030980841c40e0300000440c0d9030b106145040c000101d81342121181d034060b41c0f190600881841000e5442c04503a0320811484800740400e2640c0e15442402c034150700f030000c200a0904101c040303008900301c000c500401c05940420b510360011b00c1242000c10000400204250700504c1d024240002e403661700300b044050000c00c540000e444181c800e2000708803604001036070300303240304032000450441e543d60904689a00040c1c0700140540e005540010015a44042e0b81c0d80c00a17000180240591003501c460002882025095040710300301c0b0010302201401e8042c882180c1242400d1a240c202d0400380707d039843d18148000303480f0300d06240005003168401c8400d4000c01e03400600034001035032540c3c1524002c100349400c500c04120854240c030450107083c0103585402c49a900e600c0341081d00d580f21505502502ca03145a070069030381c0003510005800c0d00c0954003d25650b100f0301c020820280900e800c40e2003e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 466085944 1250 466084694 466084747
    0x41727041407030e07050d0f020a06320d0c0309120201111c090b0901021801141801030e120301030209060108010b0a030c0513090504020a0e0907051221 67
    0x84562041c001c800480356030410414500042c50b04014001c0604060300c07900000d50264204900c001440082001d601d6254021240c40c04280d6441c0f5003136a00c100c0036845002041440410000c031081401c6540300c112442c402d60514080c01404960304449100e800c883c00310b0f03500c04580040c002c51f0150030000c1e0078030340020001d02d40c000c24440d40c103000d00c10001480c5240f50101c0c001000554110b1000c1c5a481441901e10382450315206002c4d4002108044079804044d8001150f50f00c94480004020b8695201c10310344003400041400040781c6d56900c5040c552502844a244c0f2030410000e0840c1c05600b900c96103d5040d881000b004c401c0160506041022010062107214911011154034003440d007400208800c00c01c0d000d880c0360090034118400b0694011002034000520741000e8420f42c0300b00c4420a1080d00d0301c20030a290b020a4031031841a52003c2c8091000c0c3c144074540c006503c1c172460444001546101700440a401081124085608049611000d051401c142214500d050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 466087194 1250 466085944 466085951
    0x702060d0e032a1b06070f2409020f0103020307030b1003090c0906080d0807090e010e0405190302061503030d1505090705090d080a030209120102031b040302090c0304172704 76
    0x504100c139600c1403410a10310007100240348000181d6500011140182c1d4019140c169907001402e15056800c00c8091039015251083c464802440d120b01c205041d8a034010b044030350410402d0300440007904000c000c5d05c10f0507030350311244907182e4445200d06040360b1155001314050310645018400d80d40c595000e03110340c81c20004103001d4600003042a642164151414030030965451000300c2751009258041041c12540800125250303051500c032507c1a80a50110b41200e59210011820307820216005401a0010f0001c665003404d000040d40c2d0741c0390000c04a034103000e00c200c400800c884045102c206a001500000c200300d085c814050360703109000307081103810400741c4c1000c0340003658101001071034941d0010344104800e001c0d070305459100502800441404000c100114000d41c8151303022000320b29596660100c11288904170350075a0f034064000303425501ca07100c407100690406042201c03450011409060a0082c00018040303074118500f0070101c0301d04007501c1c2141d2101c03120703030140a40d08 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 466088444 1250 466087194 466087267
    0x6051906080a020108042f0901080318060904062102030c030d050301031101050c010c0306090b0f1305090c030307050d0915170703061d0109050604020313080702060d0e03 75
    0x4011400001c803d03020b0034042c80c03ea84a00e421941d060b004001920340300030009082503007441c4030300450415901600d650503141d88410095039a4090003160710070443c0542a4205039003406c03c0900191100134101044072500c8003280c909103c0008140700760480900c0c071f0385096160400000b011a10140d000d01005030045000030202d2005000c05811a01c044141807920b91203030044480c04040d10000704218100c0250040191119101d06100c05003002c6840c400c81c81d082d2080008e2203001030920504240c000c48240181800500c000414014031101400586050000300440d51042028001442c2e05550140505803150012035080c0c1500403030740302d141d80280500d0398207640041c4003426540e494401b00e0251a00c4c0d0450450300d0400000110011704034074906058031040d0000380034907a42e0310240012400116140c3d14905500d50003100450315510080555a001070500340c0b90241d0407a80c10b058522003016190070f64800140c41c080000d00f4401c2c103045c3c0d007609010950040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 466089694 1250 466088444 466088459
    0xa0309140d050310050604030b04080c0a080c0322061b06062c0f041203092109050f060901051606230601030f06030b0c0c100c05071e0305030a0b0d0c0306051906 71
    0xc0080009096002c000352140310300e50204070301c243782d1340d108075919a03441e010b00c0d1345905c9800c0214501070103d0002009001c4c45019510241038404959030b0641c1c1c446d1045008649490341c48054607081e42c1e585012071030030848002440c0e03202e90070342d021803560345c0000180248680100b810349044070340c1e400d11001070b00e88150043d005d0051b00e80420b204280307040c40b00126942c2410409a11010020a01010f810030046030445a04584190303240418605009035407285194840c00200b08015025254100e00c86107a04507000c0c0b100001c0500c0010321076840c02d05451840c00400800104000140d84d0600401c1540500e064080c84071500e1641d0300c040c000c401030250500908049408404c41c80d041084a0881e20240c0c000d12007050010405801c582c0300303a4064503164140d0b5003103040c5201800d0045241c69065982c0b62440d60343e010844010200702000e41c3d030007919000c4480209030f42c1010140511700031140080c10703040c89041c404240d03c020143e03516440c14402c04101c0386 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 466090944 1250 466089694 466089713
    0x801060e150d020f01030209030d030c0f020f1e070b2b140c0c0102130f1a03100b16020904031812020d02060d14011502210a0309140d05031005060403 66
    0x40f0b5064a0780354801c6500300058003c1d0044100d200d806200f445035100c50380d58075401c038088141142e241c900801c540d0003412600c42d85241da2402c2c040d4040b120724107010040840447c00d101d24a004c0c2d8a000752100840c02d001d0740f100c1c0004040001605000078011071618441c0b0f00554050320800620164401c65000180020301c42d60103404049002c82c4043d83c2901103502d0750b43c0b6040600380d4141c83d4020079045514038010007480600b880e8096000a41000840303000b024240701014050380b4001c01500c1da98849c482c0c1c40c1c60b18004a03011001a100c42a44038040c512944a445007541c08900950341c009072540b08640d2016061305410150321491780003105250140c90140e0345000c5a9400000f034010b1039401c0c00e104210100019500118024500c1c14090310b500b59103030000490211860912160621240700c4010004840814043ea201c030f04450303c03429051039510051012035003021088101040451400010010ac9501020b0288040d060865020f030400d421600c401840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 466092194 1250 466090944 466090969
    0x60305130b070905060403051b040e06040605040c151e09060e2e050c12090a1202040905031603020c120c09091002030103350904021e040801060e15 65
    0x3030079079040402c0c2d01c0d91040d520360010b00809004c060380e4960360324040743d0b1000c0d050400d00c0700c480c0305400c1d030382c0600c2c081c000c811107980204000c2417152103544400e801018040d00c1100e2103020b00c540000d1441c0440464070860720680c4031454012000c14001d000440801d0220701008203108080c0f10312174001d8014900004c050b11628000040181c2032850080d0341c43c00140409003200c92021407681c020020000380c8000c40680740000704000c0d649030b00b40242040694800301c0840c0502029031038082003514207000034030205042d148c07911040d0645e48a04044001100c000304070400341501007006a414000640d000751207107580c5520180c0320580307166400d00ca08081c3c00450f4901204000c010404026900215565607403450202181d00751850342c045408614044100c00703034075141120310403c54590f5990314001003a0100710003513102140d028a801c0da4104480450301c0402d0180c4042c00602000041d00390402c0b0b000d8111540040c4820240d26406a401026445182100b4031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 466093444 1250 466092194 466092203
    0xf071e12020405060c0307030912150c020a020a0f0f0b070c12030207210317040507030602090a0e0f0402010201051006050f07210801030b010b040e220c0603021306030513 75
    0x900200129180e40039201d5a8000d41e80100e004c10900080400480102041c0d032113621800c202039540c0c60040c03403910120b50060008100001c0e52098041341d030300013061082c910704c103031081881036074005840d1090384d070850120701c61094003e00c4031f404807d1410700503146001d91141424400c2e500ca02d5900224040e65401c0046d240070582054001c003ca0006070042c406694a000c00100c004050400c0002c42a4001545543c2e9209400030641d2024051500503018140c0213003140c80380e4019500040400e03820008901d80010300c3d0411114150103044c0f8501c0495650a09000090a41c0c9001d0103100d400c0241c22001c100300f64001084940000c55541843d4407503000d8100045848002d4403559070141d00ba00a1500040d48a01028141e91081c6000a060790302c4000c8240680594000e0b2100202d061002c1864900701c8280500a00d0b03403d1065800202c40b035541600008290b800072020a401080d140503010504d001c02c00509205d01d0100175500d07100c2180b400b111402c2e0000790 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 466094694 1250 466093444 466093457
    0x9060515180a0305070311010311090102030a0c0323040905180706080c0d0216060f06140d02040204050616140c130932010e03210a1806050f071e 64
    0x400a455150b11880116080b1007a1401c4035a02d003001200c0b0002c90301d0250010b40350000c0110910074000940701e80d9601a8003e5040c803844450540d0619060034003036040c03044007080080e0841600c14019540500780c40c4890700c2c1c910348407030344040d20b03009000d01c1700040c04850450301d0b0b0030b03001440394100c803054601140c4c0d98507500f03a03090f018800d0741ca44030082400095045138800e01a200029401e1040c0da0030489481c041c04a442243c90f035018030044030750720b5807100e12580b9000307900d1101580010f1005103400d540d1030014420f40d2041d07107100002d0489032404024481c15100407000c01d0f400c00090003803102c0303120001c2d0350f004e0461204c24a080d90b925100040c440f030a241544d040951103640307aa001203101d040304c0d201185400301c440d40d609112140b4038104012040e20000000c1100c414900449002100c00c0040002d040c003103415500e118401d40036038505034600b603950017003100140c1130900100e600d4940900411090521000103d0101c00000310a8805487d01c1c3d03515028 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 466095944 1250 466094694 466094737
    0x100b18210c1c1a0103050d021b13061706011a0406051209100504030206100b130303110a05060c09090c0909040204020306010311040306271e03050d02031009060515 72
    0x4211102e140030b0060300e011004111515989401480e040c145c80c041d80480c1d400c00e015840072030740c41c00c0c42190301c14142d0300280301145070708244429645243c10300c0404a20f840d00c0f80c01d40403108089140080c51039204400400c820400c0c99401c03040d024070310109074502400e01c01c01601c50f01c01c690300210030000c03010028016030024040e0141c85102c444040c0300300d0806040007980e9407400c0c3d4900e0745c0345142c074000007140403100003119a519040c10f1040b00c2c07603103180c4040c1e03400e101000c80381031a0701400d4043c200103001408880c0c45170707a10b00e02080e11900180240100000c000b001c0c16401081046400070650384d05003140d80c0036030304070350142c0d5035a02c2c040100c1c060017154891040c10030b030100c1c0c04001c00000f60460740340034081800c0710f40d003c0840c01c0101d42ca502c6144000d00b402c5040c030100400d500003c0380120000b4043e040c52071a01514905030307000c90b0700c11284000d034001d485105103c0d010250190380000e00045409041a04c204081d0b208240700302541c0d00184185403c6a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 466097194 1250 466095944 466095979
    0x1e0a030504060c0212011506180305150c0c0f160605090f0904020402090a08010902030f010b06030c030a02090a03050a060e03131412150f06010203030709030308100b18210c 76
    0x40703000034582807000f40321154001c07070805041c11860007110007064100090001d106c0039420008210be070402d0042500c400e0a401103c1030038800b42c880280301c2d40402200034200810454482e202020700000c144251041b84405450080354008800b0407604103c004041d0382c8244a40310941021110b00e21280c030f40b0320028009114907001070790844402d0340002404901940203038034090003541070b5400039031030312500e034222481c40a866500c00d07400e00100344c2032916000695441203050000514103000000000c14a107030343d9200302c0b4a544040301550400c0102c1c02a0489030b4183c1c001103003040719290300d1144815150050640d400700810403040103a5903145c0e003004415008096038071142580c85425240c0c401114940c0241c100c2d003002c10312552000040383c1c400c030780760342d502038540b4110f650444500101804081d1241c03221140401c24107a1200203101048102010101d81204c25051101e144d00310170703034170142100d40e0907000e901e4400820f010107000d0048a0303c03c18000400c45 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 466098444 1250 466097194 466097209
    0xe040f060509160f1a0a030b030f0c120c0105030c070c0317030a1a0a09020a0221032205100506030a022119020f06090a030c0f0e0c270319051e0a030504060c02 70
    0xc0f2740c5480341c1c04905903c0303072007c035450000f41002d80e42c0c1049440b400080c55a0f800c1d14502c0c05000540400000e54003207442e00c00b82940e10701c6408480c2c507559072074441c0d010100f80305081c0c9070150400410b010940e02984100b500481c0c5451110b125440e50b440000c54451980c450f01402680000d94200440e1091103403180054840c00300c100542540c0da280320b400d0f00704591041c8400c002c0004282403580500a048000e030b40701d0700800314412421121009094068181a003500c110416200141e44a410540c5808181c90348a0303080c1003950382d070b14035056000c2c402c61100002d22824002580f03070201d80031030b06e000954a055a602c4050041a1021425403001d0056541401d0100c0d45c101030074041d604440301c4d8030070b98403103445044480c076083c03260407110001c9c4040b03001d10a102104107150300f210703064000d0544160200740707010701891240a420481c0d25030418030190022000000c84121012540001400044144d940141c003034403070341c01540d0038011161100b40171940c4101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 466099694 1250 466098444 466098461
    0xe030709060b0304020423040206160609120905040c020a0b090f06091506040218190503030a0806040c081e131509061103100e040f060509160f1a0a03 66
    0x19400c0040325a20b4505040b07a410940e0103d22842c00d1800054403c0d0341d40d410a41a80c035080c2d10001141c840c0e03401c02c02c00e68800f07551419440e40c00094803011401d94071030000500c1c000d0131900c0d000d4082500c0104204540d8000c1071146180250b0704c5026540000d0502169070310903500c510310b031200c03054245031545c070402d00e10352441a401042120100401e4400041c2c100b101c4006094645c282084260b0282c0c130907078002078000140c0040d00786440c0c00100554544002ca40b1003654540e00800d085034044100000858441424800981080c0c49404204119460450f00f24140700d131000d011104041039024507c5c3c1200d010480310f000f400280a02c90340d00c0701d0880c1804040d00500030241c144d450040c0c6840d4540102880c407070140100700d900c564041029280b49604100d05042005809030003034418802d51401c4078002111480f840e806041d1000080251041c42c103503198060304250030200303103050080310410000c071442045c0c0000c3c4031740311586030311042d000f10304400038007210 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 466100944 1250 466099694 466099709
    0x7030602030a0605030619060603050f040201030f0917040806090706020c100201060f03140606011818020f030f010e0a181416060f120608071401050d050a1d0a11010e0307 75
    0x41090255804c1100c8400ba081100307087c085c4030013030fa180d0003039084500c12200e00b890018403100182c01503100742d000c991401205040040c40144a440b21844094031402140c3c0c0508002418049840c041051503030090010000780102c904201000703458500701c1c6103a9010f1050211082c011034000e411003005049400d2013000c20682e40e0030254001940303803003c035141707000c0c0c039001c648694402c00c0703414204032500f040c07040860b240480d40d0190b04816100d007820507901340a0340c0e031009060001940240d0000224899950401030108001900500508080c2c0d19140c0260014148881d25261554029035191101d0b00790035480b43c240100c0001803c0f2101c00c0200c013107070598110203004810b400e00d40d41c0406402201503104100d42490140e0500e41d80011000c0102e050b10126403420301e10185402410001b2802c0c0c814255803054038400b42e4261548001c4c03040c008a8418071102500003c024920110507031919000d001c1151401d0341004002c5110148a403410801e40c0000d0809 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 466102194 1250 466100944 466100953
    0x110d0f05061612090302120c01020f1b010501120b0c3a06120b15030c030312040b0708041505042d0203070501090e0f042f09090f07030602030a060503 66
    0x1400104540c07680040e140b008078142090301100e200a0748921240180d05800070008920f242d0348151803a0002c0c0040d0b101036400704000ac0310200c02d04003400e004d4400e00c405801c204843c0600500b5a0416088201d541031b0b007007446c50100c0c0c0c1f203003112500304c6e0801640b160b41d00104603d12140c0080404003424503005d002c040701e0124020488180c80c0340310450708006150b100c0c000783c410441c000c0405400001944082550b8100180620011881c001c04541400c8405e5010a081d500410810180084850104401e1024450805911014618001c0240d25003a80e80981d46000c13000d400f1070481c0e4400018003048180f541c1e036004030702554092004003602007070881641c1c4042000700e00078001c1c02d40c0041d441d402860041c00f1b840f5030791081e0541d84e42c0d0380712043c188400103100381c50003c09125040079050000c2c043c640c8400719901150076003144201480200305025101e0003160740310000700580803002090560640c1d40c040c0015a49440303050728000502140c1e00215814041d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 466103444 1250 466102194 466102201
    0xd0204050c0712030606171f060c06061202060f0a0c20010905030a020109051215100503060618010605130306020309150a0c0e21060702060601031404110d0f0506 71
    0x7002814541e4032034640c011540c40d22110840035100701e44100c501003440b050412081c07000c00000c1691100d4140c1403500d240300504901300c0140c0c44c40c1e00080106420383e1511082c080780e8003030f050107040c4030b12035000c000d8038660104210344903503549811030038408201140900c2c41002c15408250b000540c04015402c041d904941107040e10039520301140b01c2844c0001c050501141e04000c564058581844883c80c00341444100c1c1d1a190a0f401c0398006c807034601504001e0700c590030307004807000c1030034064a5007441c080c1803030b180b030103083e240c030038032114505104902e001415541035600c0b40c500107480b200600e0145d100c1c0041500010704090010040260240d00012080842000c0000d03a854076103860400784110b64128040742d0001d0711000300c8020b5814070314040001541071813800d0300c001d4a118005420a00255210f00050b0042000d1016541c0d040c02421005105c0361912100d40c20070b40d945c0514884148010b501030001042c0c00001c3c00454011074140e00d8000e4107854440c074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 466104694 1250 466103444 466103461
    0x30a031d10030f1a060d20180109050d051b0604030f1a070912062703020606030c100806040e0a0203030d050a060b0a080411060408160f21110d020405 66
    0x421008000f284500e800340860814003d100c9480c1c9040c0003401c840d1502d4882c080c90320180904c4040d040c52800c03082c4682c0900c411010080c504020421001c2c65007443c00b03000100a407887d640068441c1c018000e1500111703d010803140803004400300c44a2062500b02c3c0421100e00031a40041d109240d007004820a029070728084d1181c402e12001e4542603a0f4070b24400f0b8485c11400c0c050710050100e58190000001c40d40c1e800141039020030000c8415904d40c842c00b61841b441c038014210016008035060000ca8201040301c00c2142c10210b55002c1e0900000100a0000c000180082d101d9612a4006084a4418000a00d91a8000c1d00762707560380d00d03641000c0c800340405944070409039141100c0015820039030010344040300000c0e130f5500b031192555210141d90740480c10107694008805c2200141025003004040c55409075102c03010602807034480c02c60303041200c80d4040c40920300da0310021019200341d030810652055114000074403246000f000f0402d00010014000d40103840c02050001c0348 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 466105944 1250 466104694 466104701
    0x70b070501060906030503121e04060207141f1a030106060215010503010204030f1b0806090705010315031220030307030603060b040605030d0c08070b0406050403021605030a031d1003 80
    0x5600a4000b404126940c0503100116041c41c03001904030381090142ca03c1d203882075584aa000440390705000264a9065010080c1c044103407011281d8540c000b60040c01c00c00b52290b000345001103d000b6142284806514000700d030a44440f1051079980e50740601c00c3c01611a48400f8a590090004c0244076200e43c0065a2001024010246003001c0000090b4601e41402154181d0f641324103e1060025540e40d9a80e1400043c00d00e102c270650242c0e00450749103400c00050f880b0b47c03134590003820204c0c5000c0000d022520040f4200c95905407074a070500200310340c0720761107081d1038852400c0315000300c4207600000c048910b5026440c644c0000814002490740c0343c1c000b0b1040c0c90281d40d042080074001d100b048102c5503d84129909038101d0010500300c580582c02050740f80b402151403620b0100c1903501c43c100c0d05800c95084550503603a0701484245a41080710318400765658000c07110403400c0900181d17031400d45000c000e040000d040c1404c00701444003040042c8094010f440b4a007428070008010340030f03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 466107194 1250 466105944 466105957
    0xf070c050108010b040b0d05070516061a010e0907050309100f06050a1e0b0307020a0b0907241e030f0513260702060a0513060e030d080103021c0212070b 67
    0x640b10000866191044030481e070450f0545a900b5241001e10214180507050041410302031003402d0100100c40428000340f414134521521000410003070f05001c1e15495887c05d00110b04004000d140ca02903620307100c804640007007440c20515201e035504402549030600c0070b860210520b0074048100d60143d684e1300110240ca60866050382610745803c00c1e41000242c0c0300f0b000015000c1082c0800c000c0ea070b41d60003180c0214840c41540c007140c0745610745050106003924007108a034451b20007080a1001000c594002c00c030000385401d40594004030040c01c4100c10306e240c501c0fa840703841c983c40946010794401c500c074100d0b0320401e0005203010007200100040c641d00036141c14440e4840b000c009008500c45030110000c21042c00c2c10000540c0900900d90410f07210b45003800010005403203220b1044030500000c0c0716540c1c4c1c9002c3c000d9050181810300700e80e032802c030040c4400c50380144011f07640c801d1b07500001d00c00c051001e403550314a4000612924070754007554880b400b4400b8040b400c9541c2e100200314 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 466108444 1250 466107194 466107197
    0x100b06181519080106030203040f020f030c0a080c090106031e050a0618050f0a05090d18090204150f0503010501050702120c04020a020d0e090609060907030b10030212060a0b030c07080f070c0501 85
    0x90b660b917520015800c0e4070084800600c2450000d101d08010300e007072541d101d000d10010301107035011021a80402c242340b0342c136044840d40c6c0d44186e101c1d01251920b2103280e400b410f01498180104062505142103094a1243d020115a201d8002038407060140d0b000d80f005126004603c03c4c00360840320810f00820060350881d1071a1600400170b02d40d50b03603c0c00350901403145030000b000002c1c0e00b8103080381c4181c480486899074442040d80022542500d0010b000a003d208064014551703820b00040d2401841c132001106102041c001005540c2e0050142c410341501540c140c8030171592a40c1807400e020001d05046d60040c0b01007414482035a001805200c842d80036110803e460103001d0820224010846500380d100c1c20030070004581d410403107481d5400110381e040100b40350b02020000b4112003915221712000a601107910050942081203080c0c110000340d41011030703981882001d60240c40010000d4800d2000000d501c01000154003c40364211a803190660b00c5200600c0c02d81c8804c0030301d11a513070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 466109694 1250 466108444 466108457
    0xc1e031606050f0a140115030905010603060e0f0d2c0301050703020414040e060a271a150f01050f09090408090f18060f1f0f02100b06181519 62
    0x3c0100e509071203049000382d8184600074541e0311f00500000518003241b4070408164850300b42c0d6000a07000d002d070f44055403080e0341c003007005045001000d00d081c486d440100c5007030b4410001c1c1100d4907044080b29400c4010303102020768006070758441400402c0d003803400542640c0390a00700659154035902402c181c400480b8000e100e01800001c200581b0110064401c07550044d501040621405500c00c2c0c6e000045020720585880c60b044c0b0620302800c5403801039035040018141b44402d80301c0c0004c540c0d400f02c065801f9056001c800d10104162541c0d80c003205040c85030000d00003510f902d510341070b51500c00300104208124030b468a400794542c1c004107200d07801044e2280030800341c0c1c03a06006848481c100000704001aa079001c040000e0842d00204103500100304800024440e040103440c03000c518003d8a03065000741c0902c20003407800303103c80c924140030b03441e10b910310140303648207401c450894440324001c1251503204000181040010904400030b100002600304103001030903804103041e6025203076070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 466110944 1250 466109694 466109701
    0x181209090b06040627030206070602030402030c09040f1202100f06090f090b041518060509060603010c02030a03050a1b090f06021501051c080f0c070b0c1e031606050f 73
    0x82038080d0303004940108a030504600443d207204d503482d04041105d010010172490b541d070007017a51507001c2101924500c0c1c0000c2008290700b8200400c1410074820b031001d81c01031900380c50b41620404081390007000701040f0303090900c3c1c1c58170170005c0a803080c1100c50304015003003441003064024100e41c403860803a5402c100303141100050a100b941c0010341c10284401c030555456884003401e05120800c051025a65201c0310b03031669451031610702482c8106000106420a07103201d0b4640480241188d201ea030400514102c3c6075404400d0343e408040d182400b081035111614045c0190651035031403210380e480c10343d01102440e4050315880032240980c080b411000e890700b100320380340c00d1001003001c0155030103001000310b0305000d4081340c4204200d00480001c0c11171a903450780e003507015525030010320802282c1120003510178000b03040101140b90086190040c20748545444441500c0c030000d62070344024201c075296409200304c0740e104c5c41c0790814048100350783c80c20100a00e416141c2c0d044031140359000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 466112194 1250 466110944 466110949
    0xb09130b060306010821190f030e0109050d0309020109051002030a0816050a0e0f100305190e0a03031d03030c18100c0b1909080304060c21181209090b 66
    0x946050310780c41d6002e801a899058041808200d5141b80e01c1c065081c02c10003074071b165890508541201e1100c0e6281981d0b9090040d006042c2c407005902d0f8920703130345424900800140d0002d411a0b003940641808104a4070714001030764600702c10b61015801c204c07161004000e059010006100c500d1460f241c09540e500c641c2c2500d020a940d01d518500480c0b070402444c02c0c528019520101441d00c0107008011080d4034138040350f1000502c031114000f103a120018001111018103a00052002c902c10810019a400102030307034403074006802600f41961401d003514074810000b0103982c040d80c1b00f411240e0301e040400104600e98440300f52201d40c0c05003004070b5041c500d0f2481a503246602c1c103680703070015480c0300e131225138412402418003090404074242951040c2d102e80900354845000c0e440e035079102d28040c1020f100383c0e00440e01741420400e451940143c081191030700d9004503649a00e00241c070308280301e522038416200b00c1024101d80c01d5200300300d00c940d50043d018003d4860302201440b101e01e0340400d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 466113444 1250 466112194 466112203
    0xf090306070f0c0206030a0f020d0b040f0905062e030b15010306030b06041d101d06101206061d090f0d2c0d0b010f0f0311010c060b09130b0603 63
    0x2d80c0b10005002e00300036005460650003035070b04241e1b41a0009004a821080c100c00ca0f80700012003086152035224503030062030240308540403044080402c1c008545107a0340d0640390040200b940c6400e840707461100810303161119519110002d421541d43c1480c1c1c40342005800300070111400c1c8200d43c0f04e07184200e5107520900a00040b65407081c0d44c0c04094903200e0800000c0c25000c0c11815204d40108180440c816040152440001500303c0008046c0c4600901385e1880300320b0864060158001000e0020700f000a0380b01d44221234802401c500c2c003e0f654581000648815480200380c1104000042400140710850390300400d02d2004484c0e600042081440d03c6000301143c060215a900d00c10808020b00c0030304d840d1100303018940c1c20988500b03c40024013401e020703c0040e244815910300500683d03500c0c00102d005400c0c82400103064a28560b0340b5030742c40081d410b02c103041142c074208140c00c01400c0d40140366000f4009140d50b21514040d00120710b0b50b10521016551b240209001c07840f181004907 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 466114694 1250 466113444 466113467
    0xb09010b030a180c0308211501090f061e090803040e0603010525030c0e030a29010b0f09060d0e010e01200d050c0705060a1b03140609100b0f09030607 66
    0x8005013140340786480380400c50b00030034031000008411980940d191909801514484c00201c480503100220300f80004208020a4108082c940682d90007072000c1500f021022200e0650700309a80c142d05074813202101c04e220070b60320414007440080b6022851030103084076244240c2d41a00204a60f50314001d08601c50140c07018003020303000100a42c150850711940000004a000b8207010314a926003502107450b04a280328241d039200d4025040038842039506038040c58420700320507020f0841d410503118180d5481032890700c0340c0101d0001043d041903100d41d02950841e03079010784200404403e000a8501800d54804081019480d000300c2201c00c580c510001c00500d01f407100c600742001c002164070001404050001c648415040c020000000d0042182e84d00c80d1040d90000f0a0720750040184400500c043e011400504d42003a403e070f0300072118480401ea0190045425003041d86a1070a03404140460303030811803580c0400034145400ea8000c1d001851003c2d025030869041c1c0d6105001280c2d03d00450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 466115944 1250 466114694 466114703
    0x2c030702010926030d09120207060504090f140709050f04021305090406090818090f0705030a0c0504320904080403060b030c06070615050a08070611010b09010b030a18 73
    0x2c050600c8960740145540e00d201d8a03044482c408079900105070740c43c542140c1d6200102a1721941007208000c80804602c0013482c940c00102002d5007468005031041c021809844044c0d82d4441d41d1504114503034001c2d10360036408450f8107103a41080100246054440c9c0100c60040404681c1040241018403c892060000c0620340c01c03903d04200804c80802d03400340043c0c6d0805d458241c16408070707040c0c0009003100305920100d030300c00341c80c602f0034803d900400130103078441500d40600f04142c158001c0b0403a03030700c022001070019400c401904141c40764001c94208103d031b61b0314411524100e5601d0030420144003001404010300749000001c110703520104850041030140306000410010f902608124100b0b1030040c180c81c2200303052404200303207801200c0203031340050319010408105e044543c1010701901c0c050300e085140a092200d07295982145108a1082100700c0003001d20340a429440074940d280020400d15040d6541c0c3c442c80c040750810384090001620f070020018403945000d02059901d50710 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 466117194 1250 466115944 466115957
    0x4210906020a060e0a020306010e01030c09050c070828020708011d07030210030f050a0209011106150f0f0a030308061306060801060f0c0b070504180e0a021207092c03070201 76
    0x15965003c0900707030301520115a80b290500c03810040c1d0b8244603140c0604000384a1b44210341c99800d20705044004e40d80074240b058500b40500000090404c01c541c3c22540000340d6550703a40301c3c140840340d89820a4030300d2500e0380d44a01c1940e10707941d010a000d42241c200174021b10051940044029119021484120302548111070400050a00880b520344002e501c0c00c0000b41c0c0da03884442601030305c000f15241da01c4140d0008850400b0360f0400f03050400383d6500001070286250108900e0000404c0602c410f00c00c12114440820999595524005203600507068000d15a42c85c9005009280c069034542c3c814011006030250301c090354810401120103540c2ca80c0d00c06d03440c002055410501000c98030003004108110540403900e1030741c00340d0041c0d00765078076190b40700d242c007030b12000fa0042082d000c0f900034240f07a4000c600c944005030300000f140d011144407482c448052815480c011003076018007485400d002e21001000d50346080f0000859040c40c1c1c912064001a448075141c1c82072580081c042481e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 466118444 1250 466117194 466117213
    0x1703060a0512100903110601060e1507111509030307080d060e04080a0503060d06090c0503010f0218090c120405061e010e0f0402060f040b091c030203030a020913050421090602 77
    0x40c035402a800c805e0113400c080c1e0001d55240b030018117184c1c1c26081000400d0310303080c000d182070405044660314801c242002d075050640d175036603100c010389100c802139109000d41b00308541030402c0e03401150720207200281166601c190a06c3d020020340c11039100500018580a0001500c070f0781040b500784210341c0824214a4506c881509407250341014007596084031641e411800020860b10814801a010b42440c05082d403a00080500b510501140886402c1c01800b034008100c0c000c1e03400c0d4000d6a0211100c200f183d0f0313003038909807250141d640b42184580007001031005212000c200c5034090000140214641d104164100426040038841c0d810981c0904000549041c00107070046e400074401041075290007079000758007403540c01640003030002d204000b0b50211289024600c1c000070b8507152810f556600500e44002c1c1d12030200820b10400140c001aa000c255555200300800303107040f0321020011400d080c1070034101000f400080000e030100d03500b00304184074044e0040a080300d10750341c010401d020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 466119694 1250 466118444 466118473
    0xf03061f12081308030f040b160204050c040f1a030f090f031306030e0a1a040c08070605090f040509070611070f060e03120307020304030305030c071703060a0512 71
    0x1240004840c8102912080030504000411405a01c01d006065142e19071602c0321503d840c0384926030044a41d9401006800d1260303a242055500302d50141c610180c503041154a001889000d46500035130042c548010000700d0071303009020300b00ba40c50459290002c1525a40300d5021402e42802c00b02d60040c0500000301514118005507038404108800d84803a0b040c4240c080d0301d903400a9031004d1501d6068042400b2042c3d05104021400c2100350007064490741c80e403a8819102118100100c480b948080040c1c04e0140454042c80240700f59012940c45541d03d2400604070380142d4035040c03194800d4401d412807071902e8001d0500404588014040392482c01b441640c2d000e00c1c40702c04424900806038005039094020840b900206444d89030000c420040e001010f040c102e00d07855071881d04d0001d2051000640e40002a18152035140c240195a034980340364500c15406002e000a00800c0d80c0006052140ca05902641c041d10054800c65050754448041020380400030381d080704940d014180801644 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 466120944 1250 466119694 466119721
    0x807030213180f0524100b0901140d050a0f0902150d09060203010806060117010305032205120a0b0604020702031c051201060903030f0f0e040c0306050604120b060f0306 74
    0x880c080010001078419aa407200d488504811055078030f070b002181c4100220180c0f8543c0240c0c50f111414584072840c00000c0c194406c0020b010f000c030a450b0208181c641640603050765413040d503080c008140c90350700300c034600c0e0064003040750a000da481c20044010440207240c0030740c1c0d07405a8018a05020152002254025a0004104071004640310850780010542610085001e4542e000c060032071807074806c00140030544824100203400b442d200040000c40e4000c010345841011100800050009a1121031207010031030704615400480b5102c034409600c000603681c4210342c807414848140d50b8503442000100e018200d0003a416800941a0700c4810f50740700410030f1005d02509020f814000c4408186440358000d801000106c2d05004051003410b0b0804102d4081c0d103042c3c82c20740740b00311509100900038413070b181c002801079440315590511140a03401c41006460090700c0f842c1c9541d51075940d032000042d11802035031500100c50100384181800e00404103c64009801403809480396910700b42d01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 466122194 1250 466120944 466120961
    0x121412041e0827010507122c0f060c0d0c0218090307061109150c010e10060f0e01030b010b0309031303060209011701050f040f15090c090807030213 65
    0x203000e0020340744500e0800500400030810701408a954454055040f94107040845500b0300d480004030003060062680d00030115541558440721410050000600903944142c81e01e2040d042c0080401038048588003092019070030180454039004010745640500c2103512803000303140141d4020100c0c0c481224007410010074014400390800039403c81540c90b40031210810b035001d141540000030158113014507805100c1888034000d862500d410110000540c070070300e03110111011002d010600240019080d8426200314080d0000c0e17410101c80540c1102c02000207000e162407034a4100408541c0b4814180d03100d0690781c2c0804c82e034503180d082c02e000094a800040c10b9410901c0208025003440c100102d041009622845002d43c40d04180400904502821000c6c0b800e0451365000421040e504c044c004080e001082d41c0015100d008140030708040c2c1025102d240c0d120103201030001d1546e81c80d9002002180c0f5503a1070400355034458100e0b035110780d103a105c0658008004038401440d0820383d80301140c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 466123444 1250 466122194 466122203
    0xb0430030527090a021602060711030d03050618040201050d090c0512031e0f040b0a03050106140c0d08070c0203160306050f0f04030e180711010608010b03030d02070203070b0c01060312141204 84
    0x51201b4190b000416030750011000b1103481001c50074040350390608128440640350305d0306080c0214605070f03001c60801c0030400c600d0403406840001013425640588101d445140d243c2031f091100000c1420100760034401441000e016107607181d41d00c0310b41c03940401911800650038500b40c800b90882c02d40c0c0042600103e94440000c8010400041c06620802c006c0c50a0304c007648000c90a0740c94001e020380303140b03149076141807040380c204803c0117455804510400d200c1081d0a1880498039043c50840c1d0880c2c010740002d42503c02c54101140220089026204481c8109400d000e582d0703410038142555072040c0c4003200c1d840c0815003c100060700411140205100180c40d100284040031320850324400140c0d550740c0030a040c40000c1c1d058a00070f01940d000b42c07801c5c0c030082c0202a46203011036075a100c0d83c00600380382a03010810804560b030a100c00001481ca000340d65448070b803000400750080a02d403004540c40d0840568410032140a00d521400e0001c03582ea1803410950030415a180d500e6002b0811103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 466124694 1250 466123444 466123477
    0x180109050402060f040f180603050d1413092c0d2d0c060b01050f07110303070b09060a050906040c2702030108010e0c0a0b0430030527090a02 62
    0x707030714200d07000c061710040034601c030f003040c00d43d280c0300a0010601041403550082e6007024001d101003403000816208404281c600403134040e522800307005040c000c1048000c040d030725152000403100811703040030341017130180040700d207603a060103040c00c8a0b003050b2180500b00b500609200011580a482a041c62110984003201500f440d509001c0b02030803045c4004012412042840c824005544a8828015030078200395241c26654109080c0d00d00905100500300d0320040d031000c0c040e84082c403d83d0340300359000191440c0d03801c10a54858658501300c812101c3c49207060002642d4450000d0243e0086070008440c100c49820f0204000311120442402d00c515041100e83c441070703408620045001385000400003400c580c40c03244603410304140c84901403054202c0d280a00c51398151108460403510348420b5440d042006000e564501e911400913105440406110a000e040c0c01400070484595400455103060645840100300580034504a941023420240018204042070340100b60724070f00e000c00d0b003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 466125944 1250 466124694 466124707
    0x503120d02071b0305100e03030112080408010c0f080f01060e0f180114010215010e13140703030c0204140f060f030c121e030a050f13030b0901091118010905040206 72
    0x809080d80f10203800c591103981003007070040c140441c80c100c82d0302c00d4051101281c12401c1555a000600400b4030101520a00d0710403c0303580c03c1114014090b41000384041c0003808000703003c0d03c100248000200d0042c90016a11426a5581c6410f84655840328070013800050207006540d20328a1031030741c002018410b162924071040403514003d00b0790354031490418015400080c04c10f00c0e4440b40410098240005105255040101e6a406940300d12440300800f12810046814020340a10042d140100407001c814076501801c5180fa0500039102405206000707124000105011614015030b0743c40ea201040c100d240040380c2e0309400e0402000c03103070f400349080001200002003001902c4240d0004900c18006130840d00d209824000f9071000d14181140908058442d11032074111a55207400010405c00945007080a80040c68000c00100c10300d18010003039034002c1c01d008501303072583d6031800c5079021940b81010301120390b0440b003aa4032403240d10f07000712600900340150040380c0c811428004da = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 466127194 1250 466125944 466125953
    0xb0c03040c09090c1707030506010e0405120a0915110a02010c050f15040b0a0b0108070f1e020f01051f0302130b030303040f0605090313210507090e06010b03010503120d0207 76
    0x11450f4450013551118070440c54110400c218510f0031081c1d107015041b00742e003000800c0c0c5c0411005d044030718404241c0c0d6250b82d940782140c203110366510344225071140480c071b007185940e0141c201810703149803042c240451091a1810f4400c80b07030030100c20249070f02c0b0000040040d407203119000d04042c0f19104642207200c00c941c40c1400d0150071061030b80d4a400040400052000032100c65412007021001045644140000203108a0004020703205002c134440700d0314140d910613003104950b04083d281c1c0ca001c40c00c030540025180c5040b05002c8085608003804207001c58802c0740c1101070070020140c0d07610654611b5082c0700d030000b85854004151680e030303010a45613450a00055101e680b1a404514503040c0c00d217448000c0790800f400b0705a06501c00d11030354005108125000b0169071064841d001401d20318001e2000040b111b1100038000e0080240009104047d0341140240540c8001603071016038035402d0142240c0000d00c03610390305600201c2d01c3e0205401010041900540469001d450074640d80c07074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 466128444 1250 466127194 466127201
    0xb0d0606120b0a020a0c020904050a0b040b0105040516091403030705060a0b1008091f1d030316080c0904091e0b2509051009180b0109050d0b0c03040c09 67
    0x40911000400440701081151078000e0641c8440b2040d001c6040800340704004020b5612410024050213000000c00e007032010410902c03151a40c0102c0c444114a400c0c548680e03008800c3c0b080d40c0c000ca0820001c1b0310040e480000301c02c444030003651810b030302515109400e0042940b1403c4c094041c00104045000300c1c40a108140c4118000200411805200320a1120100c0d980d5076a10400a40300c00707106034041c020420401c01080401105040642011440000c0002c0009141c2c0d0001881100d40a500003101652040c58107860a2a000054003029203814804881c42007580004100c40c0c5120700e841c1e807000d00701310300905204008190011440c46c503221481c0303055031214510003c1051442d0441c14401c09405e00a80c084900e0b1074103d0301500c40400c42c011244280c10003070000080b41d100307980510040c820b098283c41a462000810790060000b10401c42c000f520b02c01022525051248030485080d0f03000040c801b590740c0c0c00701c0101650304050021110a4010701e000a0012143d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 466129694 1250 466128444 466128449
    0xd0203061f0905012405030f0c07080c0307050d091403070e0c041e03170406052b0f02120106080906040314160503030603070e010f030602031306020a0c0b01050307180b0d0606 77
    0x5c6048401d2000f40300000803051a000354a42000410410041340d11315841d8542d40000110f4040e54403003165141802e5940aa13802c1c3c00c01d03d10020611388248400010000c3d40c0e80150b4070f400241c40e0319019410901c8040702e0b03441d501a8070121080024125600382c0c0d980c8a0450100241416100e217004d07170700910700c1e41ca411800c0108502c103000344038500700700c895001800080036140600c0c0080292503402418403c0c251180c8600403907040514a100408080c586d20804004080040380103500a421800c2c8000c0b800600100100300940a510428082c0184100803c030700c1d611944d08442c142d0b00305100020b10344051021001882c40010102d04251146028549901c1c0c00428180f41200c0c51784881c840403100300040004003550708501013038903084400960340359034200c0c1c00f8804210011004001a20000d004560158086c1007142803130301c194502c1d80c01e640e80728201a40c82d0020301852040300c1098100050210345540003440c070010140030421b421946485910494400d44d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 466130944 1250 466129694 466129709
    0x12020f12010c1e050a080c0a1806091403060708180f16090e010507050d090501150f0608011a160212100f060602030c06010501030b060f1c0b0d0203061f090501 70
    0x110045100c40450052550300d14030f10301c0c102d400d049042d500104504c60190080303417800e200080e0304441500c100141907400310b00e2660040400e40e121700003080c8042501c184014000c080e40c0b003190500d07003c60740c0c9000c4c00f8903a44105c01754503013100c2d600d00c214000c1c190068511074002e0481008030305020701881c220034a5034541c80309141601c0701058942201608040342d00d413000304248070b60800c06480d042c08a40e00001500c038043e25020b401059049a080368414500c54002000c4085c02c0d600010380d006170366011442c1c7d90f1150f40e4154089002030944034400c080c420040c0f50500c608981030103500050800154808503c459400c0401502150786407903154218600301c541c00f80540d50082078644000c5242211280d00b042e1070700010300609040607150b109500451b0b90b86015114104540c1c6455556103a03001da2101c00080c1c2d0700b000c00d02250800d802d0300d501d850018042e014081d00500a0041a61001c03084001e22138540030110000d18014070101e64000c06114842c041c1409 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 466132194 1250 466130944 466130957
    0x80a0609060b221109030a0c080c0d0305040519090504051509340f091b110d032d050f0610050f090a1505030609010f12020f12010c 58
    0x142404401c1e910b01d00368490045041c455445031a140c840603404409141000010303020b0319580010400d48034810009505110b0390200030103111045413101c04031102c2e0000c482c290203040c400c1c000e070902d01d42c5014010601c10b0008011a0410700300600c2403203c1c10742a1a00580c503201100c0803904203540079282980188404107060000b01040b54116051038005d081d08143e1102200aa101402c03c20325001c42402d444d08034041001030342e50149c515800d15485583e1580c1b11640101003a100d034000c040d101080d071031030312805502d0a00d040203c0304041e180e540c9810006070058440360b00a9000b80c0c0807424000c0f81551016050b13010300c5078110f4049402c0c20120f0030712030621780c0030300118070491070865101d220a40040c11038012108540b45c241d01ca409080010f5450320103548400000da01081c0d030b900c440d55002004512038602161141c100385d1300c03040303000511044e500529034404488110a405860321001d82d0f114000c004200c5800400952246825900d15000b04030110780d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 466133444 1250 466132194 466132211
    0x705030f091b04020711031207050105070806010516110a1e091b0c0f02090703020d1503110607080d020a09031a070e0108060102010f05010f06020c03030403110f0604080a06 76
    0x50300c0d820349410070820401032091400e003440c1c00400c4402e1024441c4519800210031301001203030001d40e0500800101914041403040310307c0561039100d01c400712069440c11001424a5002b1003001d4055401030f91094113041041c00640c020341c0c81071f0001c3ea001201102a810303556100071035000036140304500c0f0040c6030400110002c01c130005800a424190501030b03941d00c1009203401c0c0301e442e5141c81c513014003285c0d2030f8100320f588a0140340307000c1e4118010b40104101c0540540007000d450a40d0b040800050603180e81e0301002d0010f41c0401401550388d4559104a803802c5005480098029080545410f8a00c450318049a000554190110744402402c00910602034a010030380491000008204d20b4101002003590103d0071946d41881602404103035564400d50065000c1002d43c14100070a50b19004050502d41d024400e000041c400c0c00c024400350304010040d1012258003c1d40000c40404031010413401005d40007550b50842c0007407200003035917841005111320b9580641c0b0009102c60 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 466134694 1250 466133444 466133461
    0x309060e0d030b011b0f080a110105040305030601110c3102120108011d0606040c170708041523060402090a15031a0f1201020904140a0c080115180e070503 68
    0x1750700017001c5000e51140100400f00300f500744e020314103a61001c1c070749507110507558050780ea901c8803001c05076030fa42c680400c200c101500000194003681003600c0321502103c078288240d94a8003240c440681242c1e20b121124030420203582840c40d801c0203000d403a14641101d102420498012414020302e180c50707075004000442083c81180c0030302004107541d000c50074040d50a05e90703440018000b18000c1c2c0e5180240c40e81d4034800c191181000d0003080d500176a42c100344000400c0807909603400ea03100140b00903542c1140c0075920400320803203400c0c0ca644d40d008104003031310790340000c00a12864001d81c08008200041d5110301c46040076040f00c00c03020044182c0301000500721814a40d41d000340405022030f0141950310050f0350032200d04100c1e41e55882c820290211030182c080c06c10015003180c2003203807118903500d2075101944a40c00180041000c407081c0c1d2001ca0b910700081c8254901c1254001820721031a200300e031900c101031001300920000e01d40d0355180d14400c40d0211500d40c0002d80101c244000c54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 466135944 1250 466134694 466134707
    0xf030a0b010317090612040206040b0c0609070501050a0c0f0812090304090c18140a05091e100e0106081b040611100b131a06070506090607110d0309060e0d030b01 71
    0x103462049000341021004c10120f9020303c140f0300f81c40840a00c100018085503990401c42d405001e00000458031400900e01c125569030b0180c0322159a0f000740a40819154840c8080d10f04100c155643c802d10031029403110310b503c00075041d003510560000c10070000109040850300d405503180000560f5110300e0f040c3c151040742c030b2054101040000c50b046c10204010301e03100075421707104941c842d020f0f01c5010100044d0785e001c4d198051904010054104204410080780c0140b9000441d20343c1003031552000d142c408000000c0c019900316004110051081a10031080c40b54440094994610680c5c1210b411080c030740c125511810001c1c00e50040b840e40510213010110201c56842d900340301c480c0e00f0000049541203001790942e002c59603000006056000301c4598503e50001910301643c400043c02c0464032040c085402180602c503070341c0030900d007031b108610469020b8403d4010786a8022605070840246c0716030741058410360744074003540720b004000b4800d00e041002962000141a4010700014098 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 466137194 1250 466135944 466135973
    0x20a020d0f0503070915020c0d0503030601090f0302030a03080717041b08060906070e040621030813050309060a05070219030228030210020f06130b01050a230f030a0b0103 75
    0x4002c400e2003400026600f191408050b125200324184c0104042e4108a260170b01301d050305540003144010031010b0090100042d40501020380c1d42d00d5000d52038498480391a50341c1d1000035010760280c1d0030803000c244221900c94000103c0d280c030300441c07000c00200f0061228155800e6806850615104034207411801c643c60090524201501726894501c1d1250307180d820007007000050040709d1141d4001e60759598010005011614200500702104c070880100c06c442c9454100c011610751408070b02403159045400c008154003a0040d850280000d0510446030006540d90007030003414080031005903556450014181d12103030051011a296004200c0c0024010321905168141902c65900011140010b2402c6c1c0c0c1d0142d44500c8400507012080745041032028401120740101400c0c003c590441070548000207008252105641c0d8940381003044002070340c41f854040302c0703e0140c10324a00c01c520005a004000c010055a1441604004a0308144452400721a4561883d0040c0100985080078050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 466138444 1250 466137194 466137197
    0x80c09060906010f14070503090a090902030607051c050a02031609050a12020a080601170709020a05042c0c0a02010f06030b0705031f0906210b0606090d06020a020d0f 73
    0x154184000419070207000603180714100943e003c001c104441c001e488516048282c44103044c2c0e81c0000f03080864481d0020203800e480b806401e0380010310f62055004150850b500200038090980354441c0039200ca0707009083c0c088407032610004800c1032030301c14818640f1840300ca02001d6a07034982070301c400c154403a503190820140700300c040050106072545019003041d1120111920185481400061072151650f0b11074103191065100225030480b060413124050398034001100d40c600d441d08a443c060b406a610a034000440c18881000000c08541485c10304845a07800c2400f070000f00c82c04018043c5089444041c4042d002402d2160326a0900c119280d0304a2100204001c50035030340c0b4290500720107800641007000c0440401c203424125260034228581201c03461003001c7d900c0d18010042c041c684201070400e00b21550000c0c4a40085d15885169076103d0b81e260303020383c1c03000201b1000b900040c0d00b2a410410302003440c000504180b00600d0701400540082200d07400d4244014800104d502c1f0090 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 466139694 1250 466138444 466138459
    0x30305130b01050607060b0d2301060608071d04091b0b070c0b0703020f0703050606040e0c0325090204030c1e030506040210030e0d0804120918050601020304050a080106080c 76
    0x34042240600050b0650b0000c4420b203a0750281828254080c0450030b8140358031410740107449041080c9424030b900000405070030307480300280d80b5181034200c508520501c000300b130b07417013002400c0315102c0e04080e01542d038001444a102c0c980d0101241c12a012241e0484030380d1131030b0610403a8100700b0361800000744901003c840c5818160350f51885a034210340310712100c17900f01041c0a020103000f8081d0f40103180400e002c9844840d540d0400340d0340c640301610201d00130351900381e4043c44044082240141e10034060b0062500400d4602c1e280321107044101d0b0300e1010081d441d03011448003128001000158007d0107006142410100c140780340b03042e0300d0b806280703252080c50100000342c2d02040551340700b40c04452000c00c007090181d040d4040e1040c1050f10300135000d4010382d25002030704000351500403402070004400d4440c44500503900c802e03290084080350a40c03200d981130b841410350132413544401c0c10300c1945e007090794520200d4415003440d00414500c0e5101c000078005020200141c20002c0340403607100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 466140944 1250 466139694 466139731
    0x3020102070506210702010507030f020403020f0f06041d010f062c0a0e0a0c08010806070c0b2517060603060109090b1503150301240e0901061d0103030305 68
    0x10795104440d1055038000c11000c2805805001c49407081d00c2081c401c1074100c8114030304008020b00800c012100800401e01d0103290000c1481d2901c2a40c007a40d5010780019072000001c41001071031703401181d5990f03000303804100c04502050707040c114502540d000c919041c11541007030210b500d058800e81100c002c0020680302c038083d08400c4d4809400300c03c100c0b0b02601d54100c0f00700103e6444a801d4201210040b00fa1007442014806076001d151040c4640e03441401a07600e40c441075864080c156202400076549080381c1c0c0200380c0c81d108a41d000040001540c0242111003010454803030071444040208101850714214454a24291544044103c40c000d2440c901840080c00340c0c8440c2c003900304c42546d10b0700b0a041710b0303d0b965110a020710014200c0d0b0b441e4a032500004560322000a01c060013542000c01d401c03d0229505000785119a00724070504a032800c0010360300c49010010312440c415900c500d00040c046141d000c4410105844406a031159811410050305452010f490300300202c081c4190b1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 466142194 1250 466140944 466140947
    0xe0109030e091b07060204080a0305040e150a09020a02030c0105100513020a020303070c0201111209040b011713030903141b01020a030e011d120d11060c0904090311060f1b04030201 79
    0xe1a800300c43e082c00315031604414140340001303000e65042441c45204c1c0c000e61100341608040580215007100d0a19440c0d0341d01c0d21850100340b02400511604020142c4050000f1500c030740103060101001c0c030440c1d051030a1104c03034a095030425954124000002142405242802c0315100f08840c208503042d4906180d90000035941d05c0000d08000401c07808044242c00c580c443e9013100d025500606c12281000c405003250101a4044441680310741e28003004100300354000c402158907a441c2d1a40f4488942c0c0c0d0303291070351847d42590303000ca00b00442c018000c40051521019204140c50307a50040c0400a0b0640800c510119140314942c103550024540a00003548804610305640007840d110484002d22158641041c0b01d08060903805400c6003065095060300060a440c04401036a0381c44004403a00d0859455039020385261a4079102000500c3c0c5601301a0000c800d100e219181a412003803d40304140e04010007540c0c12004041c03581c0a1040280759030507680350320a600d400341031605145600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 466143444 1250 466142194 466142221
    0xb07020c060301141020161d0109270b1f0e061012111206010306030b04060c090e0c0904150f170a12180b040e07051b010e0109030e09 59
    0x207041c410602e01500c1e805d150f1003040d01e40d0395034103030ba1080707031200500520315521004810501c0c0700207010000c0005141c8003611004007200c910980a601c40d90a006201010341000072181c40d1002c404480c001c0c80c020013040907411207009000c911507a00301072121111000b10401b00410001c002441408a64291106960013000842e0744000c90700041c40142c81100b10207141010031498040202c00403a0f099004188002c3c265011003290380c1c4420064049640c18040a0001641d09000500003202070b88240304101aa04241c403071030f965140c1194683c001129240d10300382e4046509070f407a09040c000c4000100846a5012140e070030711031a0390840380c240c40b50b000b04100e203e19500d0640001e000040300707aa00a2091500781c103082501520801d00f098564070801000709000a8505e290300590301038074408035884a0b03035151900222003d13081000d148402c40c200d4032020000d810709200d0401c81c1d40d222000130030540802d00f4040e04007000c003880c0700e010707513503900c20029840000d40c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 466144694 1250 466143444 466143479
    0xb04030203130b1c050402010903060e0304030605010f0806180a020405010b0705010c020a03050316140c0a0b011e0603050c1b010606120525050705031c0c020c01021b19030b07020c060301 82
    0x107400045d030343d40d5400100c40105160784040d008911385103400e049404040700400580340140b809004617607035460b03400307600301140c400c2d2000c030b404c81c030042009003024440801c9061201011200682420340002d07080710001c0c3d0049180c0180040da44041240c203000d40d40d40d04000d030014040c400c0c1640c9010344944001000d00f00c01d407502d41000020580603551460300750140c2c0703540c0c030f484031106494195101c40c545825102204c48100002d008502d8004040d00321603c0101382003064a00300c0c082d809820007500c1444140b40600101800708000c006944001c44443c6c0041040740ca00f000c0500011400d00c145011366040c0810001c20007003600071035801350f07900300c10082000100315040b502030103142d20040242c040000d90700c841100070f903403204c1116450801003014410281e8107a85d5240e1800607207000da00080101e00003280300301d19140c140e100107404580d280c107081000c0061003030940c00858082c05000280000964104241422071038261400d81c91941492450703030b03444040c80e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 466145944 1250 466144694 466144747
    0x1a01020c120102070605010305010e19050c0d06020c0d170c120612010209060a0216060c051b0307050a1e0b07080d0f0b0a091a0105181201090b04030203130b 69
    0x48241c90241c509604440300140c0091040002c0c1d6180d01d4401d01030f00748055924441d214a104171085010300301d030503542c200d500c00001c1814814031410302c09104050142039400650912010310301103811310503500b500000359507043c00c685140d0a21a41708801510007000510144848014480c4455816070031404c1100e103072102207696003510b40a48180b90b03107990440c1020805600c01600020900100b104601105d0b001b0342d115031080f1100c1d80c403003074050816070001180030042c0c803010740c00869108000e025552400d4440002c1050800c4603480109208007640307600320703841c0030301070f4403000741441e0f40815152400c00d8035018841e0041440110030155102c070100d18106d9a40e102d40e20062000e08011103056842d08a50000e20300c031055121201148590390500798070540c00c0310340d686424401001e25520100511410310640040f036003456603180040d0003c40c00c00da10396486644664021913480d00803034991804c02d1501d9000420b0500180145203000c0b1120001104800d00d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 466147194 1250 466145944 466145959
    0x200d121503060f060f0f14030a0f02040c030b062110060f0f020a1505181f15030204110405011404030c0306020a0521152d0a271a01020c 60
    0x30440c000401344d580c071241d68400720b42000100c1044003100c0c03100b05c800e426101619046000185502c50f01c00d518001c141c1814aa414001031400c0c1c0d005284a2102d4a00010f007000352a0202d15a43c1c0844411021400d0500c034a1008040c00c1d1441c50b8400c0142081c483d010b85810b1019101c1c009051001e42405040d203000542207208004c40f070360040d00800c0b0160f01802e805049402000c043d6200400310300030034003099070000000354800254102c441c50101ca00b080300540002400600c0035411691810130000000d03941e0741c010001c0c5941440811307582c0d14a407200241001605030040060700d00f05020800215180c110340408481c1c11035000350781c071080c03038004a525205100034040100600130281d44900c0100c52035034801d4101d41031511160111800304500c141614003140f80c850f9040b4410100c01c140052050090075000d0204000641c441104100c40c961615208002d022030801c03c3c288021075002e01c407442492112610140440800003e44481070201d11074050a103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 466148444 1250 466147194 466147211
    0x905030904020705100c09090b0321090406270506030a0f06020f0405040e070801050c12160201020f0a0f020c0105030c1209030f0d0b12070503071401200d12150306 72
    0x80500074036102c81d1007100c08111b84100044068214585c40c0100c0012510f424400e4042d42000030f01d074104840c0942143c0b455058040141c41c40b80c1c4011003a03a04561a04800580c0360190381c90288200c1219403038646c101080110917040b6200242024440d60007200c0c4075010031191000c01e541030b90008000740e40c50094141c0044544121303032105400901d403094888509002042c0c0307009130740c0043e000784590b8846464a108074012070401441c05442d290201d0102009100f60240e00700460001600300802005181c000790010502c0c40046a0000a00a009541485104901242420f18504508101e410511075020303070034000306440d240c40701040240344108261280c11082c0001142e42c3d20a8010301e02c00f525400181f18015588204920b0034118089409002c5e1400603000340b8559141861000d00104038400031818032070340c2007043c082070403000c3c00042c0320b11030040280712100482500070883c1c0500c0c01c00d907020502d8140c841c6580c1c081034031140200d903009000030032041c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 466149694 1250 466148444 466148453
    0xb01031209230307050a0b030907080c01050901050c07090e0d020709150302011d220b100203030f0a1e0506090a1a13151e060302030907030f080903060114040b0409050309040207 78
    0x8040d4010a1b03110003826000103c0120342c100440c400c81142050305ea10f6965200b140340d8840101c24000d0101d0b4040c13000c480075521800260401c1c00342002151000c96490880c1c00464a407a0510381d156000b981d03500d54440d8040000e04c0c001c00c1c0c141070800c504070100e50840c0104000740802410414180c030b402c046250742c40103010070314100802911001000f00303001808c006c1500d82c80900326082203c00c080901c1e012403000340c18070301c41d00a0362075a40c4020940c541710000800b880b40443d0b07141e031440e600b00e00601200c103a41388003140020709414890100070b03880900401403002c650401c0c0d1001280340401001007100b007410b4400c140044d1140d1260b90190071102007900040c0d00c074210001d103460130b110f0400c0042c0d210015540750709880707050450592004840d01d204560003000f0400002d01140003528080b4090014030341402c2d4140000703400d1503001c4c1d11010b0300106032200c0b5205442c0c04c0c45140354440003240d0070803440c8081d0f91416101c0c0602c290440c80303564041081400e10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 466150944 1250 466149694 466149703
    0x40f1d010e0f22140601081b10031808040303050d0f05041709030c0319021807140a11010f0903030e16090b01030204120b07090e0c07111c0b010312092303 68
    0x341e000503408601483c912400350b54a0742446200343c0b501c5114124209084408c0701707541d2824010300f2110607051100c3c1c00303030003419840e40040c5005840e40d01c02c1000c14041e1020304065442641c0700c0c0e0345c4004802a42c410b94101c141451009480c1209020004061903103401c020200080c00d1604d881040001034280305650805e02e401d8040e4410254804402d007000e07240d01c500c200d0f03000342c01c2c00b00c2c002c2003114001d0440310400031650704141000b035500f01c1c001510300030084d403801d070349400301070340303d4500355020520740c06402c42c0c0b6042000100b43d01409450002c03000d501c0100143c591003500b04d84410094442c5519203903484d8946802640300743c040720007601c840e50000c81800c6880c03820403182c074001c851850008004480200381c40c010014500d005031a43d011003030901065450703d8000c100c0005039158418100507a51414400d03606030110028002c0104600c036615500b48400c81c44100b00005081000c1000c0038400c2e401001c1c4030008032202202d501d60a410045c0209250 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 466152194 1250 466150944 466151011
    0x203332209050a02040c03051006031a100f02010506030c06070620030c030f0c041224050a0218060c1905010b1c02030c0d0b0112030203040f1d010e0f 66
    0x3400c00c909071060180c002031001d0014030a5604100d120846007044044034010345600d103034031802007801c20440d80319400501c400e0700c20112506950309000000b032502c5070382e00d00c0c4c400460041d0384103110a0b9028070074140e0150b070540140c00211403400005800303102d80c010040c0000d40d5031914156105072401c00340000c0780c0326804c44e075480c280700c184403090350000c613401c0703180380c40701c00010728100ca0502c191401c503118085502000243c031307130320103001c0240e0000d02c4240320100c59260516032040d0040a005900300390380140d5451003510b6102c02000468001401020200700548042c03000140e00e100c141c041d00441c20380c00c111490902d000d40344055a01d40e001420802081307034001c0d40310300c1c518070328401c13401c0b140b54110030310601c45000140c50020b0701d0010f0301c030010805603905e070010055051003403054a1805444400e1520320710071ba6008400349044c00070801d90001036181d211405442c100410780400e2511420190050000520000030039140c602540d0f9019040c42d1150b61 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 466153444 1250 466152194 466152259
    0x2161e0312020106030b10050f0105030c090a0f2105030301050f030a080403060b01110c090403050a0e03060c030a060611030423060a08161b0f0c030b010801020333 72
    0x100407036a0100a020b051580000e40360002101c02080315509485400c038100ea03800340c00702c041100d0700001901d10340c00041c04c1903403581d41000710f2103d50344d0384c401c102c000c1e201c0d10000f603650900302001c51100c940080060f0484119070500e40000c90300c0002074034116542100d001d0f1f2500c116201080c1017117420000100108408580442000030540200c29206c01c280e0f2a0303004003170003038001d0383e950b8624031406030002003010103c0d000c240b040c03000b041d80c400c141c140f0350041c00100d00030030b142890072a45c415454001000740116a0860f0041c030008241900d401884504507840d800e4807889907114070007105800000110b144c144c00d44001e800800020441529601059009807441108650351180c4101c401c505a120500507144115142820b2142d0826501241e660014001920500303840c903101c070031800000076440c500114042c3c000d503000561241040a0f10301c0ca0b005142040f070f80480c004100040c50b4001802003512040380403183c0700c410b2070914420074240101c41a103075a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 466154694 1250 466153444 466153463
    0x40504081c060e060105040b0711011803050c130504051c12110a021507140d020d0c050c0d02060f270f0703031409060909070207080d080703050702161e03 68
    0x4510400c5544000c00f1a1003c0c2c103607070126a5020011601c600c9640103e94150070140104404202c0c0010b502030b0110041c1068842d16644036041250001c50303038804ca9560703108524001550810004c840126220348a060140303051903074541d51a1107002409240071000780c40d00300c807040c0c4603001e40201c0c603030310030810400c00921000c2e81e0843e034000701e50500944074400c0619088410180300c0c621544150307554865036240d040c00c201a03540300d80b840c542c0e02e076000c0c043c02d051036400c0d2040000c501c04a0b12048d689008040701c1904100081085000b95044081040740451000001d1a0301841341103201000410301e8110342150944e01c070800e01c0510800007002443d1100180d448160390003502c1d02e08840c40c0e9280d00b0032091240c050302a8000c0d50600c82c0d41c2e110306050280399040342050059645040d240e00b0154602840d00402000140c1c01e0400e1048168040c4102c0ea0056420700c040c01d40d41820f0f80400000d05542d103d10b99100300d0300c004610610405c0300c40d840c0550781c000c1840 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 466155944 1250 466154694 466154737
    0x702101d130518070614070c0503030a030203071106090717010e0703050d021204050d030c05190f1e030c080c0109050303090a050f030a09051507080c010f0b03190204050408 76
    0x407001800304036070030440307007420f00482e200072003000800104617082a0b8841d6041c08503840740700241d800c2030030b003143c9103000e160011070346542c18009040c021a903541e0040c0c481c904a24020b101c64004070448404c1e40051080c00441341000c00c4410a4a1070654002103428000ca080c40c0100036001e0b00c00c9050051400200400c40c021450740000401a4210307040480b107407815010f58815840340c241d1152042d004207000030300400c00d403034119000d031041d01c1d4220955500b40900103100c0000f221a000302d80000d00c104560841044102002200e52120760061035402404400c40684003515222020990b09105c00f400d400860300c1d140c0c80802c1e261641003401300141d0b07030b10185600300d0341800f4146803000201c2c00003090b140502100c1e0707a50600289040140710030000120040030307a03903004000e494003041048000f801c1a01210780001512090045410201e80c0f000e05540d1198115044c1e0200ba41e038134070ac10f1703019035404540004490f1105c1ca050000d600c15105000340c0f81d0f15000702d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 466157194 1250 466155944 466155979
    0x60705010e0d03181205070c0e1b0a0503040204050408130308120601140d0c1205011202010207050a060e0909030d09050303010e0f01030c060806030109021e0310020702101d 76
    0x562280700e6542151000100320005406650030007a6202c2c5410200740d8074808181d21341010301940040381071a602d45646521072250090030741c0c200c070200c03520a00610504400d258615915604070006082c1001444807005142c0c0c8000303030019102d05c0e00c07040450148030b1002d040300d904088130303c50003983d50303034031318051003e0380140d600c800380150214000303401c0c0c2d40140380e4064807030100300066241c050b01d400110010184034558201300001078103031801031600f510407a8082c000f40c03440c0b50242031035031000a140c000070390011070041d0742c800340c1000301c5070304203183e002140e000300e84a401c0c0b583e80c202c12528500902941c082118104111301c0c0601c8004030041d41612004034074122a81d5404406c204a05d600788401010b40014900400030144038845060700610000d001280d051a182c001444141c0b4403060702801e080b021709002114a010403d040c2d082007248015400c107603468000a0440c1c28501c40d003000c0c01209584140c2129510189000c240b200070b210710080500d1031034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 466158444 1250 466157194 466157201
    0x1101051915050d02060d020d09150c0f02100903030e0d0c050f0606010c020918060a050a0f0603050c091e090303040309050627060903010603060b0a050d0c090b0f06070501 75
    0x110419910300e8200c1c41d20540c01c408103a68140d550140055105150560a11000e68402c8146401c000e50030700103940e41ca40d050045104850003050300e2812010409180c40856a10049071010b1040800580010366004101e080030a401404005072a90305404d00f5805030084038200c1d0028000d41200281040e00700038125002ca0141c030480d0f520f10b01d401030740c0e176403031a09a8001d80400c2c5082004401480e06000856000b40ca00e0541c0030700014042c1c4840c80c2040a44081c2c14660700c0700204401c49000c2d01c910f42100f01007000c10300a60f45142c40e041e4841c601420030710b000740801400554014a101c0f420380c10045028540201460407100c40c0ba140e81090710120001003d6500c0001d40e8070342002910a03011b81c43c424410ba6084070102c440c16458143c00e00b0350090400d20500806642c00c0c410440198007620020131100101820401c0324103058000c0d51007109825010300c04550409041020768000d180c3c0000c0041d04200060030054083c401164010b60001e01c0404201e030640 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 466159694 1250 466158444 466158481
    0x60516081216020307030e09060f0d060f1a0a03120908060c0403020102010b01030225050f0307030804140d022104090204090b0405072102180307060942110105 70
    0x11802809140c2c1c02d0040b07840784251040a0006040c2200c0703141d0900d406000181c11500040845010f080c021010507001d2000d044103a4040740d4507003440308004481d001d9070302105a1a5250a42e1004100c000ba20800c403500001d04082c0c50004001d02040c040c640d54006456090200c0d0b4803890182d40d480c400f6031060100b20300650030b100d15110694080e00a8813080d20602041c800c022052078080f5552143c100710654141c4074000d07103016580400d10042901c2c60280d51a407029150500b8030b44840d0380c3c6490554030942c02701b00820710b510340c0815418802a090701d1140080c4480041c0704000b0300491f0401280c2034400a8000341d89074880d4012500b034070003a1001d01056507040401d81c1c0b44071082e03130244006003010f5540c4401d5416980201240800041840380240049000c01d18022007a0801c0f404202c040005001c0929900c00d640c10140e075034603242c2c1c540701725160044201340c40b090198014080300c0a9200e0454000c02d281e010507807500c0c000708110310b85401e80310290782d00003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 466160944 1250 466159694 466159711
    0x60108030301061115060103090512130e0f0c070209041a0703020705010c090b0d0b0d06050f060a12051c050d11030114030111040608270105061c0c0605160812 70
    0x44d00041303450880072030b050788080c030381e00702c081034070390b0390314015800b604000714112254015030b80950380209103400a03042c82005c1210480201d406e18045140754070005e0100400000c0410400c54444440d00403180d0155040d20041c14640340c074905030440c800905050380742000c0001c10070264541c50360140c12002c0c040c1d0028850900b0024055400345030a01502c0d103a00b0b0104220441d20085400000c098040a001ea501420f819100c490443d40d06a5000c540711160606000d4145400d5001030003030540c40c034190b42c0380686927690030340c0d035500e05c00ca900d254508951049410790065082d03a45081f4800703818084c03ca0482c041d44c400d40e1003401740880000611001ca0900e0805218208008640f203000c0d92800f400d002c016203141d0710080000c01c14000c5159140054249440c1c00c4880004000002c981401d11001304a0100381e845001012a084200b0309004180c41c0310a4070200c440d10b0030141da480001c00700c0c5251003c400100544035810010b00300c64440099503406200314100c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 466162194 1250 466160944 466160957
    0x5010803032d01031b05060d06061403011409040201030204120c05031b01200f1009021311070609060b101e0f02070e091c0e04060806070c0308041406010803030106 72
    0x400e0b0184050006480c2c02d018035046107001800000d01800f46440c1c1c03440308006007810603580f00c001401552004805142082e10b54804001058208010320341102b008280103046605019010042d92817502c07403688078400c070304041801d59000b13504840c06010102090108400c880c02d10b0b0282800074404e03240644100d550000401e034580000400c07100341607480c0c3d000c3e141c80303007001c440c1e42c1c50b000c1d0000076900500c0c400070105c030401c1203d18052000c41e4008107014120380104070007a61940c807100d20301420000c1d075110300c5012740704854007260303c4400082c19000703500303100000f015607004242c0c1000304103918204560700b240340001565101000f1001c0ca441090381240c18110881c035050151340b06280034000310900302242544202090301300d0349142c1403031030758003d072421b1080070341c02103410b102c0c04443e81c3c202801801e010340a07403002400c01d82008403005102480d481c00240c1081b614a002c101000414030380000e40c0704803a400c0340d0043d611884260f0302d990085c840c04010418 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 466163444 1250 466162194 466162231
    0x504020f0108090c0607140604031101050703020414091e090f01050c07020102150705160308191a060d060801050f090d110a321605040501030f030c0507090501080303 73
    0x200b9240079104008440107080d04c0c90001c01400085d41180000301d90300c280002d00303c040e084041046601c5207000e5902c2c01c4200c00d00b030020f58212a4040c01e01010540104814001e8000c02884880015400d4960714181d0751810403100e071072030301c0c1c1c0308a00c03500a4110a0009a98000030700017086000c0740c00802141e21003025180c0503125481d0b0007070240c0c002504106021440c00107031035021085040192408085a2401c203d100142c0350880224003050180070b980c0c2401101a51510a901d80410000e045040942c8403c401c16000c14410440003503c8141c00d00035400441c020209000248140d04140c00241c6004404540150051243c10b5035000050302c1a4801003208c4c81e071f44041c240c00d406036284c40c00e00081c107500e800000355890004d542904100760301d83c49034078041c6000d08000c0b4940c1c20f07008042c036056400988110b083c10010300100d0600d40c030b20700344941d050801c80d00c07115061600794240070b5540d0000c12513174078080001525210110045216000c0c00102c41078910 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 466164694 1250 466163444 466163447
    0xc1a071805010801030b060f011205090703030815090c0309030d02071101140403170a0e03160819051e011103070905150f0a08180d02070e07020601080d0c060b0d060504020f01 77
    0x300901c17024284460000104240742441e0001c84078041741850501d2015018401041c240c030002e50786101103520a40f070802c00c0c503a01a54091308000003a0640d50703a03240c0640050040301c400b61040c0e101170b00020124500e0b6108004460822580c04001c1d5101c00603400c0c03a00062800039113003808540c210380c821098031107074001c132030a490703100c1c0c1e4103920742c48000400b100380d8024406a00a00120b800303076030740c0c9035003c002c071070a90450703000c58186003810300c06003071300f8594001010440e1b0005940658002507010401d2504282024008a0381c3e02ca80442ca60251550440495801c140001801130440e84030040000f50342082c0ca95845a00d2180703100740440c440c900110150050a110600c0d282d44200b84013504003840c4032120304801d090380c2c4000d052070006550345000d030380440420001403d86c03802c83c40c0c2c0007400d80050000c0350b14020885484400d035445a404000703031182c03400200212a4070801d100351000c0c0c940741212941d4a41800200320940703069208030034042070944190f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 466165944 1250 466164694 466164707
    0x6011220040f08010203060a030609050a30030b061e070b09060a0c0c2a09020c030c2401030f05120a030b031b130e010212040305070c06030509030a0c1a07180501 71
    0x3040082c2c106015207207151503a8004107440140cc81701030142c0c5469002155583c0310446001c1c0c2d400c4030941c0424480300c02c0090700d6050040710410316003401d109030742c140e4a46040d0361310f04d880f40c4041c0f198000c07155400a014464982f00501c0108641c06020b400c850000e481d902c504003001e0301b00b2036507026401c1511403002c594030040c0051105030000b89401070b14940e050007071224008101009841349442400e07a040b240000e0722035400410b8480b18140200400300803080c82d880c0e42128200f40984c0c0c1c144a0905000140c6152005a400300800c0800c00c034000c070040400c0760181c1c0b00c404d80340008000e40051500e00d84a031040b019590784141c0500c001500c1c071380006003c01e40c90080c01c440e4202424504100103130395542801500c00b0b2070309040801344101e1087d681d8550710140391034256070102a0b5040301080610785810010312510004c1152114061820031119002c01450a061407502d0300304100c0c9081742e1407080c405210b400840c0e40003529041c0f59850300c41901c0714011a201d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 466167194 1250 466165944 466165951
    0x206040c0609080304140402071403130501080405062a070303060510032a02070503010501290c060408030c04080d080403090b1c090602040f030803090c0405060906011220040f08010203 81
    0x1513802c100410044008208082003c0303180140003d41005550b4482c1201d15007500d20002c0c00b41c00014460011110341a81140501402d0800300c007142000d440c1c2a959041c0148140c1f51590030895200046000c1d484014140a0266030281e0b940b00616004001c5c000911030075010b00340805141040501034001c030402050014107519140380c140c0c078400c072511040500382c5c065000b0014080b41c562802e0180f039018285092000700100d80c0c070107003241c2140869000c0c01c3c480009104280d200c0c0e10200d2213680140d00500b0349501e0303848030209800140f103103a002d15468812809182c20300c90f00700300514030880c02501c40c064a103544040c1c0103e248500c281026280d5001c1116884000480c2e112040c15805a0001428030f9100c402c0c031120340190303800039191480080304010011004000351401c2c240282c4042c049401c0c84004165420406004903050102c032070001c24407940c665104019140118101039441c901c1c840100241c1d5010740201c14880360320000c0031500360414002c4900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 466168444 1250 466167194 466167209
    0x207060b01110a0b15060c032203030c0f0201120f090204050906130312150e04050d09030804144504030509011d04021902010b0f0a1809050109030206040c0609 70
    0x55102613503a45154040e001060800401c440c8845000691602d60192030501814001540e0b9000110307031040d4520035244250341c5041c0d5001090000070703440710819481e9503103c0664816168144010303142c0c01d18820141c0a19031802e0290700b12600d107600405000c900a44082180d5164214800d071217403400c441a680101e4488110400240304511006661200550009084501a80d143e62240f010360050340c00031200340030701040c0a410302005642494038140b020449140d5510a40c03d80528801c10503c0c20500400511039103d81c0322040e5841c1c0d0300b1000422081c0f403400201020810300101c0140d40c0b41e50004c0c1141d12145800aa0265416489075400e001901c0300440351040d5407001162000d051445003843c82d200e600292199400d00240c8085e0f44541100003030840c1c9042c01c00c0c40c440c900464100d0700c542c80350382c8004150b406000c84000c01000d01a1501c029101c0c45070001d04541c0303440590b00c10b065001c01e00303d006502c56026405410341e9040c3c00c803607110540c0203105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 466169694 1250 466168444 466168453
    0x708100e150402070f11011101020a080604110d0608030307091d061215100e0a050f1503030705030d0906050705281b030c03090501032d020405130207060b0111 70
    0x20001280c440d041c50140034010400b510740b84007a0b0380c079029000460070440f144d8502e0002d42e00c5968024070a40940c0c00c5200c021030503c4808080240403010141c0003d001d241d81e958104c0b110044c0c00100c4038940049241030000d02d076a00700160f9a50301c115118000030b040d82d079011585d444401c4000030b05000c1a0300f4dc81090700c5200410245420741c0c0c20000c3c0310311801c140101d4a07080107030000d00c600b540048824400e403500b50006000d1000408000d08545000d0411a1006084020642141d82c1c0b5582175440d440030030200b4914400e082003d4013074400810802d0901c546500503140030340c0f00d8003060010703032120441a03481b8000e8048144052040e0130100000b008480381d502524404c0380382c4508030095140352071045120185041d400111201405402d054001640b04003d0500f0310b02001388002000b1021900210760310f06401e44040340300b00001200081d0140c501a08006005442c08812208510001e600080084560302e0030101c001d0032540c011404910140704010281 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 466170944 1250 466169694 466169701
    0x8010b0307030b16050c0d08070e090702060f0403020106090f020c0706050415050c0a020411090102150709050607050c0306090a0c05270423101103010308220506070b0708100e 77
    0x18600412004084410030178140440341190f141000103042c401181c3e10340c01424142120003c1030300454215103030050344010203020302aa03001a081c2d038002d41c8454034200907191450200c0c0588980d030300026039541419480252101658010f1402c41c07059402c9500041c2d9908040e11513018502c0f039540c40382c050780c0814000d039015000030724001d000380081c0c8120203616400901118581c1c107000441d1803007c1041402960100501d040410a50111010341c0c540b644000307084c90f0482c040d0314043d000200d40344d820442c04101c030401c0b000303000f400d43e1494980402040e0352006609826122801080400107050a00300030034010f400c4061814202900d103c1c455421000c0041e004943c18811000c02803012508640185e2601c850f10020341083c0050000c100182c40381445060503e803010001080010744c0e2404440210104203c04042c044c507070a101e116607403156220715000403000650100b000580e16034684180199100c6050719126805513011001250044078868490000030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 466172194 1250 466170944 466170961
    0x4030807080a02090d030504260c13020c07030b040210050406020705010509010c0b040606080f030918040516080718020c0c011b0f0f021f08010501181e08010b0307030b 74
    0x403254810001030b000340c40c00900e00c0114030100071600e02500001c13004601030040004458400d00c5640034003c150b030041d620000c0742520b0356809a1054444c0217015400b40c0c4510064040e58141550f000680752555502d0415001c0a4011141284281041c110f81c03041c0c20b020741c1c19a03060798102c4d40180303245070801005498a0340702c40d00b403a05220000309450001540401050303ca01c2c40b58101240f0140340510240c64075001140d03032950358005005400c2c00f9158404501c05503104100b0030041c44e01d550900c03500f00b8000081d40803103c0a035400100e0120300000e40c0f00c040310301c0e20340c4c01a610078009400e00100e009244040340746410600054200f90301c1010f080841841032490015114441d6440e10031120181c041241d44900c0a60544294508482d048000102100c4a001506d100359001041c60605004041c18041e1860447e00d05409418140020300781d10710324550b000001e640c650740042078a00c6804110340c03c080f00048182801b180003021a41c2c0a04403036801e031510b001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 466173444 1250 466172194 466172207
    0x20d140307092114071406090604050a09090b16020c010f0e04020406031b030c17041e110906011407060519060f0e10180c02010b130e060105030604030807 68
    0x450100300b401072000c1240c402035480181000308080d0901d400e19100d15003c0070410f141c0f54622940c1e040810100040101c1c5501050581021908241c3e035030b40107030000c3e41c58041c0c0c1d0001a0400050b5802080c41c010560107a01014000c1d40c1510703465030b4943c40c50303940742c00044500700140c1100c1e12490003075001d03030803007202c0c030315a402c0454803d10f400c40418105d0f0450745c0803400190321541c00d8400309241c005021500b103442e180c14011560340c01000380246052007150109020b03558002380074000c4484003040800320b510b034018400f001500307000c1d01c4e6005030306c9924410b2000001041c051343c01084010048421003000340d003010259203400e401031900030051040c90f1303800c0640c84801034443c4a010301806a42403404912402c00329022940e0707000904c07050a14440040900200e45120b1840c0b82081e140900032504c20f178901303412409403030510031543e00480305030800c0b0103c1480c0d030010245d03031001408841c00740c0c2ea220201903071500242e0700600415000ca0100d00041d11924 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 466174694 1250 466173444 466173451
    0x60f0c0c030209100f150c12020a0501060b0304051524120f030403050d1404091a04140a0e0a02060702010c0321050f151f0c060504060209030d020d1403 67
    0x140100c241a9242c001ca00c2c0c00c0300c100c65030441440710740303414800040742e9620b1001404107400070440c07060810340e0292014101140103000c20b07140c2021002c4080c0308115200159030b105009004a5680351242d21044d00300369800c0b1554043c24204203101c80f003000d13107584036900302080308901006500e83c041e040d480c082c0030347e03812003481d00540b609507404000d140d6000403824010341d6524690f06015040144121500e0100024890b019142c42a00e5054400740c82c00036600040345101440c030a8110720103005603507005130030120454100000004000e102c0c3d20410418400d0b00708604026881d005507040c001d40c0403d09115000155104641c1c02c5902440303414030b5404407810700a000d61101030022900b401a40326410445030307030742321100c2980050021401d50804801e4600041c150300d806025003002c061201d400088071407141401e0700c02290000303420030203824a401c150029601001072540288668034640c01050700c0040c0411101c140384d03458940e02e5081102841c02580f018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 466175944 1250 466174694 466174703
    0x604020f030f06121209060a0306082d1f0c02070b030c040602120301063e1506090c1602041104060215010905010b0909100807060203040608060a060f0c 67
    0x203100c00e12034508544000c1d8003450b50980a001c00d480e11a0401141c01e94042804000d904000603e0b98030302a002c0a440e2454800c448040c0c82d805500000c40090040ea0b005c260180310303a001e1743e100030f494038071450f101d01c3c0302d010070b0180d84540e00c040c036503103850f039001c0080c0810703c520681d00314054660001907101c80a10546001d550358003413204030b5030026545880c502d01c0c0010100580c0b0b404109540b502c0446040c854151f6140141c0604010491b001e0140c11190400a041d2445001d01502030914048040f032500d40044216150f82c4106031200d00c00104407000104502d890080d070500e01c00c20004000d9450320910720150500a001c5050403604107031100358243d20309400b040500080d0a980e8001c000c00341150540c64000981a40102006454100103100c01242c2c8002c031030003c50b003030f2459160b90300d407082d000105080035444204103001d0300d03001142c8507901000600885021b0350704d29883d07440c4e55007041201d00c41c5120b4040855074001001034858001c004802d2424001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 466177194 1250 466175944 466175947
    0x7080a080f19180905160c17041805090118021903080304123e0a17031918030c020f040f0506040c0921050304030507090614040b0307030605060402 65
    0x140d50900180b0704051194002049245114006076541150f031580103048044040c00a030a1203c26a00c03851411030041042001140e2080d0901c02c5038800142808041d1940e1503580390b8403044105440c941911001d078040c189070101d44950b9050154003a2400e4407002080078812680c20080c48060452035549400801ca400002003801000690700c07840c0500c020318005013070a240100030102104400045c41e00b079040009280031441990110103071442404c00c800285c0700516450801040001001500000c01d0300700c41d8114040a503000c0c6840440e110701803c884a50501603a854150302e0302c6414812040001092081c088050030f580013800c3c2d02d0096410101003025550402c4d41241c4240c4c9860512160381804d1061b628420f00d20b1030103810300c13410002528480401071099000b425050340b0180c05000051040790000c55100b412203210340e56032143c000c09005144074482c40c1841400e00c40c11141001d018800c0750020040c007410100d070440c1d0700c2c4802445c010b001c86801c40d60 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 466178444 1250 466177194 466177207
    0x4050708060709050f030a110f0307090207060614060703050a03150b13060206010f080705060703022d0c150306120f07030602090a090c080103030509030c0901061e0207080a080f 78
    0xc0c10320070540124220360394190414107060601000030400360307442e4003944c016400d51001c80c001c00107000c0403410842d015107840440100003031130200c0580151a01610000b04c070010000b503603010208441d0502080180241e5050801800d4028080082c2c04102e0170090391014501c00c0c0c2c040c0d040c044803054001c58486d104c2944111079084aa42524000300111090200c10b40400c001401003041c0c9010607501410714070041d495401c644505809031381d02040340c10826000b8044952540000e69560048104d004242c41c03540c030700440c8011241c040d4807500503007030030305810982d02035544d038040c0ca10310b454504c1800340f5000c0c549000c0d4080d014030185d44120840602000c00214000d680251315103e00c44200020080c0b143c0c0a07064480ca040808503a8540080712581100e8040c1490703034031924801c1c003103801d00d00102c0c0803661005480c0b0001c80c80e1600300d81c803000c0101046030016040ca0b41280d0590382c42860f40564200c55009843e0303400041d100c0e600605040207029031031420102c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 466179694 1250 466178444 466178459
    0x8190315031208060a06020307110402041707172d120d0c031506020c1003020d06030c0602010b03210c030d2d091a06041b0e01300203040507 62
    0x140c454008403403a00b061401c2c820501c1c0d002014a030004021244484c6a52070309102035500d2203480c0b002050644070f84892003035681e4540c103880040008011000780e152480113070507103c60460140c1e40344086400b1100c042044001940c090706203c13158448140d010580c900c104210521500041c3ca100e8050261103641c410b030040c0c11251646040443c45601c420300140960b16500001c0030150480300042080036400110466080420389203008003400d8104110082d100750b1140060260078800000100f00729103c01204a480d9580208520300008041640b80d0140307030130460f00500d0f07411501d1000f10448000304866034540c02100c0ca00f00742c2240c0768056400101260100d031b03600c1d04151786111510b0038030920311a400a010403011455a45034500080390714114518181c071800020720b20348850340702d550540b0b81003006943d045c3c507020b40104a00d82418000303000039144c8c04054000e1800700d1300c07031104603190b090128107400701d07851a8009407c000c2059446100b456000070381b00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 466180944 1250 466179694 466179731
    0x2412010c05090f060f0f030c07170d06050916030c0c060501081e150f150909010626070317190206011d0114010f112e09081903 56
    0x6005544032940c42d201584208042c2001062006011300300030000c0c0b48641c10041c048411948524803440d482e611441a0104140200800144050181207000e400743d8280c0c0301520006c82c0500303040c0012a192400d01c555001d050701c115000c00060601e000c1710b5800303600600525140c5103003c5041d081c881c0c4643d4196103083c0e0004140e6003b074841d19203da02c6800444601020a50082c80f0b44410764055041c0300c60020074165800c0f040320003040b1001c0600c441c0010340c500007401500c050800c0101a4020400fa00c1088400030701420180c040105a80901b4080040c0d01c011b0400c152031a1120130130880f8015165030000c0080255071080c0f2001002d00c1c41c2d44500303500400c031540c10700740e500c00000300c407182c001c1c0d40c40c8610340108018603203502030f004640c0080c270313044080090364042a244d604a40c0d100d507209014007804c00d802c602c6a90f08103091a00e0086032103a001c4e500092000441781c001c10040c0004404000c0564000c415131020341d102c44040c580010b281e1251201c03a041d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 466182194 1250 466180944 466180961
    0x11e02010b2707030507020d03090f0b1510030c02120304060f090f050d032903010e0111090a05090f1b210402090f0702030405131b020708070e241201 66
    0x3400c1021000b240001040268541c002e80030700f0200414141408003a50312220002c090f0300b01600d0b56500e9040001c032102c1c40113001e6000e425041e0074108085031083c4d45503074181060040301c0050b11250094803902801070351a409801916a194403010000a25800200241c034966100d8034240a0954280b050034171071402007030716032449402d6182181c01d01031146030407420542402202c2441d10340c400f004c192030918250380d10300d400700c02801113405001000e8460440354a0a8154118005150003c0000041c202c801e004c0440d221402c0000802c0180c80d503622948041c000501c040e210507045084844840003980c0c18032040b0222101e44404041031b00313600c110381c6000d02c021402c150000710f802021511030202285030140000390b480c01039110b41c43c411114420ba002c885800e41d4810000c0843c9885117070121403401038040c0d44c4105910035980907110f5104005121620980000d01030b10303030b803036495000a40341203262248002c020345c03c0d540400020082c2c5400c2c2424420801d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 466183444 1250 466182194 466182229
    0x150b0c011509150902090f190f09060e0703020702061611011d090604051f0b030702161404110f0a0c0b060a0501020a0f030c12030920011e02010b 64
    0x42a81003600c698203900d2540c0c1c040340d035250030f141e681d0740c4aa207a201810f05480c2c0c5048010b032246070401c0022011100b1a04d0b00f500070101031300384200103c006515100b680c580c80f0720a03000315555130a02d000c039100c520414042c4840c01c0081b60b45144a03400828006000800681c01e00403442c0366190080006981225014000304000c60035507002000700c055008801003800c0c00071080c2c404541041c000400d110312855840000030100010229590b2188511144250605443c0c00c0103000590040d80e00c40054880c2c008040510001a64644265110500c241e6443c208510074007010f00404800301c8155001031000601c0d40752180301400214048e41d4819420512504190441c0b181c00b03000707180a078480700006d010356600000c18064082e4080b180300200c0310b03181811280ea14590708020411a000544c1a06141d8540c00801030f45001d0242c507034402c0c0c0c106051500a00981c0100c2e4085808950040f605041407000c0600030410740c0008980d0300c0c80000003801d00c0302c034102e0303021 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 466184694 1250 466183444 466183451
    0x10605040806010f03080319060902210a2f07080d020a03060806010602070506030a02040905040318050d111216271a0607050a1a041a010303090603150b0c01 69
    0x407400c5020403009006100002a0829241c15038907900c0d4030f80300045c680c0e00440780258260030419040d034411f01c024402001c08549403c946500303400030101003070445009000b0f100c082092000c0920402c130348607103c45007040400c010050903540c40100c02c00d8218590b4420312007076000c544c1b03c4d0300405803046c440b4401070303444507420b02c09011141143c0142d4595404070300140221074000800d0b000303864040321200d480b40ea03036800c22000391140c0d80280306050f0508042c00304050f0441031144042e00c2140f00300b441107071218180030141c2000c28020b082c21140c0303046010300c2e090070b40d00201d5040810041d180c080404408001030b2201039445481e58240c041031000d042074030401c4400c0c2d01c50761040b060000030b00c0144502d130b000742107c503c1841454002084010030500700001941e40f9840880044400407241c05419000011282a99840c14510318054802c04502d8481d069a42c5a2241c030049420004214000c007143c2e17103010b024a0cd100f0f00450030b40390141c040d00a04070700c4030012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 466185944 1250 466184694 466184699
    0x12110414090f01090b0601050c0a060f0501030231020918010e06040c02190303022b020909090309010c06200403080711032e1e0506091303050301260601060504 70
    0xa10b821044600c00341d59034903052040e00000c240c40103a070b80103002480c203c0c1e151081c0e0200141081d40c10840240524503069858246d849907404c000d040740d008030b8000c0301a46115074821380301c2d0017a00440500c00e100c1048034119a055601501041302c0150521001502c480c0c0803d0010030280c00140c3c04211590800c041480c0c1390049900c1c0700d17810300c06000303207070244da2101000b0030103154001c05058000c01c2c3e1040c0c81c8800e115901000d4411030ba11111004815134a200a5000c0786200303018001c10400034aa0f400c00108990600c601a502c908407122152120740090401e1022001c030421070a101003451406c120160020354082c5040542c0c66000d458130020803003078100c1035402908004e109180100000140854401c0c1101010b2102500341e907942c0024100d41c420540103c0c840c0650802c0344005a1000d071180a09603015007050303c4000b034111050340141401000101c0c100300601c01180620350384180d15a6010140514035154048242486000d0700030000042004c60304 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 466187050 1106 466185944 466185961
    0x60a060f14061e0306010318230c04020c030c060f0106021009030302120103060b011713110303090904141203061f0905130614060c0712110414 63
    0x3419070610f100f140c0a5032981056460900080c41c1009010584011020181030aa0040d00403060110050601110300c0304144280300d0b98054282903107940e03281e42c0060318959980e039018545400c0100c82c904d207802001000564080d42d50401004040c0e00440e18580008880b0750128907068141019406032281016005541e843c0324000404c1c4142944046240c2c08241da4518070b18148000a01342030105481c140320310300a840e0442c00044801014000081024003905c5c01c09403010b0010b448544212004d0b0b5070034026402c00c1c000312006014081c1c000020188241c02c50500c07d022411751310102610341116440e484010707000500403400c500c024030004001014a01d05044c0180c0544410310400641100001d1031000340e14081007696000f120340c0006040c2c4903c0c1801c94580d1f074294907420b07a00c0740c0c0c40d90170114094569002d40342076820b0007168031303c0c00c0c00c11084 = true := by decide +kernel

theorem cover : BRFrame.Cov 466007194 466187050 := by
  have h0 := BRFrame.cov_init 466007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 466007194 ≤ n) (h2 : n < 466187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
