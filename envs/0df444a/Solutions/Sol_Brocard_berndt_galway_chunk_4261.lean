-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4261
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:02:35.885615+00:00
-- url     : https://prove2.me/submissions/e709ca29-a72e-4550-add0-08ade492cfc9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 766187050 ≤ n < 766366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 766188300 1250 766187050 766187053
    0xd06180f1b0e0c030907051903060e0111041a09030d0e01170c0a030b010225170d0f120e0601080f0c0105180105071e1208010905040c03121b0c08060106050c 69
    0xf10722610090b40066900c2581641611344150326800051a0780e20140800044001810310034018069240320728000601c0e504003c200085085480304070034040c500c25401a40e04002e80c00f901c0d0000201242e210041c01001d42e8210104200081c0101c041c11b44c8440c005200f4025800c030b0344001980031406814003500150030102e980004401a01d0590605811401b4402c030a0490074444048845592800030301c1c902c189041c01501c001e07075010300080c0700e40369215508a00f04540c0048010350743d031a040c43c1100510020b500315002905036040506180d1184000010f20f4400210764141e45544010550b5908107086004558901981010340070402d2545e0703000c40b59602030790040030983d02c00c010140800c010303080b4004080c843e240c0c2c00e580c135000f030b200c0f031019180d4080030850150019800801440c140350300c1e4031920503c1400001c10b002c00d079100c039901c024050801c1c00302c5400190703408170059120746408085590741d441207441610036940041120750252080c1c1c1c01a0500d0030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 766189550 1250 766188300 766188329
    0x5240109051210020f090312041206020d06030b091b03070f0e150d081e070f020409050712080d0b01020a0b040813090f0504050c1507020d06180f1b 65
    0x80800118902d01d1002e07812502c241000d400c014a254000751180c0c40360202c40035264403e010525040c0300c400040a02c00c484200010311050108800d55241e558021400507215400c8841e0007004048035080608210134580402803508030000c0e90fa000807030f0030031801d0000001c0d0000d141d520070f0a805a00e1081c1e071003000c14081d000690000a40c08241116002e203607000da80003094001c0701c0110b0594801070300156545a42d601075941607000010600b4541c500700b4592036140015110f00d400078423441c3c403003079100c0074448200522806803202d09802504c4030340724a0134a00d01d60041d6900030304582030200c276100302c1d0300110718210a26042002041e45580c0c0781d480003000e600000020518005d543d0022030300322050320031020f1b54680150300103110f041c2402d0007854880c210800c00d210780011529400750351400800c0d2240260706856244c100c500c81e250590242c040749441010305451041d01005001040c0c1c40c01a0711400340e85e94001c400f401c0054100d070507165000b1020119500c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 766190800 1250 766189550 766189559
    0xa060f050c161203090b040e07030c0207030510090215070308070525120806031c03020f041d0f09010c0c030c080c0105090601080c06090906010c0807060501080105240109 75
    0x203400520844501d181a10780d40d90701c0300840071040381541c02083c26418280c2600c8101604030403450017424401116600f0300b440c01150120002d00105110100341d21030102d249901c1c02002250090b40d48101034480014580b103c0030024078a416040e4031400307540344040080c030b40354401c443d02d0035090303615007031503959414050b59194002d419540c4904145601c0f941e0010200005078001842204140c62507909600010705408000c0c018500c00d41058000085071181080300c0d4040000701d040143c2c542c01201c0300a1603900460b44003c0b41d1090250101114200700407030207214501e8160f00e0501c545550040a00f00c2c0c8800c24900040b80040d13101001080c0100c2c87c141e20244544111460011380c841a9800d480d400c0e501700b90a5800385006001100d802e10a820a1070001d0312598100303003603100024180340c0040c00c4507052000c184180014082c1a00444504541000007030056582d600b540f64000c1c00100c0701400302c0c2e480b00551005a08078250082024a1305a441140c0f0a041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 766192050 1250 766190800 766190807
    0xe0c01080c090415081506042702010f0e0d050d0908070e0c030c070f0507060f1715010905100507170319360506130b0f04020f0a0803180a060f 63
    0x99074114905135030301e07000c0010168170402401500001c000e5402d141410464107110941303a294040d00b9a0208000d00b61800d203210740104c0d603101e5024640301c000703001c2c50402900e1050000001a40003a895110482400030008400c00303209019503407210150380d0b0700a0315031140c060303024105011081d540072030800320342013000d190130130400d84500b490b00d0400d5444030f40b41c0c0842c1400301c0700750300f120500304010f80e081502e85040c2c96143c1003260462002d0030002e16001b000801802c08040810084240e90b4403030a0311101030b080107848800007489c9280094016001844200c0f0010880da0078039490b507000c482541e02550051014180c0d80100c084c1d213601620808c041041c0c4240c109a032440880803c42c0b12040314401c103c08280140524185a070501c1e00040a4221140c00d003c1560000b0b19140200b50b400302102c0038101c40d0392a540b00040e611020401d4495000100000109481402000a01d0000e0598440581c20170000060064080443c85584086054a41c481010500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 766193300 1250 766192050 766192061
    0x109020d0204050a031b0b09010219050a0506090319030908090621100609120c060f050d1e05132001140403051f050f0112030507060f0e0c01080c0904 66
    0x441140c0942080d45650104400b010a0703401a03589124200944401c03442926602000d03020780d60515281014900010390365480f400c14900d41c41c0c0c010b41c41102400700030700c8080d12541e807050607241c403410040c002c9640d980010000d17140b0140003c0120020500906c228244035074090311407424480321201704402c0b5008421454000103c484110048492010640344207050043e9010803480c10071600070004500c94000702c80c0c0d6820b44815030003203030039402104201c80483c07030240d100e4901284d080300ca5000300300b1114040fa060203c030010500c654000060050810a000c11040d907030038081c003d104010050140140940902d0700210f080342c04c010030a03280040c180525000d11001e004807455105a00c26240c0e43c2102c130000c2c9003807030001300101c084050b002040c801410b01040214101c0b42c18460b1038040912603002e541007600420544244035000503040210035500e13401c2c40050400c41014580ea4022001080480d6018922407401400302800450902c1d400e441844014030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 766194550 1250 766193300 766193317
    0x100207080c010e0102040f050301020f2b020d0204030201111626120403051e0d03051b1201050108010902040e150301061203020c1906050a032c0a02090a02030906010902 74
    0xd020014191150000d01400d10800a0800016074403803900e1010205028203801c8984079034010006a0644602a000c0d26209850241008040c0500c544502600303001780381e00c01d00490000c589030843d4803150340a001180e0003a03c40c900914580c03901540c5410481031035655904004406000000c0c03203103080100030402180f1a217001c0212007166180100001001f915041c00040c140f0801030144585007c1304840e1202e5003160004054040d00c2c0c0fa926981d00d020596030b03100040c81c51a42c0b115108160042e00c0c02aa034076201d0000403120303400c0c03d00415011901e03041c000540e03c03a02d4400c071005c86148400c00041d58603100002d1310115400200e441d40b543d2204c1020650440001031091040e100b03400030144801c07680140000c81550380c0b0032030110384101e00200101600601100c43c0c0200c107103070010300c01c40d014052003085104c000e6a02c0b900740075118004c24640300014a0b5011a00807209500541d40349826403040c1c5c801251112210380151700100035046181d0041d14114 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 766195800 1250 766194550 766194563
    0x3171c0b01140c010905120910080601090506030a0e010b01080606090d152a0915030903140a020c041d0a140102041a0a031d071e050301020414190602100207 69
    0x9104980410982e802403d100421650340d4103039a41005400c011001028a803020502d04044505000a180d4003a0304884002e200f0324000280c0c0582c4603460f1103002c4c00c0004c0c4490744034140740b503030b0100815082c11280040d62816808141c198018180740d44103000083c20380e4a015a080140501910341d110216213424058045140c000c0340f9001f8201c40d04c1080c46180e025030310070204601d180d43d94802c08800c1c003900c01c13414414068a070754064500d2030103080c003160480f01458215800c040303a611148102c036020a0419406034081400c2c50106404c681c00d000f815000310640360650b034800e80d481c106038003039410300c0f0010b07030891030061038804044001818103a488200400c000369480180400c20400140c4403100398051045001c03101004003007800c035180c215040c0f603503001103004142c110b29400b85282003507068100d5001c09000040c00070f5407169541c0c28910b172551f0710100214840c0605020341c2e40303041194822030b012250660b00500d01040410b1610b802036118002c1907624 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 766197050 1250 766195800 766195817
    0x90a050408091020010504170309060103080c0313030510150e060111100501081606020604031416060e010203040303060e0f1b0c24150d14030c10050103171c0b01 71
    0x2034000c2e0302011134043c00304001013014649803501170202c001c11888103408503014020311841c4200080c07003d0660b5880401103540e4550403100b2451030007001c00c5000040301d240340101c00c110307001c1098a45410010400d2050b46103d40d066943e4a107a401440300d150100400580f0300c2d81b00300d000c1d55441c0103a00c16620385120300442c18094a100347c002c54590783c42411410f044001c0442c0318802000c0d148050311160034140d070003c041501c2c661040820703480100c0c040c007a41000d040152001396000c002017100090120303166020350004c590950110b4038080d40050689082170f0460301c15031180c44140a959140303419603600e1044241501e0000005121201031050104808210070054081c10180590300c920861000403004002c00d0524600e1051459107854031107080034425130060500c0c040d40401d044070b525501843c41074183c50702c036000b10b5001041035980154140d9002c2c54001a02c0c881c00240360407030b442001100040d01a081c8001e00d1800c0d8694403480b0701c2001407511454 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 766198300 1250 766197050 766197077
    0x11820010e060c060933071101090606090f0605100305070e060d0e0c12070b03180118140d05040e100510050c0f070303020a0b18070311090a0504080910 67
    0x880303401000c82c124003135101005110409208014686030302015105a02110014286001c000c0070700203502025003140c24049100b4501601040100900001c020414485981040809807209110322403000346030895004261107140211000d941c1d005d0004c0e200319065950840c005d200042c450401c0018074100003595070385103030040100b070a8180001c07800454403c1ca00d4103240c00161f1070761007048142c560100c0c60501040800440d281900a56200d54880d5102d0300b42ea2100003104109520304071200c5000e0b2009400c0350303031113401440c14002050640000c0b990311760b640104000414414042004102030701182d059200b50880381c1c000d40c2603900c00c0811400d02113114603034007049010502c20038528080101e002d00070b0510004191144c910784000c0e454482501c809810400c000d00018043e29200107000c01c41100c00003140c20f0b255503420320380e482e0314407107007d1486800a5004644044000c0c0103a030b0180d41c0000000d4a440940d4040281c0c107440752a10909100c540e05032102c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 766199550 1250 766198300 766198309
    0x3032e05060f0f1c05340c050a05010f090c09020304110409031101110a030f061208070309123012150e0411120d08070509010e06031305011820010e 65
    0x212004e09840443c2c103082808200304c0080b02c509088100c86103812101401c010222406038005095040100040d101424010300306038031000041c20175070824840e001480102c0c0d01c41841d60b40582141808991545240400c0c0c0c0b1043d107010307002c0070a0035802107541c41e142e801118824032a040060122205154003800d40705107100002103c0004140404090f4144c06201c0ea224904a001c0212605012180d0740c604d880c583d0260080c1000310348107082500852085002e002500c200450394451071900405600c1c44030035000007003400c0d410b013141c041007450741c058030000c690b214800702840d081e00c0c402c0107182d00160100600010800003440322043d0001c54000c40c0129070a581d4602e1220038071444110341e617501c07000c5503c40c1c0d07640341085502100326030f004035440c500035694545d0b1000403203001c0d12406000d60311810000910142d04203891900d0b0119101d50b00a0056004881c922400c44d1180200a440742c0060103055a0058081141c605070100c141884156120601d0224 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 766200800 1250 766199550 766199587
    0xa051009050108071b1a0109060e040f020103060e010b0730120f0212090d02161206090c0e060a140303042903070f1101052e050303032e05060f0f 64
    0x155103400000d48046c640c0c010217401e0b01c0c05050388038018482e1910b0604c4c411402e5400400141c248620b0410550440e8446d400c00c00042036002500e450302c0d41c480c1c01c081000d80c0441000c9541e404201c5011b00442007060052841c400d6844001e8600c9450803010f6407001611240c0c0d001b403d1369042c01d40c00ca01d04520152210360105101d24009161007218945480d070304200c2901954000101c0c411025603c0c6200810749484a010b0400e0321094031300307580036000540300245107201d45070000c42c0c901600e210440c450081240c0340321a0079940c80c440c0969501c1b4000d815010f402c200800c1c00f801c070320004084010b4130000c445c004071a650703605060580c2c02c01c3d0342460010300d45440c2000d20551280310075030b402c14000300801c4507040815400345c0c403a14030785400c800000b01c82d10020314014801d0300c03078006100240550340d41c0d00d01800300c000507008010842a003040d072050071403400401c06078a036081c0e820280034149010354904160000e504400c28a80900c0410400d48010380b0340c88200e03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 766202050 1250 766200800 766200803
    0x140403020d060e100903090b0c120c07050301141f0509130206120403080403090e010b03040f110409060e0d09080303040f0c08070b07110f01020c040e0a0b0c090a051009050108071b 79
    0x40c028a17500c1e000700701d480d00303034403500c2c03081c0c02070121009038040840d00b104104251080d0560350b2260b80c0d031044c00c00c0006c2d0300040d0b045d46011000b0103860f0192207001c1c400e030302d201e01041d044080081108242c01d03207401415000064200002d81040006202c4250f6600040c0a24242405100c0103820882c048500311300040400040c04105500110080042c04032440c5040c1d20b903052506280d02400020700c0900340d18501c45801c3d060008a9910780d100f50700141061042c9440b40c10240c024046040b9201500e01c142018803c0182c840c04004059400e110701a6166840300e4450122002a401068446565502c0d0002d044e03002041000300034100c40c030080303072a030720141010000c2c04c8040c60560b0154106e210000746a85c2c0c00715120f0202c0c60100c0f40003451200c0300b90001d19044012100405880c1041c05008454040401501500030202c2c0d9600300c1c0741d155414840f1a10818150402044208500340311540c010f01d1000c0e404000ea18003000c120007000c003840c0509018110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 766203300 1250 766202050 766202083
    0x10023409020f0d0c0c0b06063601110d21020912011e090b04020d0501021611040f1104091e11070203070f06090603020f040b0a0915140403020d060e 65
    0x3c055550002c0c2e030041c150500d05a043c0004000700c15150000c00020060100344101c2001800c980034203030760200c841c40000304112200240703044044240410003c03049460100f0b1030341031102c00d545400103180c00341c2607031690b84404100c3c420920410805030140c071510419002e00811600c0c3d12009560601110301d440041400b2802c00301c02d9880611150282c00c03c8c908202400c0d0110b400030210640080c0d055890400071030b080e0403e1402030203104040304540d40d40d2a12901405402601c0f0401032130111010449496100c050074201c409498a0b000e039000107000070801f900c2d481d8803411441002c2500805864022000ad2046951008002c180c4010100e070035803c2d41010070105028204d4003c26218003810a94041e0004003d403056004058000034842d0240d1044010303240127005040815448000030300024000d04110f010700701c4c03c4492120200c40d054840c1a0405034240208441c0c1d2801d400d503028400c28410401003500c85030303111800781e4541d100c1049280d040158094 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 766204550 1250 766203300 766203307
    0x4090204150905060307030822090606090e01091503080a0507020d0605040b240f030c0d1a0708040f08220e070201140402131d12040510023409020f 65
    0x201c50b48100c8030f02810707950003503020380001e10014598008030340c54909440e42c20241703c1d943c0c41e2040c3d0040e1140d005500924241032002a016030012040c800ba0b41c0c0305040e43d00b0503a04c5100500440b40811085040445401c40410100305102c0c01410048864a889803800c8040c0e008690f001c0e080361400c9070910b0b074034000c0000f1302c0405404290001c003411a1020460034481288000c85855030380c40e44035011b4680384681e0f5640401135501002c80142002c0400c5d00c150618521f07003075400300918240c4d02d004002502c4e1501c280881c0d8402c41c0c1c0700c000d660303084c111070300c5071551600807140760340007035002e10280301d000695100204c3c02003804280b00c0c045882d0242c03000742919041c81c2e108800d07075504000d1100603580c1e140e413030701c2c1129441c1d4009204c1d10801c00001003660325100b13000d00b6008158070300c1c621400309402001078580541d50103456100d52902241c0c0c604003840b8500030784000e095800400074141440b0707264896480c008122150312000c000b07080f680700d04c0700080f0300302e07000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 766205800 1250 766204550 766204559
    0x50906122404020913050a0f0f0506011106042f1f09080a0c0320060f040509060609060307080a110c060a0f05010e0a11070c06030c02061b0d0203060409020415 70
    0x14070720518251040d641981400c40f9880800c44002d80b2404120309181c60f03000047d4000400e030304c14a40a00c6180b820303c04d25440d0700001000f01000d59200c1d00241c1e0210340d1a29100d000101d29008036442050310f080301007046982040320310b2000a448203640c090603c10f46954401c1048003a15078000414903021850b00c1d4050a000101d90211890f500322040d603c01040b50707100c1e60011a900400c910707401c0c404034001c1c0c0d4080500750b50300c41d502050118041d0700c294290270140c01520415240d062031070b11650308205d400d00906079000c0d44544108002500903100d2124a5080b41c003d00d0040742104040c0541c0c000350301b08070700002c2554050b1040001849040c0070b80f0b03070951a0301c041003102d941060442d043c510801080c2c3c10f02e00391103201c41c0c0d800c2e800400c11501d4864000411540854035004001d000c1d101c4c160a4500500c516400318150000320303900080c0314095039039003516081003000c0800c081d400081415070701c640c0c0c03501d00c140982c031240210b48100c11036001c64020603041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 766207050 1250 766205800 766205851
    0x30212090610150212070c05041401080c01030b0d060b030a0503030c120a050705040b070516090f0b120706030e100203070e090106030b060301050f0d0c090b100314010605090612 78
    0x1c582c088614050243d4154030900e401207408140d04454000d0070380c0e207041c1420603443d0030170380b0350119400c103282c0003440701e0080104040300e040e02c1351401a11404101c4000450640709461000c1c1e0303002c0780d850000d00c005a244d60090814250203002ea8a0300740741501c9203410350700308482c001c00c8580c0000d002c00c900c004400f11140d028100550070011800c100100070b105000e54054281060f40006035031050100410540074141c5c01d294002c0c1489485c0c0c41c0b460301400d240d844151601d401c2056035801031920000340d0015101c0d100080100300c5c80c0c040c08402400071030304101d05078003501c2c01e03503460760020340001c5204150710740300c2d9910b480514040c08005041607000004040c40e00c00303031303440c0350b0368070b80440e41111000c980171000c10002d070000425000200c800101040b00c202c2c000030340407655400c80ba120010844110760101c0e84048213505a400341500c03250b07c0d0f81000014804580140080e00d49080003400c403d04040e4610301e814111001a101c014200c00326400c4024034810 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 766208300 1250 766207050 766207081
    0x9080a080318100e01020c0c0103090c0608370e01021e0f070501021306020c0901151d040212090105010b090901171c11120a020c09041104141b0c060406020a0302120906 74
    0x4080ca0200003a00041e107415132103510cd40130340c6040226003c0403c002d000c291210036191a00304807070b0a0304100d0851500d0107035001000d121032860418600b2501755806200b41d030130600841002240034a68041465050790242c45d41e07420120051002c0300109400b40b003e03044200300c04481d40c0105060100203441d00120f20090740c4226030b0b032001448130500c02640c07880741311707440d003007640461494410150500984404e0035410500c00b16200f00c44889500303c560250080304020031060f40c88070030250340c030304c00d0300c4915030061800e000401501006c03401082c0b0310700e1264241e9400f488001c00c15a00201c40403051b400180400780e100742c5e2400c091207051400314029850b54603080105002135282c109074440c040c82107400c40001001d10000c084400d45a140080042050315000140100071010507206600030004480105015416800844503941940c40003001e42d80e44030ba85000207944500483d0041680078055002a5004441860300a0714240007034141450a03075080d650692 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 766209550 1250 766208300 766208323
    0x903030b0a0e01050d11040902060d0510060f05071e0611040303080105010203271206010914130302122101121e0b060609010c05030f03010609080a080318100e01020c 73
    0x4a180010404c81c1e6840d8081c00b03141e0b5014000d40d0303851520700005401400016400380d006080010f80c0132640140d548050b1194032404010b12400391a060201e590071070741c00c1c4102c0819410440e0a0109110b80c403000004c81400c2101007084aa03541c481d01960445100201003200225091041640000070755001d06020b2008608005012282c983d0b1041e88602c60055100381840c0d84260751102d100400403140141d00312811940c0d5034201a00034200c51800e807161039481804625000044807110283e1030f0103900030056041480301642e0a6400f012040f04002c8e00b200d0705c045145600d02c8201d00070220801d0180d550003041c01c02d000c500e0703580c85282c20054a030010100000c0e00d849100c4d50807030b10540d0f18a803113080100050350034462441c4054502d00c0041024100303024200021410f035010341d074601c25410b075a0102c41c1c1c0c1d94071030140000c080d1030040c000221144a0441c03504160030901003210520010000c1010450300804083c078481d075000500b20312140810014120484c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 766210800 1250 766209550 766209569
    0x3110912070f1d150f040b041b0504080106052e09080a0b0f3402010f1406010f02120901180518042a090b040204080f0a053703020f010903030b0a 64
    0x1440b0b00e0740003c401c0c06190f140320b1b20075591307864402010f4450381d000c00654004101c20a43c110b40c1e400010700350390414031424142e503080280104550509006600b0980700c080080407906420400050040c00502a04410800f2503180002d1486017003002d01080c8d4010b0400c44038a0034444030002c0301d1070303000b440ca50014401200e80c0a5a0307403000c5940040c2d10708003000c641c1c46207030680128054221038910254080c20058240328171915400304038040c8909803a03240c044040c43c64140d0326040e0030002804d8130f0000740a80b0f01035501842903140d0a005000002c4c50301d070313150310000c1c00480481032a0180329000c5c000304810000da044490101c115185800f0030505111001d95050681ea0301580554689448440801d6102ca40655000c1c225090942d604810218280742c0d071345000400581c0d49100341849a032215501954010ba840703400b210031110722805050010400d188000c0440851103400d501048a0320203200301c104051207940d01141400426081040301c050641080100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 766212050 1250 766210800 766210831
    0x30309060c1d010e130e0f060901090b0a0504110a0b0c070605131404060b04320a0605030603210913060f030311010905030307170703110912070f1d 65
    0x207540d800c0018120040928281e115140070001041030855005c054500746810700c0130700940c101d408982ca5204e40003150031144140c3d20742e101c55080c3c4181020242484070f00d503003c81c500344010b8100d81d901c0741c001c02d200302071a1190004a50000899448035151000110b0440d4246c0024054480200310601d072442c00c261040101d5030051034103220b09880c400c40000403840a4895411a1004020b01c1c0e03403942c0c41d00c0e500d9210120000c0c0c080c0b030007035640344070b004440c1c14840500058010141d01408003284941840e4064440342c0c4054052640351082110309800c81c03001c50030301402240c850900c0e1341c58040307120601045809004604800b135040407014010f02108800d10401c0780d80502d800e000760880c090302980180a02800a030090000008010b6550303000b9400d101da0307261030781701c403001c030380d40c1c1c00b4211b040b125000d0580d0b00076030041080003243e103003195551100704069802d5968143e0741da061007122140c682d01c1014501c0301039112044001c96101390561140300000c0c401e50 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 766213300 1250 766212050 766212077
    0x812090703150b0406050a09020901021e0703030e06070c14010e0105070510050714070b1b0c0a02060d0b12060f091f020706020918040b06241e07030309060c 69
    0x50892808a1124603141d9842c0740b0606540c458000c1782c01018081c106510503921407108002075400300340403d0140c07052114803174010301013110030b410803400c4401504015040d81c2d0304075400210758800c10307807082050242e4400700c1c1140c044d200050041e2030400e1040c5041000140c161001120100e041c0174061040f40040703040402d00c428940082e180c00146551548000d64bc0558003001300110b040740825500c0810030659580c60148002803500c000100c1520040803003482010342c46401c0303400085c0c0c01001030810b5800b1780700c00002e1a03000305207138000c034000c01d5a010141d9900e95559000d1000e20149240f600d8a5681190a40010740b03c2c0b2002d2004000c0c42c0d01a0031801400301c1e9000420b2001d21038140c1c181c80d401140140791070b4480a0000300020740300d034181c405498204916012442d103140ca042c501103c02d0079414034200043c440700030501d40c0c3d0049000c001c080c152600d06003050b00e038040018010140b080c3c6000404c040e8504212044460407541007040c45400403600d071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 766214550 1250 766213300 766213313
    0x5210f0d020312091c080a1805191e210809060f130c080a02010306080318010507050a08160b010504110301090e010f1107060e0604020609100c050a0812090703 70
    0xf40d0104000e040f2101c0780d1142940c2d5803800ba11178210400205201441c010b0f0309502a64150040c40c401c0c2e0144101d28a59503285048c22010710300414a40c040042c01c02200ca84403104c0c20098000c0b69840300383d555075032252840b0b41039440300f292802c40840010044018030300c01800405850701e0000c24510706500798503654417024140458071510240006c0b0003810800542c4851035114140e480360b0355899140ca941e0b040c0301c000c105c0c0440d04000c0e010440c84000000d48444d4003041d1140104c16080200549496100035030030f54103400b03491402004902c080000b0200a00d5105100c1140c01081c28041450700c01a00310510503418145a5030700041404241da0544400301c8002038808003c01142d0f00601900e140711404c54200840b1034141340500c000780c41c13101d014100502c640744000f4085a214001190002d42c094000e100e551041d051002071800c50303810a0a0510742c1588a84441c2d1a14500c801c08844103c00051030300c00b401210380f8000d4021044400501580f402d603541c80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 766215800 1250 766214550 766214557
    0x6130c030f15061409060f03150301020409050411030609061b070507060c170c070e0a2306030709110a0509010c0605012408060906061615020310050625020a05210f0d0203 75
    0x407807000034080003262141d820030216620270703036001b0000c640c2c0d00c2e130300c1051a0140034202e40560302c3c020008810281030402203881440bd031004005080307540c0c0e071009046114803941e1000c51281809001680008078200040d10141c002074540711100240d52421b01961100c0d4580c0019400302481a081d40c5080080c00c0f800380c0350100090585c66441002075402885190b0380412007002414114412020003414280901001d40542c1c6c075550b21014903006568035404802c0e42c840c0304001c1301d04e06030300c100c005e0300448a05140c00b90030b0700210f0b200c0b0705c02d0314020303005800542010b035520031000c5c80c5503070146401c16840c10030450300d00c1d21200140310138000900e01805090006480007450b145a4025a10150300554440420300d40711001d50080d04103d900b1109007050ba400441d480c40c0c690147c99a20185900c00e0b028406620a48000580030100803078128285c944041903d030750b2003002c484041c2c1032140010052543c1510b562600480e48220240d98000c40440440d141e0b010085 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 766217050 1250 766215800 766215817
    0x3020c0108060103090506070305010e0603010e0a080d02040b030c0c010606080930040e060a0e0c0f0c01111c0507080c070b100b030f0f010e06130c030f1506140906 72
    0x200c80e4035a0b941e00160003800d48524020300b02c1c000c4a08011605e80c040c0e00441c10b07110000e107422441d944d032500307050032103200c0d103018006c551007854550000f074514002020305200352000541011f0744e070b404404582e081942c81d202c0c04000030070b520420100910680c0001c10071890200120304080c0b0581e901d4110018000032100b40304000c1c3d07404913041c6000d44290191710b540e4a0b0b912030351000c4612800d10188c8a01e031148002100c002106614000b000340645600c41c1d1940c070b015161054083c0c5a40058194540c65403952411325030004810058620035004403448050600c1d00c0c110b000855030020000002e05c5a584d040c0311182c101d00f070985150320303030100076000640c4407040008180d6500d540514803803a80001046680d41c10440e4082c012210341480a04a03601e495880c90035810446840d50084000e5151801400054014a141c00510708002601415003600441900e080750905c0f1070b0109500d030301300718141e80240340b0f00f62a01800da0103814150f03003200003181403050400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 766218300 1250 766217050 766217057
    0x6031101050c0106050307080d14071a0a060e041a0a060f05040f0b040204030f050d021c030c03090209010e15040515060c03040b04030b041104021602040e03040f240c03020c01 77
    0x4152400c030304254411400340400401f25100140c1d41c0701d00c40d94646107200c4240000b40748440d8043c5a20b1500c0070303200102d03801400c140d0640c9603500050302d42d000040500c10100e03203d00000942c01e015545483c082d500458020758007140c0003000b01c50062018245e0b040f190319042c000c011310890440b5403003c1e142c00b101e01280100b10241040c0251180d02c40351603020348000f400004000a007a50406050f101e00103441f90071030041401da0b19488111300a0500e0500e440300e02408510039440ba02803552681000900c0c404560045601200c00340c211450b0a0012410b004014021000505922904450900c045e1500c1d00382501142a91405075008180c0851500c1810320701740182e502800c445c42c007141c2c89039075038140801000419a41540d10450983c0681c095040070700031125000410010308081c2c101c95400d010041c040100c1511403800305008c08180c2e015000b02181c010507162101100141805518151480302e460280c4188405500340100080d000700f0081c90311102400d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 766219550 1250 766218300 766218307
    0x30803130501050a32070e0d1a07022109040504030215040c030303110f07110301020d0e0f0c0105042405040f0e151210020304140f1b040603110105 65
    0x103100c038860691114001c0040d401c0008008107a106035008a20001400c1320311801d03200da95000d44022009440010003844484000550b000e010300040302c00384038050140f049108060710707100700442040032488503460000e1f06109100d58100544008009078a076202d00541448070111071501c21151890302843d150300000741858020720498070341722072805501e4000d02d013034908003148191501046010a00c0c00040c2001d080341c450079505040070201c1000d103405081d40f55800c910300101c160a5066400304100e4089600ea402199504d2909100030556614000712080c20054503804550420206000c00c214441c03030b0701e000314040710318100c214000c450044011107161083e50400201c02c030010304001419800403895a21074140086807408210115080004039140301e107070340d500c9502c1030500852000d0b103035005580052003042d800324040701d0b0407407641c1464208101c00c103443d0421046c11310541c51b002c60801e03110000312010003c290440d51814107003030603504028100034010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 766220800 1250 766219550 766219561
    0xa05060310031b080607050a2304090b0a1512201c06050d03050703030f0606091806030f06090b0a0504030f1b0b101a09030a0201080403170705030103030807050304020a030803 77
    0x2070891070113804140203407040c41c6041d600152807640208a03140004a660700851701982c41d03601800d2a80300000a03003860103250561950181c645201115408141440005400b4010104401500d0059260008203504c140b402c1c0c403c4900030480c900b4000403000c15a234074501c0740300845960100d4016852055115109a0001406140c02558200301607101d164103058221001d410058480d50341801102c105540307500c16159544a0400410b40e0f00c0000d0000c1540e1846400d007640d115280000c40d2603580d21445c41c3c010759250180c1d0715607541c5e400300c424031219480c00c2e0350011101009100c18241035800030100501c0c95200310030003034802c581c4c086a03812003088460058004203010550f0a19400707400c08082140318070044108600c07030b03454402120b481651585200203003d442c0c0302d50981c0040da0400b0006008808011300400e0340c00b242403001800707a00490140e910562a907040d071038058020440a0079840602000740304200c016594003855030190b03584074021544a4480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 766222050 1250 766220800 766220843
    0x506031506030c01350f2410020c040f0c09080706050f090f0d031812150b010c050f030a0e040603330903110d05030103150506030a140604020a0506031003 68
    0x482c035800e174280e212412142c1d890b50050f41d024031111100424140c4440341401011040e040540d954054400c0409400d4a40320810148a01d01401070728503030440c02c40020119120310400312034095840e84020449603101d10a0b00140484c040280042070070400c01420368011200311050800000469800c1c1d910307111081c115052000c0d20325280044140b4016107000300e55009961003035031070000058055181c45c100445203400121111501c000a0b000c40c01801c40801000e06221070f030052800054020040802451030b404007075510f507001c00b64010420a0407030350b0544528142030091020441c81510300c0360424240e60503035613907001e03c0e01d551001e0000c203d20160041c80c02d00d40c5400d25402017800e0681042c03000507034441d000c510006541d0381c0801e0102900300c4902c0e29500940c0300f81a13003c2c41e04401d000381181d00c1d1042603034500e0b41100e806091081d031504668240021800c0c0090510301400c0125585400e5280020703103203003100c0242c0b0015100308a000c4244049441 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 766223300 1250 766222050 766222097
    0x605100c0501150501120b22050412050306010c111801150206090102041a09030106260c1c03080405070915050f040b1c020d061103190b03120901110708010506031506030c01 76
    0x103400c4101885c0000e812480002740800c03102561184224800d0070312103446a0200d078440d480503169407200300381076143e01a414224020854012000e80f03040020b481d09400154028950400200802c15038100c009003804409002d035512a070040c00288449120030410340c9140240e200c54540300e803003480029014121f17030781c00140032254008000514140300785181c9282c00b0000700301c8858080040600204255450380f0384103403810140400c001a11901801f0381282c0240201c6070002c0d00d480c041402c80348890200e20b10035400b28030400407030406220021040310201da04102c21134030900418105480822490b6041080007049070071947d501000c00d0313816400c0b107410810703204110b00c01c890790f51007030320b4209080006002040720b40c8054001c20000d6074028026061140e06c1660b00415608180034450601491a0a41e0000700b0f041000b480100880c40c00400d41341051000d0505100301c03201800000303030168082002a4600240e881c04100082c40c1110030320b401e0300c02c1807a41c400e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 766224550 1250 766223300 766223329
    0x1b060112021e090c040609050109120f08190c141c12091401140c210714030406140603151305010605060d050a110702090a0905010605100c0501150501120b 68
    0xc20f881c060041d030a015802500940344581c8851064035180c0006558072403662103285410624815201e001901501c810082c652040812a0070f0103400d14410181c202d1501814000901b00604d00c0c043c040c6414426481c81e14481c0900300e4032041c40c00c1ca080903082040f00d0001e00200340c410003071014142e8442c012064011015807034030201a807030300d8081d24115041900700e07034100300419000500441110500d0311103014540804015490602800d10014103000502881418a0700d450840c2e00040d44075521030000055000c50705c1903190004000500007a02907881070103a0150b800c680342c0c46a4011003594421a6206000e00d41a4054400ea80000740c0006d00440c50385800980e03604220b01500041106015014181d01100280c1c000c00d01d000e540b11030400042001d2180c181c0c030550034030b8010800454450f8991020943c0d01a00c0591800080c0302000c450080c05000c0c8512420a0544a0041006031a000000384446409580a00040c0d0340701040036290750b80320310404542 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 766225800 1250 766224550 766224559
    0x2010f090803040902120703060518100e0405031201091803030b0a030606060f080108162612070501050901060e0402100329040e0f19050a080304081b060112021e 71
    0x3c540b1000c021020350820300315a40040403400109980070300a001c0d10040d518082d11980461400e0400b46a0159014000c003100110341000410070555101d90144031328041c00040d1f07945c0307055074103900282c1c005070700140c03e0b1498502e5034001c0c4074000b4401d40c00590585804109004c007840000d40581d0503500090100d842d10600007240f80e04158022403445103a20740d22002d0b030342c0e83d024039285c0007489190082c00007081028040203200f62070240c50985030402c00b0b0f205024202e04d19181810300300000c1c442e4074000c10807004122090294942c0844401c0090100030703d882c800040700d950240009205040c0d401602e11a42c4c426846002c0000d0541f05800c0c20401c6e5a04100183c2c441c3c048160040c0c0c18440060311450001407624403540f03444004184440c108501075080441460040310305000d00b25118001c41e1700b480c0034500139409900c26640d00c0c0d16000d01060035804080308034400e608400c004000c040203c4010398609070701a80c5241c807080c02034501001e1900000900c1d03520 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 766227050 1250 766225800 766225807
    0x2010905040e0715090617040c090f1508010b03010b0d05060c0c0f06010914160f0509150c0d180b0426061e090c0a180b06030708040b0106030605060702010f090803 72
    0x440b540042528122143e946501079000c011603c0da00412031f04031405850200e6810003044400810b41c400140420318410000e016200352850450000b006e60001105a44420b0484158076081c0302d41540e4640488988210520320b94a880e00d5141c018030080c0603c4000c0343c40200301c1000e0205c1080030f940041030f203402c0d40c0c49202c1c140003010b016441d0180c0380000400a10780029080c0040314506030794690b822407400c2580102c4290740100c901d070303403c00540e00001030140007490103003c199100031b0180005128642d0014000e00a243c16019103c552036030807c9044103040886050342d20580d2140110b5480311143c0c65845150070f80c11149109000800c4140551200e0083c0001c03640042e4a0240d280e14003056a10003c05480350381c014610300301046084222480c11041030a041d50101d04414074600061203a082200c0000118416200300070403c03d1150009000d00001c0c02d0401a40d810480810a1805140c030020705100b102d5888a590501880c1c800c0010020380342120364 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 766228300 1250 766227050 766227089
    0x516140d051504050601140126060a090e0303160e010906030c030b0909100506011d09061f02060a14040b0a0902120706031a09010506190e09040f0302060f0402010905040e07 76
    0x251044248180c002da81491600c0d41803540c8901a0b588176508198100d4810486114500603849c00161440740e10045038800000d0f142c81e42c1c02080c1c42541504007444d100d16049101c410400a000148002c0202105806071184e8004489400780c940c1450300280a01400a00b03600401c0c10792000c40e80321101c0301c100a81200001460412030650020034080e649484005541da40180c1200480c2054041008003d5080120b05103030302503002008201e8202d03204c14400040c8d0884040d21005030424400c00800341d0440c043d0200100900840c0a01440c003511a140491001b81100c1c1805440b01c4541040d50740d0342003140c24547d1900e054840039030303035003070003030010a000e02c07007403403504001c90500c0c5892074500b020034122a8007802042c600940c0100c50003440051034074900c203020820b14008441c0d01c4800c2c08600c51842400d0140c42d0000394100a40341c00001000e02803440703001c03400c000050341c1c09542c40c3e04440c0700b900c021544144501004c1d007002c415800c80701348081400c030640c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 766229550 1250 766228300 766228303
    0xc07170a0e04061a16080d1413111c02030706021018120e030f01090c0906080105091f0603170909100e041e0813030516140d05150405 59
    0x445041a4a9181c8000700c030006000c140d40203841604094001860401c0f403007003800f40105404075801d002032403a52010366803a00241c1003824910100f680e40c44519400320020701680741c00c80c1c03c80310425075103c1c0c0c40d500d103044010500186030160000c80b40c0c080910131a44506c0c650554001c06581c00ca0b5201d01d0025910b8a03a050310b000401d080c01055141c00c9030f2442c5501c5031075004100341540c499200000da5291075211006905441072038000e100403a000c0c0314080c0c1461062880c184018074010300d46040d00d8240c1c01494050349040c081c85034003200003901032020011003440040796013401c0020346c014159580b01505c1d44006105040103d40648001c0c0600001100c10104c0e9071501d0b80107a6503111140503080c0b50701e0f104404100406c08280d45040c01e0381a450754802c102c003003030b568041650800542c0004100b610340082c82000310910241c01081e210906111503030b480e00c10305003131050300c00c0304050240d0200c0407100d0a200050050700d0700c16241d910f103a0381a06040c503046 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 766230800 1250 766229550 766229557
    0x50c01030507050a0c02100c051005060102100b031504020105040f0602070306060f051e04110409090302070522020f0c070305030c0106082a01020708190203010509240c0717 76
    0x6000a2030400082c4200d402001900d00b4900c3c2ca56484c00702000300c4c1e09000b042d0205810010a11400e0b200440001d103042001d01d0422015841c003103880d080c0080061300d801480a0051825070800240c0b8485440005003503072002403100144000b500c2e20700040c0c880303101e5500314210710141c0c00d201040746a00090307000c080324130450003085001e41c0e4883c0c030708035a841c0b401125480720345945a1803515545801e0422408002080043c901e0b840c14440d58980d0b20650001892a86401104090640511103034004100c159010081c3c0306640b44601145d60321107249250095001c1120003586000e20169101340c40150115240d068907810400e40d640c000000094456007005000f1910083c0800c41855113808400d10f6052000400b040c3d2a483c2d41d001600d6046103d2a01c000a03113800c200850000d0300c10040600259070410f00505003514801000b844a6a1042d054501c04504140d00e9007280885140c00211503115a04580124400c01c403020b0f050f40342401c0b8450400c45500002c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 766232050 1250 766230800 766230823
    0xc08030106091d09071502120a20010615030f020403060624090e190b090c1801091202010804030c08070605071b1106090d080304081206012d0507080705 67
    0x105680d0420704a4262100f240480790030741c440e04010010042d6540c1840b42c0c560203000d50041e00c02840c8900000041900b21010300c02c0000d50769510401c4c2c0c0a02d0300c55035104954040c00038401103050099400c084a4000301d03100425540e1607941c42c21860039415640034541c080c0040c0526556800c140103200c02020001f480d500e9603000000c51640168921000c8940000c50040c16503a43e00076004c9008074444100a010f44a01c0c0d58840b40d03680501c510310406024440c42e88489141010380500180c0c1c01100381480407102c024400d403041101e0b07000c1c1903582482c009015962758501100e40036a5030700000c01c0013802080c0e040800c003043c3c0000340f0602c403594400c0707404040041680b20b0307140c00780005001811038412503030702c40c01c00c400200380e40300014240840304e00d000e6030703258156801160140d606030b80106407541c0c5000401c890301d400800918124098584d94400200c03c258003003901c1041c0c00d01c10640802c1e150140e0240c54440760401d0340c4584448150a11689501c03440e03a6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 766233300 1250 766232050 766232069
    0xb030d0c02281d0c0403050c060702060d0f0603060b0301020a0c0b0c190f170c070b0721021e28020a020402030708060406060237080c0f15010e160c0803010609 70
    0x3042d030138482c4285c50481c1e801400a00d107003d9070304248403183e84190000d98001c0340401803c0f4000b0b406000c0c444000c0000030300000c1c0680783d03003010000c072142c81860344d00c2039004004680c6580d6100c1d644a1341c40d50003d204c2840e40d1607400d0300c9441031180c8000e64031859030b02800340d5045604000e1100c006502501c3d4000b040c080c0204004c0050004c5501c1c0c04100c41c01c5c480440441c00c00b602d000d0b0f011000e0706041c0d007107014010341c200040c2d050b241c0490050380c00040c556422403c0c042c002c0c02090130f01e00e8507030406280b29040e0026110a440418200b030076080340e5211540308201d407005854015008554a041500e0000d0081c6001c858480c001c1c3d0420b0700004080e032000800003003480c00c2d190040510b003a041c07004041d000890005c1c020840001a002010800c000c0081001243d5240101150200d2520b16030510603d20042d081502d025001000002c40d10360003e580041402142c500300760800c0401c2d02d0340c5202c0b50015020705408000400c1c1c65400400000650b11240d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 766234550 1250 766233300 766233359
    0x5030106121b051c020f3006060a03030507060b131409061b09180901060f14010c08090103021b031c1517070312030209040b030d0c0228 60
    0x42c40741600160a128090700300c4141c3c6200f1041d05a10814142010300c020041400c94204c540068040120607000c000858401424800d81c040c0640a218107030260030040d00b01c9182240025009010502c005014420b001a0020410020350302400c480c81c0c0040c0010214408a40c0c3c0344001d0a614540990340c01d00d0b0004074442000003d8040d1017010a12140412801c0718050110b080c5c102410564205d4440403004d420800701540e0380344140d00c10000040c00301d242c00c40b5001c107070354035611004180c01900d010700c0099a2160703071030346101d41207101c5607981e04044004038001e100e08429011050b8180c5502c000f0540088000c02c5980d002040440303142040340a0041183c0c2c1c94072a060f08014419010000c0d42703d20700030801d00707074107a6080d50b400c5907807502c2b45040c00007407406605c002640040c103000036203083d20480e02c400605400400030b9860101015100b080c90b1706010b4860620b150608110004070340084400c40c03080d4203d042e105596900e82e0031100c5540781e51310149000c64 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 766235800 1250 766234550 766234583
    0x30804060201091716060b1203030c07121706060f0421031206060806120708060c190e01020a03030b04110a091d04080d0f0f020711010f0201020310050111070503010612 74
    0x2801a00d41e240c0384c80f0502070841809035035590003400c1e04148a038016400ea559072036408ca003480914480c2c1044000c5580c0c45056240400708450484070840a01c003440054055032894001d0541c1d202005a585a6036411000d4034040c09001d180d05c0140300c28000d141002c888045240e02c1c1d481c1c84c0c82030b1900c216854080c01400142d035200d0140c100000c050200007680e9140c13502540300d080c100642916031258507100303451f0030300070100c5006440080014242029881510404d2140342e941e00e0034644094642000035219460520007504040d01c841d655070860741d85030f001481e10084d21181503510342c80200003400c042d8407842030010402040e5110388c2c0c1d0341c1d50310000301e1103140c2c01100c0c949800719280c500d41c000d00c00c0c00b016809a82e6190740480c40c1034030920045c00007034041d08200882c61440800102001c2c3c800054004590061042c403140400d00c5c511581561400d0a040d200007100e008010300c2c16200303602841c1d05609041c80000ca000380c80a404610500420b00c050100300c0c0c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 766237050 1250 766235800 766235843
    0x1202030115031d01090b0f0a061805090115180b0d021807020a0c0b091e030c010e06070b0106031b110624030610150804200a03080406020109 62
    0xd1151410742101071400030301e890701c41d600a02c0c46103032a9001c80071807039801d080e05084482d0343e01d003141c140c40c444c030a03c00c0004002468070b030300001a00c0103008003410482c443c41c40703d0b03001c28806480350322180824203010003900700021310310800301e00c044025520848100d2428104241241c090710340301c0c00d04950300381074914119454001c0e00d00c007016001e41300c84140c0448001c00d41c000b1800b500d014100020401c2400030000e044002c0256100d1030b449081102054021804842a6084601740d03030450301c02140303104100d8400d00709541f06e10045008641c3d54407411000134101c0079240004107415400d640030000e999010b41002004542d0860150783c60b4401c0780a0444a0b40000c0000341c403080c02890326040310304032074901c0e811500c2c4000403038602401a0303000202da604000f0140719494446a00c24404149440e00f4020b0b81840c0c0c03038a410311206580c0080c24090f0000040b800d0b074480c01c1d66000210350107803155a84a40e1202e0081c000d01703458904480000410003045290560f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 766238300 1250 766237050 766237057
    0x16051504110120030a0c05071703040e0c030618100506071506080a0309090203070c020d0b090115030c09050a0e0a060903020d090303080a050615040902040f0b0a080f0c040f030807031202 82
    0x6a400044d407409405041c10359440c2d07402c9004660520841c8030100e9045900f84506070030126840c02140c07a91304142140410001c028420000d4035003d1041202c10b1b91400c022a580d040d9000c0400d029488041c0211200d800a8102940080e4006070b11020090350391500c0901c0045414200910358441c8140d98441c4090180a400241030300002c0c44000c156900860b00440c0d0390401e980b64002c20b81c040350306441e030b00101784c0e03c2080506c10824005020301910700c0d550191082c56615074110303640d142d03691044d8004d0100040c1d4030740001c2c55080160348200c800f0581e1404692102806140c00005046c0c500c0b800c400600602e540304000c140070b40403100c15254140c681c5104d40d516000c10200070a00200510382c1711303203210050032890007080c000380302410540c4400740c2c0da10300f01010300700b00a807254442c5018620230032100c4a4203500004403a0801d0000001c1784840e182c40201100600441d00481d403840a05e01000041028007001401070038440e0700e0b0341071101c880301c013000304900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 766239550 1250 766238300 766238357
    0xe090a02060a0e041407020a20010c0618060905030304051002191b060c02030903070b120f0c040504020f0d050702010b1e04140a060f090e03160515041101 68
    0x400c01d0204003941d074010f0050f90001d00000c2c000084000000701030341c010003c10b886c8035002d6007202d002c20301480800b02c01041c04014605407041c4070107601e00020481c040310302c0c1c09000d203641d800c00030303035065408083c0d90780840d0070000900040c0c0c9681002034803a442078400321074a10070030760704d403c0180450003031303861001801609200100c4800425100003070841d45040d400400016440e0014038544150000c00308560300550321a49800c00f41803030440960007100c2640700c180405042605031790401d130362061144102142c2c6840e0384140d1004d0740035039082154804d001003445140e075910780025200d405080001841541c40c0d610050b0708030344083c400140c12511015050f0540c480408030f90201507000b40c800200d068007441100c1c0070220641340710180300c0d141c1e0400c000807920b81c203d2a0260616400030840380c0e0541001071b0340e034840c003028581e54581500c1030000380320713084c06807044007400109002564601441c0000001044912140c0442c04002c5510020b0000c0388044c051031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 766240800 1250 766239550 766239559
    0x13020906040903020f1f060803040812131508040b060906030c01080c1605070303090501021501060f14130f080a0302100f0b03070815071b150615090e090a02 69
    0xd44a640a00c0050300094000f502548250742007444003000400010030540d06000140c90700f0141c42c044c41c01515590f40c4050321580c401d00040c05406800b00311030b04810041c40c40640d454480d0303040d400e8102c941e0381c4008000380c13089651007002c5400c00542407040f40700e41d44020955441d2010081540429280c00d074141d0300c18441c042d10365000f1000143c001c084c00c0e43e05c40c1003010015104211151000b0122041d8011000400805801480d42405071000340040e1035004c0c41c01a00c46000907051080000b0031465842400646002d041c00f4041007181010160b43c07400700070b201c0444e2817074038441c40b14200800300000444d140041034050040741d166019101c054010400d645c041c0c003094001c405440d03a0396000440ba07a90401c0b010008100d0b80f0040c0c20184001d042240c00301c200144844180441452071030b04540c1c80115141032a9844144501c0043c4a92400070040800c2e402400c00b88550458101c2141c0e0050044401c0ba00300209019440d91052001500c4038a03c402c001d402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 766242050 1250 766240800 766240819
    0x7081606110307030e13020705012c250504050408090f01050a2c180f1e0c1c020406110c030a0f03120b100507020f09091903050c060405151302 63
    0x41d1080c81714100e035810040850a4090310115190226807000000300c0700c80e951910001c940607074002c3da04004040c00034030030b0710001c2000c03030082d2260101107124031030400d11012040161100750b850380181c40058000c11035494140340040d030a5000c1aa507901c00e4080c10f641d17500540c4242c044500240513980c44a020b5121f030503290000301902c0c144c2c0740c860507032010010f48075101d4160224001c010703c011040c06081400d5001140040500b0317104d140141080b120b2000800c2d261003541014011290700e03030320104401000301d402c0f000c00340c0c1d401c07c6000080c001072455104172105915007181c400d803010400c0c0d21003055a0f135016000000c00b000c645100181c0806d000e01c4680c0012140607402140780c4440c000002d444004803491500443e48c0031a14000350704080d44000c003488030035603081c5810300308030103e107940c0e4401c419100500354208101c1420907108005480d050307840001143d042d4103140ca40b4036120300c101c04030240b00b1902c0c1400251100e030015407401c0e105070041c282411 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 766243300 1250 766242050 766242053
    0x506040b09040f020d05061905060f0c0a061406010e01051c020a0915050a03061502060c1617121605160c180902040b061e090109050307081606110307 66
    0x106810190301650b21036a50f2040c1c9510420900040c80d014003030581c00502403030311004001d040a0b604403800c80400c03210b90f043c00291620400c984a00b1400c1c0915602e03540c900c2807482c03400d448100300401990074003420140070300035003542c0c900602d4242c860b2080c01c11114011641402400d5054032103802007054444841c840c4e500400140c00c040c40c007401c4c034030b4492480c0227401010709005c000007100010881d01e8241d0611070200076101c1820301d020441c2e0306410083d40ca960180c140c40750b40c000000d1110410200540e45a0040d43c8a0f41d8045002110800e550f0076402c24403605910f810a1000078500c986958050034950030142c960506008681000c600c4200f10800c0481e400039000320003261000c9113240100316600d3302c203000320328640341e4814401504d08801d43c10b40601d80502c841030010a011000c00041c080500d166912000c0a00c01240d078038031a98002e0f50503004010011541e0000425043c048904070204c03003c6d0141d85001c11210002c4045100009805c01e000300c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 766244550 1250 766243300 766243319
    0x31e07090c050c03040806010807090603020612071b0602030105040507081312020313080c030f010605030c06030a0209090115020d0207030803010b1c020f070c050f060f03040314030403030e011401050604 89
    0x614801e81d15149042220411425295501c00c0e0810000c55120a00412200c0c1041100001610000c901480003c0c83d40d408282c01d8001e0211100c0062402400940035602c150b1504009500c01061181d00001c42d0a0480c001c0d0302c280140b90040e81410005080203020780d001038044c880b5020030416401ca0b03600d0391030b09041c142d44408114001004041410f10030242500040c203910805080303030803615410980703000c07603500200e0300690524404000554011444041c10300d0b00741e4041c0d0342ca0b6901c0403404000d02c6414006c50f400000d07074001003140c2c07a407150b0300fa409018503021140240340010060b0ba5900c0188002044140200014085034980304e000d0425111010791480d00c42194207880f1040c0d0700544e0340540c900402241040501041c2c0010340000d0406039a480d03206900c40c00890102d11902140704c1003000c0c00400324003010b01c10003000d0401c2d100191480c1d124203081c90000c01070507800410a8041d030800445aa405020010141c102d840040000389000c0c035250b01803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 766245800 1250 766244550 766244561
    0x209010e010b1b0a022e02070810180f080901081302060304020103020a020a05010c050919080601090b120a03030f05010503010e100b0102150f0a060b1e2505070302031e0709 76
    0x81c0418007401011307100580760850030080c0d540321000001071089645400800d0402c07400b50f140115400000c00b0090100701042081c00c0c50a406404158201c0002215145015400d4000c01c600210342002080c800500c0c0034201104007640c0700301542d100d8285800a0049000c0013070b60150040012800541c000d5000b450360016038010358200d400c40743c40c0c0c0c40c00c4804440c00d450100f40c0c001030094051070b10440c500c100c240003510401c4d55034204110255581014001e0b10411a510401c1080b141c1e116500460038503025011206803050919009010b00b000075100218141040000b09403460180607082080380202d00800741d02081032128000350440f05000e0341035005a0780c4000389841b410104074401c1c00368035001c85c0c0a080a50f1a102180c1c10741d1700c030301d21060041c0f002880105029a2609218000d05046c079100c1c551040e00800816202c1200c1c4400695041a282003150101d00d00c0c080340c3c0214141e98600003c4000001c5c44c00441c00641416000100203100f140c4007a07001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 766247050 1250 766245800 766245847
    0x2d110f030a08011509050f0d0602070507080c0105041a0703030908220f1d040c0503030f090307080c010c080703120f0b010314101e0803070c1502030f0a08060d0503160209010e010b 79
    0x1448c40d1030b0b50b944078031040f85d200030000c1c0c0d580c0d0000c1d4814424600204440d0324808820b2030045c0c0b42900d80100d404805101c51410b041c1034000090038800c0c580300b900840c8000380c0001f001c6540300180c11029440070f0b024100c142d900100c0d010000703402041c0c2d201650407a800e1a149660350081c02c501540480801071003150310300414903002c5900e4a0400151200500b4003c03402d64030300e43c41c003c0500e031101d194032290295110800158890360b001c010000d145030b0204031944c88001034902a1218100f40580000003031420500c0150314001d03400440e0464401e0300c0802900c40200030103a680101250190403100c6418010007403101e4580e00c4010a48018400d22081e64568402c80c1c02c50384594002e544d0300000c1c1e902440449040c80c0040321140c40c07400298602080d0045920050065030190014093b00e440091441c1d214800c00508284e07002003079998450f0b00500030000001442e80a81c0a2065200007140030002d1070011410703070b030ba4050220704180791034400e200040020103a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 766248300 1250 766247050 766247059
    0x40207021f03060e0603061b21041104050906070e1003020d02070b010e070302041202061605060f01080d050702060403060e0a0b040606090c2d110f030a08011509050f 73
    0x70703103076000a92001d5080d039550a6900420007501d0004644d4401d240903001038443e80000043c000300c5090790000481244030030316101e854201c480240d100382d0714058002004c895410701000100013414000b0110400c00700c0b010003058507459403541d50b44804883d2440402d04100d0310781914900200c10303e081455070302d000b510748140d01c80400305030380041000b04d46482c06000188004041e80c115107a02420501c1c00f141031501c0c01c1d403410b10f440783d5044064024440060703400614500300c01d605080325040000c44203142090401c85100d4402486100c0c05405403041e41d82e071040c811000c54040e507030014480c034201401e54464200919094107801424451b10f43d034500000d10300b0035240d11607030060b0400030744240b9180c007110990705a0740d81242081100003845a0000002da643c184400074559451a0808400310583d01841100303000000d034070800c0c0120140c442d000005010440c0ca6030780b00e00346c9903681c407601c4410061078080c44020400242091199080680c5500300c41d140091 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 766249550 1250 766248300 766248319
    0x5130b0f10081504020a060503040b012c330f12070512070302010201110906070b0a0b0607050c2407061a0604060201290a030201080627010f2304020702 67
    0x42c40c142ca0860110004a4880c5402c01044150b00d0255882c50092406040031403641c500b80d5110114800140500e0440c0806060b4000015000e4403000004000405002e9031a080c00702c007201030208409109403400c8083d20300780c1e00c070704800c074840100c000d00a841403510812801c2089610408011010281e11407500002150b94400c21004803490180c805014018203500009080d01d5032a06001c0d101070f010018001c1503141c104c1120171007504030381083c1140c2c0b105014074018101c15120342c5e51102000c5030010512001282d07013150075808950180c80c001d45501c1500d010f0704100e487c1e1506410501042002c0f40954011580d40c1c84c50f24604104141341200103540c2d50002e03044140146c0d910307040c01d401541c142106034206034142c40e03802070407101030000482c0200300b0b0100904010000c00071400b42d8a54007141e8040a110b1800c11032040c424014141d0811024841c104140500580000d01d100c3d0b502500e880003110702d06010074130b840c2c91084c0f1001c1d40c40322000700e8000c00d485 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 766250800 1250 766249550 766249559
    0x308160501140702100c08040303090219171b0102060f0403170703020a03051812070611030a020c10140f060619030203070201060803090303090103090804090204030804030605130b0f10 81
    0x1e02c201c42c826038000b07060baa00d038200040002c0c0f404094901029955240c40d00d00402d081d008034410303600661615004c01d00c01914408110b1108a80c41c21901217440c07410b020812414042c0c102418500d0345084404860443c80b0602c0030150b24079006015801c50004145004200c6a41d80e0b4054005d042070b0055581c0741c0c0b1203002e448800c898440020ba4080342d690481941400741d69000790f2003014112840411a400036210b1a144001d09490880001c14200700710345a041540b031382d24824a60fa4507440c24a221101941c0102c40070b03c030301c1c0100715010420031000c0c0314684e85c40c2030000e00110155110400040e621030080c0c0031590040041c410390800c0175400a4403154108207681c05a12401e14400103825109c0da60040e03086908203114446c5103443c0003055510400e808d103000300b543c0907581080f41d020704c510b0700010788071400041d001c030a00400380020710859201c0c100030445650f950f820001014012100182041200310100b190200b50030055500584040009800c5aa0780c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 766252050 1250 766250800 766250803
    0xb01050f0a1b0b040b06040b270915150913110f01110a030207060e0d080315040e0d030b01091a180f0d0b01050f040203010b0a050f0f070803060a0801060f03081605 72
    0x1220105c0b0001d20b000104000e43c02e1501500840d100c058415039144541b00d01080f003040d0144d00c080300b80f28180d03000200041010046500d6103800d040c0010301600b000e00f00d20341c1c100c901040c41400b0b04941c801049000b00388440645070560030000c858a40f110b8003040041000701d0058803810001b10052a0310004018440c101c90248241c00501c4c2951070b0007000341040d5801c0300d01d1441104944402000710f044001281d602c044691210100e4946020010b00100700360341500105105852000346050b406034080b0385000c0d02600c407045029600c0d00e101900e03140a000044080100384456201140c807030b91403e21002c4020b14000c401d449103c041070201070400d00980312150910010821400d040401705043c010a0f40c00750b21750b6040641d80102c4d4880c40c007500040140004101401644000903282e82101410300b040d40d0b0f0f00c49091801690f00262095840303020705d8034000030f40c50300500c2058221543c0d00c9280d69402d255485100d0203800601250038141d05002121000800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 766253300 1250 766252050 766252073
    0xf180a0605121005061209070b070507031103010515040b13020d06061409030715110618010c0309120c03050d020c0a1a13110d0b0106030b040b01050f0a1b 68
    0x10369031038584880c2e0612641c0e40c1c090b400361801200c0f000c1c0590501c0340e911361004403101003801d0a00801c00351030748040c0c3c07031400303409500600c0c40042c0440e0540801030b01241039401c0364021800f590b0021a04000c05003210020f8803604426150383c44100038030305007600311803005040201061801d0714080c120b5000c0e640400e201841c2155103d1062201a400c86800c240300c00c2d0304400c40d41081c0120002c2503981c422401949481400c221680107400e100700d000341c007007070041d40c113440307460601140c002c100407440c0ba44100d0030b50070310756020341c014071921036940c00316041907014000c0308a4550550726086416815802c11008201465040400b0300061a00c0b0000400501c142c60050070581c2880d00d0303041c40e85c4410311032501403001440703407400702ca80e42c190804a09000460040009103850050f0310004140d007040200000f10503405500c0314a019038241c2d010301a0791540d134011503403803080c40700f601c0500f40c0601c800d41030304c3c4c841d40030003290340b2a035000020b000b5034036115142c4998 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 766254550 1250 766253300 766253309
    0x22d161502010f15090b1f02061e0405100e0106050a0e1029090d050d080601080a0e19051f0906110c031e090a0e0a060e06060f180a 58
    0x80d840819a400c0990901c9480421120b884040140850300050001c5407003661207030710b000d19103461003d0b41a03520b0103140c0039513402011030350f20300300b42c04100039440d94022a000d40d82c0e20861612800c4070201e0442d064891035210300500082c140c0d03030a0f04401441c40b500c51103002d41d60fa11020841d600c0b409543c4001c1d00c1c00014400381c81c80d11400015020000343c00150050240125042d15040b40e611840e0840740005841511020b001c4081f5003c80e0f58107602814a106070010f090351705030003d001500984c0281d0701c0c03000d9a075907808000c0c291619264103480c1c990051200d45402140381010640e09840303a0b0a440d0f2485501650500090f0280d401180041da110130f000c3c01c00001c0e20410701d004600310080d600380950100200e0700e9001e0250380c0c0e04650103440d07031100f029801070115006180010548214551141c489140c9407404541000c2d41910300000070451541c8003011500c10b42c4005c00803458a02e181802001503001212040d4048800b04010001031391068030820140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 766255800 1250 766254550 766254569
    0x2120703020a060b0303072f0603160f0212040314100516020f0c0109050618040c020106050f041a060717040b0306180408030c090607020a06051207022d16 68
    0x102c0e2281820011540e456070310714405d40c400c20640d0300054844a420845540404005250b4964030000000c2d07a0707509003440e03070f0041c0000204075009540c0f03030581024120075510907000280c0000180d0781c668401040e03040400301404100006001204e0800301112a44203542c416070b0301e4404a002d0720800d035400a103078820440144503082c0e041100c01d00c1c03801351800409075a00c8400c000b030400800e9015690241ea40011540003a1402a0444440f2600500308009a0760310000080c002c2240380034070340c450802072402136500d01d003500420b01901000c0c0e01614210308210200b20259100c4042254958010740c0c10b51624020320002e04000c0a03852840342d80c2e0306d44002040300144046803060a800403202c148400300b291442601d41c805200340d12a560f0b0303040000014414080c3d040e000390f0112495801180040d4000007605405404460300303070841d00c4444059031500e01d68a0b1301c1d0814180194403146001c142c1410488800f10b02080e42c5c204c2028950210142405420800c42d0303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 766257050 1250 766255800 766255813
    0x7050708161d090a0f0305131d0a02070f050a1a01092906070b010803040e06030a0f0f0303060905150a0b040806010315020c07090902090601050a0f08070212070302 72
    0x1108400d202415403491541442201c41c0c1c2000c645192158150342c01d403001c0040d140020701000c1003082103000d165001103900c1010881d52500034401c0e0300c840b1451a40400442c8000740003c0340061070300b08403007000b0300d800540c0d58416140e002508401c0050741c01c1c04540b2001f0340030842c103002c072415003402a401451052840034202d004450f069210340c418510744000503020b8071111034040744c010740b000d10031207070b100081c40081c100d40101d904c040c1c010350004c000042c440310008000c0044988070a00c1000ca070f9928410107442da00d42034009001840662a42c0c800200008491036541b0b1190038001540360b00c4440c0714080b100c00b250841901c0c54429100c10880c81e225090314000d0000601c202e1400d4286069641c0f41d00c018032000b4044a59004e40c905000060b030142c0700c1d40344042041740d0200e03a681d20302001a154214041e80100101e1010070381552240c405c40310404450340783c00301d4594140c3c90850304494010304d1407085006607200034098890702c80c02001994020b82c020600c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 766258300 1250 766257050 766257059
    0x9050a0803031b0304030806150f0d0506120f0d050a09030b07030c022b050309120c03190306050604140301090501051603050901090c0e101a1c0908041a0906070507 72
    0x403142c0150f00541c099a000f07108200000f980505180e81c00802170301d03941c02004000301e000743e00740100c0404580b100c0d40860b903003000071050303400b4900c031380c0d0100d44a80508e21284411a1a03010201c42e0040940100f400e0300001806040248140b04842c41c2c000740301a681e84030740c4a142e200f0368852001946a1210b81d4190350304003d02c00072004407011054401c2c0428100070381c1c26464101305030074003002200086540f0b0342807000c1c4d40d101510310324040d42d43c0f032415009034407640700074001c001c1407100c4055130b51914483d1059200741ca5003e02950300d030508040102c4030021120720b01c140e0540d01e0306419000a1400c0c010b1900800d01c00040080c80202c03002c0c040c0c291900202441603d138904101e006c0441d600f64021b20880b441507102d42c076070740c503080804914080c1580240d401081880c160544520700b200040000c64401003619003001141e010b800141e8080000c042e1200f00c0c02d003c07c1c041d0200030742140d40700b403141402081c42c1001c070201003042a0080300003900c554200610130007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 766259550 1250 766258300 766258321
    0x120507210314061e0105070803010314100203070912150c0e131808090613030b10080d0815060d1e270803060424030302070603020f070b0709050a080303 67
    0xc000c0003400c080b40107503240c010041442c180303110480007443c2541168200660340074078100c0d1005a00100c005071340e50384904000c071911030714001c181c00e20700c6640c020201c4690303240300340c82c01000b6903a40c4d41c600c83c5c40c25450017881e08002c4801d441800a1102a00b0007240d6846481902407003030703c502c0c10b00c808080c1002146510305191103409401e10381401e100340289040b03007400d9039100c034405480300c00d6800411040e00402d0a00d43c2985000e42002c0103021100f00400c1c80b644aa11320358030966141c0c40070640701c212030407003c03021400c6038001c180002038403092980010409070a00341404845102d09050721f0045c000c6000d100c1400c031214030480d640d0702414041100d850b5000d031200010b00040c1c8082d40c004003029184410201c046003882e65150420550340401d1101032500005007040e843d460301051000702e01600c180000040c00c0d034002d00a450b20142030405c0241411a140c8509110f110003c3c600410800001c038003040998071400044081c1040d0f000854407442c010200300d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 766260800 1250 766259550 766259561
    0x4080601081b010c0317360601030213061203080402102d020f011a0310090201050d0905011119030605030613030c06060b03070909061a1804090203030c010c1409030a1205072103 78
    0x4a07040700340404407e0600d480042c0081c1140da05403080b03e050107030740b00321710010b00041c1c00c000d003103030103101584050542c0f041c0802e000f40d0084819980c1c501d410340003620884a50341c2018685400c600c4026010340e41401d18a049961034016601400c2000110300c0c00c4850800c180071071440e840303003180040d0030100010420140c42d01010004000940c0010b050790183c000da098030282c8074108003013003001c00e400c21502ea01e1080d65aa0321f50b0815003500d500f03034080404850005c0c1c070b0010300003034900d00003503654000c003030301410084546215101214444005202601c1403516103000040b01c1c51004011480303954580d8447e0f0702c1d14241400c0905a40c0c06900100944405015207101004403004540c400c0240e0742c0800c0724a1a01c4010901400c0c4c80400a50302d4040481c04080301e48046d00b00c207004c8140d65944c010034800c0800e500d0881d000b00541c02d80c01d54040440d84001404106004500740e1702d40c102075003072144941c2c4a9801844480c05812107a4900b11003000307594260041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 766262050 1250 766260800 766260871
    0x140109020f0f0a0c0506040303060303080a050106091a211f0b0d0209030120220b0304081b0607020321090c04050c04050901030804080601081b010c0317 67
    0x40d4544400c039100c9003540c0c0038607400340c0380e80710000920700c90040c000c0c40300c80e02c80380d03000e819201075140c0340c100a0000c00d039a12007900444c040c4400140d80130031920a643c1a40d60a850700b403000f50400c0600e0328408640000d0354981e0b00200003142d40d03020150b40890f555074584114060901c1e04800848800b00124840700f4186980702c01401401d80785016140c202c00b44500050b142c0c50101c0c00030b80500074100e19000390089a262400b4800b1000c00200302d901102c500e501036200c052640c00d072032a0340324030038421241010f001040c0011011402002c402d01080000c0120007a4401030754100042030b184180507a100107507079041c00c3d0039003c3d9040c00214040080f10240b80074841c1c192203c16081100e845144d413400002c061113018420381d800341c200a48604519a100e280001c1d03998000e0045a000388180d030000580440001544c08140030200307111614404580010b450700c1054010403405d2140c4403031040d011858100011744a100d6408050344903603202c00d00619000d6a1641 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 766263300 1250 766262050 766262069
    0xe0705151207180b0307121b021e070b0309060a0c0314040b0405030c01020d060806010f061707020c04180b36030903010606110c0913120e04020c011401 67
    0x120728803003400d5a0380c00b818500703200800c00507040d42c810440100342c02854400c0030220034841c40a44c041d018044031072400034108010050290810011100e42080000507403000071a11040900021410904542c941c126100142c8881d07000040747c204846c04400f50b1b101800f0854140f131180500c0f1085c40c014101000902420f0082c00441140100060506105034011404108040046880c00104e06008549484404850001401c9a88543c0c04a4810200041000060310303201e5421610303070303071105200c00b1a03801c5004200c0000905801c2980211504c0262036102d038000c2c0566074012042c01ea03001002882c15924041014001c0701c1002d440101040e6040c2c0903175030480c40b4050310f00e4680c00d407070310214040b0310318400d183c1000d8041d420464001200c0c0d420400c0c140c413080042090785c900030801000e00c458010200c8884c50b0000c440c18081020410216084040c801249081c01300e0000d90307404601030360b21402c0544650380d03450b101c00c0c0c80d03801c4060180380036000c3c044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 766264550 1250 766263300 766263307
    0x14030a080a23060a030212101b0206041e1a0603010c0903050607050d0e07080304080706020303070c140a0b01080c1503040b010311010c050f030a030b0f011d01050c010e070515 77
    0x244081100140d510803260000c4030312021607001e42d540c884007401158007d1850141e4200342022a031140060f060022050f030a021002c454122241c21851007881264001c0425aa5586603204880c803a8403807903100d03220315001000441e86800030320820422051801d03c450800d00c080c9400c40f10400368040400c0a55402840001c1d40400c150f60046050b15040d6194441c40d8803c05c014600079801d11040e11030344a000a03090f00100103881210309404c181e4640b5075076060140c4e12440102e44580000f600c004200d030004030810214945440000c00702c0d5200152982c3c2e110921101f80c0041d115a840414100c00394038000c2000c07404010311141d00c90441c1499620020511010302004101c54000c0a1441030369105d0401a802035801604890540f540038883ca61654001e241c8500042c0c18503038070310310030b09103e41c042d981171406079100703240d902103000040c0c40061000101c07410031404201d2000108000d000f07955240d9240c101400c1d03281d00d020f040040c10200100100100e09091 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 766265800 1250 766264550 766264571
    0x151121040308010e100b0705010b0405100305030a03050709080a0515070e011d04091a0610140a031e09060e06010f030b15041b021f020c1f0914030a080a 67
    0xc0b07402d811500781002020341921440324400d5107002e07a8202d4076100b5800309083c0244941500700803e401000c0e01d04024030344400310800e5601410f0300006d8100d51040003060f20240c4039500040d408041450511407081d10741e03d11600f070a0800070113681c698841d22445010012020040f03420508904021115030400340000c0d00c0980d01648014440d50000c24690607921103030804000140c1c4800120703212400304561540d910416200c09005040d01118601c02d40c0c0218181c03499a62001000c43c01c000000c00c0c00c9000d00820100e04102c00ba10341540907543c03219000311000c0502c40da40108103191190801481d1000503405600000f0f0750480c00c10204000c020712a0b004444a0007941d0721100034004540504041501991001c451402c900749583d40419a081c0908400e400b94050b420150818000d90241c24005411600700805c0c0f45864400c2d0b98071182084110b001c08105252691102d2007500103040807074003560400511507404139070045010740d114140c038104104070100d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 766267050 1250 766265800 766265807
    0x20a21060c030c2a0f031d010801050603150a0b0c030c01050c041512060b12010510030902031903020a02090f070206090f120702040216120e0105090906010c1511210403 74
    0x5800d0240020015680b003184c00028030101d200d13000d400c4003540074080a203150041200310324100d0390f01084c003015074219080d8881c5541074100c0707600400c0307c6c0c00e54503105100c910580c0c440a40951000b10310b080056215500b0000d005a16a00c070003031921040c203100b006081d5040102022401c1100308401c0c0310703c5512400300c01035900c83c0c2ca42442c10005407254100103114607005604480804030b0b002d044e000d0500f08072030681e00305644038408a12100b0040c3d06035030200c1310096047c6c01c400321140d800c0c81d044c5d142005850103441102c149401c00d4012403000d00d416504c1002c6400d0791300401500075010026650848883e000820602060700100d03900c80c6034405102c4202e490000c2c50100399965901a00c84420518466103001c50303151410844089860020401045915455441d40d40c000c4054500312000905041415503a680044403080e0072100c2c1201c1c500d00d010503500002d52244251080d007000b00300500c0d511a000d107422040304c1d00f840c02d0701c03c28100e03120401000a51 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 766268300 1250 766267050 766267067
    0x307091509090f121709030d243006090c0605030403020a060b0a03080d09020f04150b0d020c070e0106090f0b1b1e031b0d09030f020a21060c030c 64
    0x1c00000e01818048840130840e050343e41d4020043c03148608205015108501000070080d44202102c02c004c0050103007265951040903246420346198810800c000380740a2076000c0160303a5000004190040c845170f148070641901c5401035940c00d55940e07030803041102240b45080602801d050450651410b41d0b402907030382101d6000280340a031608401c040d01d4540c00d886401541d0702629968170b60110600a00050002c90010792160b80703642e01c0b41030141002e20030b034042c110b2511a0400c0e81030900301783c0c034015480b05c800401040d50822050f5118403007441690054100781007958065490124020002c2d5001c4e00610100500007900b0811a0f041074126032022042e031401c4200307280d141c00c14606000d1500c5a18035180c0b401c1c00105400c0f4401300050003151f00b1040702c40c0080824011840c0e41e040d00e46002000704040500500c0480c14038112191002e1000340035004080e2038481c280e402020241c100c9503a00030340c480e20000c00c03400d40600114824bc91404006603084070328010f01d82c0c01c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 766269550 1250 766268300 766268303
    0xf03022101052e0521130302060c1905070f020612010608061e010804020f100207080f01020403031b0f020d06140a1b122405031b13050c090307091509090f 68
    0x4000204103080c1c414510403c51003010005c181074080c82c01c04071088407204000f00403030041c001c503c0020388500d50842038a000141c04918420000352840050364154041c8106403a03404040150304010307555500102651403800c00040c944ad4988180640b0411000c0d20a9100d04141d8a00c4000b40002082c0049000424a4020307a02c0d00c403030001c2410300c040e801c440e503001048424034001c5c140d00010320304102c3d842d01088130440038a40d80c48074200d01442c0002800a0502d20a29201c140f00b00890310b82103024100d03940c50301c0621b900003120100003000803100540c80703042002c0380c11300380088a507016103941014011203c000d4030100d41c00305844a460140320030b07526400e80005e82c0c0e9201e030341c584655505c045000064980300c4807241209100c1c0790b12030312905010b030081842094221a0100b00582015a152210b0700810040e240051010031000c0080c01040c403181c0d0200f15840c0107101c4080009001e1103901e2069011181d0740d00300c0507403282812129400100c82c1410f03910081e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 766270800 1250 766269550 766269557
    0xa0b07030c080438070228060b031f1a06070f0b1509090a1115030c0a1419031b020c06030a02072306070e100f03022101052e 55
    0x7440c1c1e80b40c10110b692030a00b9004c4142103103060b0310301c0360441955581c020080c640840d400b200e43c000c1ca4800401c101d41ba142a0841142024000a42142c011203603d61000701624081502d01990190740a0749542c5c40042d145c40e40c2c8103032204801c0580401d1814001d039000f40c03401e04661a0b009000c03160100c000c1024084a000034130b507905001012014090080075407641b410241441c2d075980302810345c00c0c7c0740242441040c842c0c0c0d14081ca40724444010603040141142d45150307000d180c1d0f0300004400c0b402d100c06103031030760f64400c060801002c111030b003027100c1c00250001e200c0080803a105016410031501207404001041900029100501e400441d0007541d07a5a8860a0364081c1c01910b4008001e81c03064035440e2030000b41040c200c1e410f00188022503d0a031f903104030482c0d201c4050303403c09820200121124010070b104805a547c240013904015140150314440c101012204450306d586035840b003c018495494401401449826544054281a1444096142411041022841403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 766272050 1250 766270800 766270823
    0x31504051b012c0604090e03070c06050712180906090c140c0a020607020f03031b0d050403020108041e05030309010207021203040b09060706090204090b0a140103230f030301080a0b07030c0804 84
    0x41d030fa0301e8040742c2c044c001c444000c2c02000281080e0307962341d421081c0c044507445d00260000c00d4140c822000d86026541050030024502c91201d0306071480503071030114142882c0184030201d030f40c2086000d448020301c0e10400004150010010007410041d4400340800d004004124850901c40c001580d0001180c0465956555031054400150914a04041c1c0e035014040800c2d502d1044090841c01c0400c0e000c0d100550b600104c002c0c03000c4815101e80d00000740414a0000442d022500050300e00600c80c46800103140000c2d0552039451554000b01e510010580d00000c90408504010715010000751440c00217500f0141007901e41d003040e000d201c0c00107000c0e280c0410381e5810b024854100a4509401070700800c204241810496110441151105101801d00c60318000d2402c0d81603244d4101c980100e43c01200000307041e00c50210180200c0007a44038810a0030701c06050509000442c000d050100c000e04a219580c5480710109100400a60034117142200a04116402c81c04556205d64802c1d01d40c0079 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 766273300 1250 766272050 766272137
    0xe0a06050a02011b030e07061107210b010906140409110f0d0f03080402040e2407090824220201030906060e150a082109031504051b01 59
    0x14002d280d00000c1c4d10000c201348080580d09540418144075100040c0c0360001d4030350005a81042840c000041c295118000401c0504103086c803c8454984015001d24030240f030317403100c20f1095030a0700082d05051740c5c1e080c2045418042548010760182c1524144020146620b8403c01c4c00c0d404e001990048103403c40401d16651040310003015281d01540b80c550351042c03420024144078041b90200d01452601f4840a0207800000b244520404081c00f20200140840340b103114000006d4600c3c3d092102707080700401c00c4e0205001505030700e5813103018000201d16050000040e00c10250181d000c18040c0100c0c2520100e070500f01c130358515028203001ca01d002181c50705100401c059408203590401007818022090202c00d034003003021008a441d200c04507160301c030058076400d8010444294001c281a10400c007007070f40c030142c18500402001d49107180d44081003001d00700001c032403c487c2030f00801904000d00b1259508601c0c1c12500b880d00c901070038911409800303a4138100c24007965842204603a140c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 766274550 1250 766273300 766273303
    0x9271a03100c05040f03110f04020403021c0c1d0a0b04020405030601120507150203090a090b0303040614310807050105070b0424060e010503010c08061009050904080909070e0a06050a02 81
    0x40040010400c2101c4150b56400c20415000c647d10710316102d402e00003a50040d5113003a000380c800b84c030740003002c040740023107206251481901e5040040b40c075540342c254005415429003d4041d071010400707803008010f1604a800c60111021040114411481444284040c1c3c0b800501541901d07801400541000801e003002460025160300a9400800c80b0000d8615282d010000d044624800d5903000c40054170345603000150760443e102c9a40543c420b0004000041c0304500480d200b503175801038585029803c5c0048521098140c44440510128240044000d50015200401826510082e1504c681802c0009005120382c0300f001e8070000302b030000700e02444100c103551810700300742e034080754108140c06402101503c020b21a611540010000000e498181030260141c4c1c10301543d40c010003541d4200400ca0036408030b800318020401d0301e00d0045800e44410301014080c1d40a80c0c101c3c0c0c0c48280c0d98081001410006000c041001581e6030006503a4480304c060b0000e4614a04110b07445d404191000c9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 766275800 1250 766274550 766274557
    0x6300b13050106060c0201110706140904140403020a0b011406070f080d05041119080607230d02030a0b0f45010815071e09271a03100c05 60
    0x1070080d510b0400001025900480f405035154401c0e02c038500c0c110041946c4c5a01e401c2140320724804182c0c00c1c0c50303d201c41c1c80c01800421351756600030400203100102902c01040004100d40403000350b032100b800e2209100070340d1411401030100c0c2c031071515400c00500100e0a81d0003844002042e00302d0110900c402c001c0f5800035101d5503d100d240800c01864507080402680542d85101030040440750006c03040b040c0c44c00112001d6420343c070010b01840d2107007a01110440c85890111038001e140c01ca41604030b810150044c0070300141940d015880b030401000d0301003100c03c844031300c1740318090309290610661901708000759120705e5405c411494410705044814000b424418240419800c4401070484d100004103103810703240114211280e05401c40c2c10900032070025981e05002c1041e11540c22035800c0c00c10700203114001145807c201c600d5940c048215a10311660b651041001814100d00014600d803003209d1928241502041c0030148450229441d90450a046010320385c5803030030318410328050402ca = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 766277050 1250 766275800 766275803
    0x904020c06070906030f0b0d0b07031509020703090e040515091212041a100308070606150c0212010c170603031e030a0c02030a0503010b03250306300b13 67
    0x2501e1051501400c0145985000d00a440c042803a1000030fa100c1c01d03181c4505d180e0703082d01600303501442c8a143c031032070b0f40520004c0040003099118281c200756014503902e1000240051480980c039400545400341040c04590030165042c49031b0b408220100f0800125464004000c103261103054594044060502006501100c45081d000901e00d446200010605115a004000c18010782424201c80d0003605002c5e00c28125282c0144030501c0499405402040918031070400080e9041d5101d06503098810308208410100d07041700e00031010b509002040050741c06008008000c01008008042c110110142111540003020700024032142c138100704444890044410510403c114207403056100e40c001c03a144400181402e9201803028000420f41c0c40f0403070f82e901d50a0440e800c000071362415801c001c080501241e001000020105800400c10030f210680780e07000b066482c281044031500c01001c0407040001d440c01c1d07110028260303894841240e030310b6100c014400952142c0c02d141606502d40c400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 766278300 1250 766277050 766277053
    0x9030501050702030a080105090103050a02010f1205011d09060c030c090d05011503140304050108040b06030c1f09170c0d150f1e0b1807210b120a080406050904020c 72
    0xb80008160000040c00c40000305648107140c41c1e0701d42d028442090021311008215500000b0300d00010340c001d550141502134140b0340090761510356600d20050794000c1e880589100d929020362010054400b00315076002100800815544c10b000030780103158803004000c9000180081200c1e842c0359540100342114a421600900c0441e107004550341d040710661208441108034504041030181c008025038080b00d40584500c159a0340301d844070070400e0f4008140e02c1e450300524580d490103548540c0d400007070600c1030ba400c0d2a442c513410780180c0381611030b030054210504480c218021317500f000038002400714000d484501d801c4c100c2d071502e004c4036400c1d4210f000c00142851404014007035580e00c900a14036030b0200a0b060350904031920320840b09820540782d04001d50032113150b101604048481c0c0c0051952500300035103c1c1c1005080c00c1807048620080d64252100c46144540ca80610220303006005038010707018142ca10342d24007150784654454042446401303d003049444c2c0d120343c16134800420707150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 766279550 1250 766278300 766278311
    0x21302040f081c180b0f04080a030c050d090803190207080d0224070c02041104080102070510060602030327190506270705041a041d07090c09060c0309030501 69
    0x1004aa290406030464040290008540d078581c180705012400d005108041d1501613281000784001c1207500ca03805a0f18900810400020445410403240c0070b22406952400c07d5801c4602d020341c24260341c0c5011504100040d6402d00c035450740801202e00b0301c2030820641030a8031400c0021303401c110f0603511048180c040c85009182054020600702c0c40f02040c10000e50f410801030944800c1c5590a07914080001e840b14640401800c095205001e43c2401d4040e16081c1560f514034203080ea80140e0088820750481090181100c50307901401001e809030780044c5081d45810740ca82c81038102586130443d90f0306e0310104a02c52210044c0000d181d029070401d1240d170003803024100389540707a4003542c001c140090400905c808806a440e000c0d03860110b0740c40500300c0d0700e02d00b0042201410417a0f01c0e42c280300c0b01b210075018070f40e5118480c00380c2500f8040b110b00720b02d402408589082c010640e106101c403d040040907030269620022080540f01c4905201d240301c4180d044c01c0722107038141d4100420541c40d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 766280800 1250 766279550 766279559
    0xe190609121806050f040603020a0e130b0406140d02190e161e0210091e1101020f010207080301120807050111031603060b0403080a18030b06130216021302040f 70
    0x1486500700b5141d965400181c0966a03d01168240b0078803040b007641140c140000e000c014403035002014441c24a03d03058914034440360004c0d1101c08405d03015402c00c1d55441d14215503082c02e009500c0281502401c1c112210f0040011aa00c0003240000038855045034a070b8440350300d1a00c001034082c0c517030046082040d20300701c40c50b504070f02c1c005e00c0c0f0200862560070841c2840c20701c8030588a00310400e54081e100303502107102580d01511141a0442d4500c10303040d80740302502e6008482080d03583c05000e0140d0b0505400e000a81000c05511411140e03900410403400030414080489044440340d0f46000401d80250421440030300882c0b000070b19650070021001d240d492040003560042c81e1003a9084210b0600f0202035041380c195206845120400303000400202e00480040c08109007581464240031706080400318292183c0d0700708540d111940d10500102c2d081440406c188501c079480304603d0907200d15000c0307110b40d2807800c00038440c099501c0c1c00a0101ca56806030f034000c00e00301035045103441d1507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 766282050 1250 766280800 766280807
    0x1e0b1c1e09052b0906080709052205130305180f1810080f2a150d06050117040605040201020c19080d08040b0a0209060f030103030c0606090e19060912 66
    0x401109002403050003a649002c60700f884519000100103807039040f511881e001059425103401020038051011405001a9544440c0c128083e91a02000311001048021056000b12070000d414819410201c1c6003100000f038000048406031034454502d4400139010034001090b81d03a012001c1c5030800003010510704040120090240201c01d0014540ea442c2d4650701c2c8540c0c4c8402c3c0302c00746141640841560141d0600e003244551034000303e2280800024940c0000c0f81507500001e5411411060000340050400d9052088001038102484e0600c40701060541ea0282e01502400180400b60703100046411a8000c202800304204083d002c4280b40c6600c060260300500b030740c032039842e0314000d00c404040e907284110307040c41c403441d4880c4142c60162525940400250480c60701c040c0c10103c100072044340503e00d5030195000310700c03075900d004001d0090301c2e208081e60100c1c0d00c0300c00f0003410300e00c215580b845c0105290000b0a146641c0360704070300301c0b42403d030064050b03d1b2001d401c03106655840c0991550 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 766283300 1250 766282050 766282063
    0x301150309080d1d0d08190207170c030c10020406090504051003140c030f120301120c0902040e092b0c03050f120906103605011e0b1c1e0905 62
    0x2100d0a458099954010a69071807000b21050200741c4981040e1f0803c00c21b050340a8000740340039002290110181101006080c2d0201800011661000c01d018591a40030009000a0011048150b05041c68900040c1c0300009500400f44150344030b0700040d15801442d40ca078001107420544180c2e0300c9241025103510b078001a00700f00c2c000c0c054001034030f95181000444080400c64800110300c2d42e883c2050708481d80e058074000b20307000c211055000640c04038031300180018200700c10115600307052100e4010716200f601041c1028082e8420001c00104104401d0008510385900b0402d980c0318482c0b504803610b1040081107890820049421501850b070052024402d590503c00c403520fa80300c505080d4400510b9200e40805070000c5d1404118905840500c080c20304c03003846a8580c4100c03208070342c4054410907007040d100012021100365039a00030580840003490802852441d0103c0398500c00320104402404444103501d4001070020b114040100340c0d643c501200d03080204031440d20705192281c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 766284550 1250 766283300 766283351
    0x40b070c081e2715030f010b031806070806040614030a06020a020102090a0308040918051b0f060a0804050c010908100c051606050106170115031119090e0c0301150309080d 75
    0x212444c80707441c034841000126402043c0c0d2130151000e5a180951420007035100801d810311005259181c00004081007000e1030041400740c442c80d2681c07902c401800210b403201e61080051a07022007007911a51004540803450541001e4090f82d81c0c00000d9081e0301a2040300c0b40c0c0c58100250a100205002b50340028106440000c178061210340310041000d0400114400e004d80300380c200749200c03802017800c2c000c5640d0501000d0105014800c18000142a6800c8102c08201080d401820041004014440034020a0f002d0030072200e880c1c2070400d1290748241001c00c3c81100b581d1a82c504950324050020780f80a28441540c03040c2100232480c140019000031b02c100c001003404504500d03c010f13900d043c001e0581d00003a8200440e034100160031070141c00c1d01c80f500d81c0100750030000080b9800101c60380c000241c40305e407580c904541c50b20a006400308001001c840c030750581400180648040c1c40400c106184441c42d001c901c1200e03608140d4030510408228158040c40c0104104640c0410324080003401d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 766285800 1250 766284550 766284559
    0x10e09061f03020c010c0201050603070e152d0625110d050f16060c021309050709060e090304081f02040902030726010302031018050312040b070c081e27 67
    0x401b60035001d03420382d80250754140d81508035201c20b110380303010480000c1c0e0102d240d03a001214103c00c1c10200d241d03014003107405000c101449030340140079000152200310461043d500a450524210007a102480c001c41c0c2020b503a000c6c10000001384940444500442c582c002d0050b10743e110300c2d1038130580c0c600c01846400f4103400f4030543c1c81582404458400c0445115885004039182564208544918903c1060910035900c00f444c0c0003292041014401418010000281031400e01e841d280c00740781e0042c00001c0c01e034010407090180040104091a0740418007041a0544a0f9502d491020380a1508280801440801008106030b800b004000c145510b200e040c8240028007944081c164200b4040650941c6c8410780540f802c50003680314042518680500084070a0746030f840328155030114040f060b203035203400284414000d0000c402500260942814107401005035124061400340c00441c240c60340c800003455503260603820444a8850500300040440a0100c0c8454820726a1490301d6005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 766287050 1250 766285800 766285811
    0x5012705060c0703090303050a0c0609030e0312090328140610050d050c1207080109060c08090a0c060f1e21020a0804021e030d0302041a0306010e09061f03020c01 71
    0xd10b1000c00850b0641501941c1c0e00070058116101507074a43e001c04030820401040c039418a001c5100c1d03118208180b4400d556010b1301c500b0f1030040510f4840c0c500703800034401d5030410110407699030004810b51410703074203c1002e0b42c5603401d11030110703803248c000300c05460b1441200300c01080c1e10021030f00d2880364444c40301c2c06890366100c00078485501d07a03844005000381c0c0002c00030041494040080340403880c1c000103c5250319292070f01142940c07650041244c496480c1e840f00d0240c1c507005040c055104031f801c801802200015117481550184034400c0506101c440e400180c0c040b131103048402d2611a4200321107540810b00d003402020228a03c90118220300055403000a056941c021103204170519a03036001d540e21107400300000894142c0c4040f008840e103900e071207034523102401819200303941d40c0c60045c0c507246420001c6040c040d43c03003541202302c00200104078450b81c01151181b001d48050311076a856036640c5000c41c5983d180c491500fa8200900c11000c84c40300e915400405610420000074480b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 766288300 1250 766287050 766287061
    0x204050a0b060a0c02130e03090f0612010e060f0a06020a021f14161e1a01030804090506150d0f0e0f0a0f05120a030b1e0604120501270506 61
    0x854061481c0260310407002c0010b030340140d1258600d648460700040c104184014150301c00380c00c592007003c09403107075000407602200300d282220985031008801d6800300e1424401201242c0010414000d0300d0350b85000300b0100324240c9448419200c1404050300101c6181d844510183d9500c071303104400c80c82400446d544d031881d0600a00c0390403184000ba161007240400134051255250000c00510030860004c0381e203070001c10450928403010403680c41c600c0603504c0e41c500b0010344100b0b0b0f194540c2c0005410000420004600c00700300c0e42280d03030b00c4230000382d5134889000141d0505183d40d40210505c10105058140842036400f1015004640e14104108150744001580321064502da048160f0000504107002c952121110718681e4480d80a0311800080810f100040c0e07000b441d0090300007503940d0103404080c1044003000041c415000d407001401d581e800d0000d6244d2040f4028024400c1c5010081e10400409400001708c0e0700309190600c241401542c404644c0c44642042582d0764418540840d9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 766289550 1250 766288300 766288321
    0x120803060310090b06010507020d050106090504020907090f0509070509100305100e060a0b03130507121a0f2a160b100b090628030f05010f0b0d05070c0b0a09020405 72
    0x62000d500026074069a505d100041d180d503000b4603404d0f600840b1008030000015002e10840d0060310780ca060005007410f0a00520080c1c01c070040c080c0b01400346a107003c0c0f1a0701e03075400803801100c00840c0c1038061540e800c01c00701e0f0391f402511000c5402051f005240520103402da0091407045520444a0310826510403104103012003e0b14050303000307050084140300342d5804400071940000b070710040000495066854902d000425803001c0c08120b842c10070765003001416240d00c403400320465a0040a410040150101580c010300b144908142156404500710305110101103078400d0302c0711650302c2ea1300c19821500b540e00401000c840c0003801c480040c984201d5a1152401d80703041c510810700704901c04c001e11000d0390260110043c1c01496001c00c0c550400d5120740741035240456074021680046425040065507410f070030510102c61080c1090145d0b1b8000b074251412040c0c9820042601d4450903010b0300d4007000c0d0745018041c00c040c441000101c41c819040140190b109480030062a0303120540d50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 766290800 1250 766289550 766289561
    0x10b120a18050f072102280312030b0108070518010e3c0a080703060203061f03020c060901110f0d020c01020307110601060201090b0c13081e06150603190204120803060310 75
    0xc0d4020984142403da805d820a41f00e40e441c819012402c040f142c80740c070303945c1102c141c80d00741e03400080e254010004c485d41e0003d44541c1002c140c1c10030908009500c07029102c01244005054100440c0da103100800c0d41e80d516070401144d02e01a8409606401d200d0070140031707010300e00c98114075108048034003020308000700e040c8120f803c000050680c0d5420b40e65841c021307510103000c05078450801e4081c0321020141c4a0560364121071740e200140d80b002c03040c0e0000e00342100142019426458900440303403d500810071a060825030b1140c0581da07a4980d15185c009000b215100e569561005c020000065000300480410800c0345080b100541e07a1400102d00ba1625500c004010304984004a01402d0404016080001c00b0500d040003d98541962615104040440381e518003000c0e040314070504424455581c204420004504100041202103500c074840030709102c44140c2500b040c140000225810783d80640340100d58500c4003402ca051894440e08280e82c007500c2402640c18400404440c4e2049 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 766292050 1250 766290800 766290803
    0x8060405060f0c250b0603070b0910090f060c170f070609020612040b01090b030c0603060d0203150406020307090b09030d050c01181406010b120a18050f0721 69
    0x2005103a40e0840b03482140c003006407000c0c4a294092081e01e07200d1100507030403928281a007581080046103410b0030113440d00040d005500030b4004060910003e007020040310a4088147e8240d006001294000c40d802e260301e91200e501c410042c90f0100d4495404a42d94108900515804101001356029600203105418441d820148108180300005207241c01035030f8102d000529882c14424075075280302d0600800c031022181e8220340401441441814402e6201050054004003024021503021401074030002c1c144502c42d660ba07600d01740456808214034044604400401e8a8504046c906000030b03403c140c8030800400c12904010822469400c02c1c1c541c40300000f0000d04032030414820651351640074004a05c02c42d502c91801c131007100c00c02100c400141d403003540c0c280c0391414814a650b08012042c0c0200c1800309003042a58200c03c4072107645900b040510000244180f289115030158820b9032100030658015200007041815011a08034211000b640c1a5468030040d59403051020141050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 766293300 1250 766292050 766292053
    0x9010609050d03110f060601090f050303090d3002010b15121f031b0803040605030a020d0615050702010e37050a0e07120504080d020702031203130c08060405 69
    0x904116501d0000360704641503009044c03a0300c1480007818518203000581ca403021035a4010341c04c1c0291541c0c0120840010407101c2c500981341810203000036200d214a40840788140d02000310801403250240651040514001c941644800c08013040030400400c4003d40c405546011000311981c1003ca0100041e1040c0741082458806034041c14085410b01a05900680c05c450000180c032090420410000c0c502600c0808021a00c1c00402c042d4611140c22904068000744010031005400a05072504094114005a191281c801078035004015135403140c0b5500311a07005510500ba0040010483c680c000e82e100141844060180030100300014200c0307402d40001d00040303c0300302d517800320790504000e0b4140c280b8106e07a031980014000d040c1e03500b0a00c03a0050403000e119525030018207090503050340307a80a00c21481d09849104050094001840d00c03150000760f50350841d40c007440740810900300905041c2d103d080845005a0840000c002107491074040680468407240000c2c24900c00d960200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 766294550 1250 766293300 766293317
    0xb03041509110439091a090a03030e0906120c1215041211060405030904091b0308130815070e150c15280b0109050d0809030c090106 58
    0x240000300030003441030182c60a0140c00d10704005a551801508246a12114014600004500004100c0c01803220071502c110f0304140000d421500a80c10000303c0e0755041040d07181c60541495811288110061143d00c403910b0342010007019000b401d8200a03d100f5520009070340d03200c0d41403140c03005101c41c010030304d54000120080c2518140922045002c0400700342d44006400c0f0015400103541035408440303401101050340703100340e400401e09002e50483c6008129a091907106d10791607106988425001740c2d200c0c4201d02c2440390031010009150403d660102019540e030510f10100d8114809010341c0140740c0740002200c2d4400079071080c071030509200765121520303100e206407001c6c1c0140780032a070041160b0040301030076883c50380542180310359000545020400341c4580420940700800240e121204504040382c0d40c2c1d800715010b50407619001c00028504040e00042c0c840d00126400154411168680b100801c542c82000e000390040c181c00300d56281042e0030400c035102909000304800116080c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 766295800 1250 766294550 766294583
    0x507030212031f32060c06010806042108070804110d0501151e26060a020c0705060313060f061701060312051603050915040e0912040f0b03060f060a0215010b0304 71
    0x44c40d142181d400201242d00c1d0000f0b6480c0381b07003420000d0340a0a415003041e4200b0060145011810310003103905189040a0b5454900150412102a010804001d40350001400b00941c1004e090340c102c3c1c1c005d080c09100f00c0d10b45001406807005160121074040b60301c400142001403c03002c86001d2800c280c04002050420760b2001c060020000107800c20740c840c896004a4042c28032005008078408a00580d5030307400b68800b00d04d417007201d030711050103024108104040d4204aa0b6010026a4000c001048040030aa03c000103800e2582150744400340324200c41c0791403401540003500b201e216003140184455a00c00640703403805000410201001a01c09070340001c0e11400091500304030060544011400d2010b400000307402a41000c401c5040401c140500301e0b80422805204682441c220303803030141800d41019030741000f4420900201408000b0801554811280b070101902c00f81420380c640006000096a441135082c198510580340000441c4541050040344e20640c1c0141295903142c0c4903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 766297050 1250 766295800 766295879
    0x80610051507060203040c030605070c08072312120903130303050a03060e0103080c060a0504020f041503060f020a09090902091b07020907021e030c06070507030212031f 74
    0x2401c481402910108800000548144041d600940c0a490514a22411860700b41c0c1102c0014042100740488644180300048505044a0762268803c81d40512072101104002c14101e00c1c401411990203007191075820b601d44000a8807910401c1160410345403a0003807103e880b40b140f0407032150030940310101400031a0160000300401c50551800045059442c20f00500c9a42d0a801c02c5032500300001d844035552804002d2030390480100e0b10101300030b0816900055501d00070441d803030301660f1502e02850101c60440504001141c010605105102002d03100b90003e5004e04070034404a45090400b24202c0001e01c03074900d40550181c1000301c1078860606207500141c00d80c0c16911074200402c510380060b202d1113900c9001b411280c000b41601c20103003041c072607074070380048101c03020b6401801441d550000005589401075641d0509550303404072400e0482c2410301c466842d001411000051201d500145080e008c006a040c1050300241a216009000034116079103800b84800b44041204070070300f60 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 766298300 1250 766297050 766297069
    0xb03030409050711070f030c0509070804260705030909010b0a0f1d13050402040f1a09090a050f070e060d030806132d0608030715050a060f0b070c08061005 68
    0xc240c100030203c0000c0941c105c2c40c18003d42c002076881010b1400030000c02100d88a98030203020304646918080c43c190800401c1e01200920103042d08024405000541c1c0509070311031461000c1c9118965601030a04144da0b8a034042081da13400307040e040d0000204150300f00241c3d0498080c990b030f114400700c1400c0c011185038100d00c4c0d40725007501401c0350380754050b52010000c004034800800040b440340740c00d0041008840b030842004003003d061851412078180d810481c94840300e012180343c0e80c1c2c2d403180f58045140c03000001703000f042c07481a50040403a421000032260101d6580c40050382540e5107041c00d00010303000050008010a54003004528140307003c000c5c01c04a1080e0032400500002c02c00c00460b00c81c2d40481c180740c00b502d89000c80c0401c040f01405448080c0c5909401186081c055a50300c3c0464079045000c80101c0340d0714008910311031900c1d08460700800080b01144504d079141c8580e10074581c030405085490f1007403090001810080800c0d03140c440c00e51040000c0c8070358034003820b0215540c0e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 766299550 1250 766298300 766298311
    0x70203070303020904140a1b11030f070503040f24020d05091c21140705070501080c0c0601030c080c0907020616050c1e07120f030c020f220f0b0303040905 68
    0x90700c0d41e81d40e20380f141880c10f00c940304400c81000840e942358114501d0360001c2d02441c0002c00c108a01d699207410040000458101c1110440301540c1c03100941031480c01c501031500b10a04900511030006014134000c60a500c603c889030056002c14400c000b816a501c5041010300070200301c09105191492a0180b00c507020405004d40282d240c1c9516030381c100252404040502617510111407055200c0d51001c000b480c10210541107900e40341c070340d0f26000ea84603071500c9058100041c010000d190080f0b01c00503030f030816002004540c1156124074051524062034002c3c180c0e548100044403007a40790000350b81d40607256a80250025803606841313283c0d030303aa0041450b002d0041c1000341d0800303164100090030075502c00d6215090b07131004011700f031428200c466014401c0451441c1d880f1010806240c2400882a0f140c00c0900656996201003144060400681c2f544500c2440d008510030216280382e150304e10354010b08000100301080c2c2d002c1114554680345405500c00d03c410300000c41030341c1c0203c0e00007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 766300800 1250 766299550 766299559
    0x30d0923010c060e011a030f100507020a14010603060b01032901020115090b010f082e03021c060b0301090b01031101090e01080a15050c0d150801090b0f07080702030703030209 77
    0xa2035070301d80f2800e07182e0800f28018039079034800a44c804414001c0c0c60b269440c8040300640748591144107000d81d500464586a44c50b15a0b4002042031140200034030350300103a000010240076481c2001950003004140300565641d03003001c1c001c04d1258402d02c20b0520004242c15a0052584034040c0c4000007940c84034403e046d5035031980f24071456004015601c0042045180114880c40380400040035180180c0d0600c06100b83c100070b0050a81209491400c180b01c1000c4004500707403586625031048039180e00c0070f0340120942ca508105601c90345010480a03004650038003071401310f05c1c241422580c0d24000900609081001400040c8680d04081103046052406511154030b0300c0030211070341000e80c03020301294003108002c8104007421500d000c0ca458012030802c41da28121244020622031804c0c548103c1c0d503500d8004c008600c44410200c007500104000b084910414500403604010596a20003440003400c0003d402512521555105520640c040c0d030509500ba0381c1a00603401107940399600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 766302050 1250 766300800 766300817
    0x712050c1b010221011712070b04031205070302030f011e05150909012601020414060703030636060620070315020a080f0601050a120b0607060605030d092301 69
    0x1d001c01451504554494a03803800c04c0c651401c046480a180442140011a00310201106842c140d103000d68040641020312043c44da6034600e82264030500f80403043d00c41e149000c040c440d81d00c1d8154051440b8a1603255138148690700c40f00d022200c0041000c040210410984051241e8140f004201048400f1000711a0134240d0f02c00000351107040c00d1b08950480200c00041c0407640c0013620712001d60040301d01c002c524150801c04030f2189101d4500c0300c1c5000c0d0380002819420140700340c1c4602c000b0321b82d4400d21940c03206d500c00c00d82410020307403031003080c0c1c2c00c404035500c2c1c5603403202d21559040700c446880750b40385003190800c030406000e01486900701c40d01031050b000005c1030340042e6000b4800410900180c1e200d44d03141011348164400760650000024420401c2801c0e604202114450b0f180360601d4000152800031100c0a899510a550b41000b0b005c21044100203050b0808801c0c0c0d1070841c1030318100c4d0343c41001140e26611a1240000d0603103220300383d09114005040c08001e07114107144c103002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 766303300 1250 766302050 766302067
    0x306090e340317071209080d0516051b010905041401051203130e01090e0606010e040e0304120506010e180a02130902091015090e2205150712050c1b0102 67
    0x75a88440701d101036410f030000b40792410041205406840c900c4242401c05146040070402d560f19946403000c9406d020380040c41c41c14190404d04150b001940c450212009003140400c5c4030502c8400300c1c80240412150030000c2620710b061300581a62205003015000240c0c45c04c0200481c03483c3c070081c078880701e000070040c2c1034040e1910303400e010290426111600113945001ca141048406a40403581e2942112041c031030709a9000000309a50401120085410300765090950b05510540d0b02060018003000820f40400002098880c101e132200300020210360f580f240c0c502c0e03007442250a1006141c11441c0351800514000701c41d03c1d01c1c4200288001004041c5501041e1544070a4485014002111004000145070b404100000070944e1030310380c17a4a40350069a41c005400505045ca5000c8554040c0300140460840c909101c0d4010f41120461516214480082002594004001404914080406078882c001c05020b00c1d0701c002d8251502c81c4a4880b088442c05810a001c204e5400f00440813 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 766304550 1250 766303300 766303313
    0x902013c0914010c080703081b04090e0d0801030302120a14030c070516151407020901061106070804020609090a14070f1206030b0c0304080c0a030306090e3403 70
    0xc01003601d4665801050908001180790040701c1400381c10055210081c07000264403200303842c18194141032450303564a41c60086070101003200720103500c0c020007140c0021408940d41000c0ca4000180c1d050350b42c0300d5a82a0212011202404050b0160340200040d13001d21005000070002a021842c048005091041c1050015032065a9104409201142a00600130144807481e19101e904010107142890480752540220048602c0320501c404010004580309089045070715099000301400350b20341e15244090a050410352108100b4070400c00022071850180c120107029a03002001c00d41400126410440413840041085050580780d035001004055501388460243c602074603030001c480c0d03075184001c001c0b0a001200954080c207280080011528032079000d500900d20480c504d9413503803541002070803880750407a403a107940f161044000500d9416070011082d100780c1c6200740014552006802d035541d955010b0040d60b000c203c0350041140c0f210456000c0c00c0c40d014003c24109a07074035107490 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 766305800 1250 766304550 766304657
    0x160626013321051902091c06022203030912021801060e010f020303010f0605090315130b06030303041a090a0c080d02071a09040b010c1514060301090201 67
    0x2201080300c800c0e0019108095075180d842c03a4654960820043c5031030107400d801000c90380300ca50311403980081c01c00c0e0305458502c01e9800c1c91001c1a1715824007400d40c680300009521611200214041400b10000d0442c03e134801e02040b260507640c2e08000d079080206d480c2101c1001e8800301da100d442d100c142000388541516440c02030a99480303c0c1d81c445a80b00001d0310341d20f504050101150030420052102140e40401d140c2a1219490032940307440c00a40482d1604401c824145600742440081110146e0326060191400384210031400d216164442419a00d001c2074400070005806459807000145074020307030560215000003110900e4410b1b0b240c01c60b000800b82c1141c00a0381040c415502e0568040010000a0110030740644404100d00c2608015001d4412580d10964a480300c101c0c0d0b03a1f01c180844003401d9000700e28016401c0355040b001c0001d00c5108901100c1102c3c0e42c00180740d0f850706100307103600c040d01031712141d0503d940400c1d154003182100d80b0600c5c940c203609078030310704c011464a0007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 766307050 1250 766305800 766305899
    0x180a0b01030201020d091d07020a0c080601031703071704150204090b1806090106031a2e03020313110a03051c0e060910050d0e16062601 60
    0x8895055045000083c10700c10322020704000d01690720340402201e807088450320304071800310141810684610b40c2c100e0500400142c05016010302500210340c02a0204400f41280d1040c2c0c840209440c0384202000c2902081b2203c00c08554884400c01010034004130702c40c2e10a114035100d01030041110b5081c0d04a0300180c001c458095928105980340d420304000c000d100c12469000c42c002840d02000080c0044414080d0104040d1100b0480f088125142c401070103450000b080d203101c1400d554800d088500305035852310540900b8a040c941d11502274800c50b070040143c15403000f0300403059103e0f44a0421882c2400d5040034103070310300001069007030000390001100c01d14048000c841210004099100e0071549510801c010400c18032160341d05540d900e1035448a00b019074403003000854080003810f40a041d01e10318002c1c11001152280030011102c04e80d1202d4440c1000c0f00f4801c50074900c4003102204554201c2c06420060100020700d40792010184442c100301c48001c0707170201c619908840001035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 766308300 1250 766307050 766307063
    0x907050403061811060f070605040b0703051e150102030403050105010303030b03070602011a0f0414191d0d03050c0409060e0a05130c03110d020604030b073005180a 72
    0x18107008001c803500070310b80c000ba8004807200364110740d03881c0c040110460090140c4180030005d200c0d580c4c00e4103e030031780d4041504100200709034913260030803d42000b0100c03403000020385000d00194544445120342c98121184800c2c040c61961000002c6030800c94880d0b0f1941940701c1800004001042402007034040c4d0300c00d54002c280256040c1c01d0501d06411034101400303690414002c88080c90301e100044404900c1222640744643c40713100828001c0501c8407000360600c0705c0c0d8003041140d1508a0540030b001804140c02c1290b0880308040140d039040141254905420011041607540d22070b400041d00070809060340c41c03510350f494800c40f00310b82040e408803401c0801c0100304009000d07a88511035004004200b800b60758229940c2d000c003004458040140102001c0350500c126443d0595644200d50740036007070702d0780c451700e904000b00e0742c00c000c03283c0304005000207103001c15010b13401c101c80012100c0c0000c520354010349401d211000d008002c2070030f44000100e00b10b0444d8214100030160b5200c5c001c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 766309550 1250 766308300 766308307
    0x90a051f1415010f021f090807150c020c031506040911130903020c04020703120e1c020703020a050604060c110103020d1b03050f1005060705030c0f150105090f160e090705 75
    0x50500c440e05070b4400117540121026880890ba03069042810891a800028a103a901d1901c0c4076140680000600b000c0100030084041c521664003a41d12408190219a0f460004404140e56001c0030300940d200c0101d5480072941504046d001305506500c51801c0ba810303000b1013000b10328040043c402050001d5218811201031540611444040403400d58040d85032000365200681800084100b060103641d6483d10300481031010310020001e0400c4103c2807900c107010b150020f5503100540400d9111704013107540004c003840c0603411034085507140e480d50080c18071070351130700e250000000030402c0c141502040300803481002403080600703015004038858031940e041c400007411150010010030307165011100344040800c0c0c864087e01142d000700c400079a02c1819191107815070107040740320f0185218500f1038511209001c83c1d40c01c00c40d95101845400c90f0f07664070400181460560f4400100004040480c038203000852703150445403c00c3c03c001002c2410710307000c181140c40888007030300000e0010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 766310800 1250 766309550 766309591
    0x4020a030605132d0807060b0604091509050103030e101106100602150c1b1218011101140106030903110f100e010905030d18050321090a051f14 63
    0x4030070703c0c12240304a180041003514004c81d03051914603140d4060140100840c0b520308108050308201c140200242c00f075038949642d030440b071014226a560f54500c6502402010030710f0b010724031809048a0305030740d83c00a5610754205204804255818601c1000502d03142d440b1f0700c003000c1010038003070042102800b0000d40f034540c00038281404d0381608101d4900c3d02041c054625048000c1e200c031443e0882a80e40c45040800c105071908260b4040c1300726501011414061030060101000d80c0c00e602030721098140d254a11005080301e52541e84490906140c40060000c0c520a0707110010580c400c1c1092401002c942c11140d1401079800440d00e19607010703000e403802120b9180079030181c1440804c0240a140080c2d52403c0c0c6034021450781c040c00d1035445006800030340540d0901200c07150054281c036582e420400c80030520403440164803840c00044000316401d01400504014000e0300300000e480c12014103000c0b42645082240000c101a0b21040c0c1074880c420404050350290500c0c40080d0a40e00c1c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 766312050 1250 766310800 766310813
    0x7080f1c060e040506010e0c0d06090212090601180b06070605100302210a150204030c091a011b11031c0806150c0619060b0c10060b0f070b04020a03060513 68
    0x1181c204000403102c01080c00002000002e60034190b03050885c4244042c3d5902c50521500e02500c403404d01e40c5420420001aa40c0040c1e00500c090042c48085103516981d4000003070783e891080c0300b103040d120000c2510700030280e032031341c0034030210b100041c03401d07113040c2c0d0940310b032001c0d6001503410500d07812083c4000c0045241001e0f0118031003d035040c501c01c012100b0640241c5599521001404965541010b1210303410340c1d504a40141d50300400311140709484010540003002c000d020100030403240701c1d4001007907000d00d035880041103a0320807a18500c0100d0f51440c13040b031040006c0c00c2d018469a08490302901c80c0403039481c401e02031540c812601c1e140510821284264081620b12401020010502000800315800da80944090070700c03802e02c0071403450b0f240180450360100600300804924162001c0e00482c0411003811048070a1215035104d12280c0d6282c412280d070510302d54001c1002000064000740c041e58854001130108211a41d83e489030000d4940032101410000e0402500302d040200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 766313300 1250 766312050 766312061
    0xe0d061e060e190902120d0908060c04050a03030509030106030c09140606070c06081305070b0d0c020c030327130b0907020606031921020304080f010504080304030507080f1c 76
    0x31600703100c01440c10061141e104440e01412040c0d985504c55110006540310b10343c0c40c00c29030303003e4412922007102110004005130940d0040c4040c078000c810102d142082904152001c0e100c0007000070700d045296070f40a80301a4890103003160103540f100030000200d0001d607c520014108003d000c500d118500042102c9210000c0c1035a10405040c04218003040300c00c0300140c00d40d641ca003031404942e1500081d0748018443d844006010748503458000c2161008513000d0006131242c82c1050155041d074200036070304ca400195810307801d940b0500c01c101e021100d0300d00b18840102c1488100083c07840000114003441015110701c0307c0c07142c80d80041180c5040480743e503a803107a00f41c806084241070200000c1e0f120540b003580051050000740c82401401800c0c0b040c0d80901e81c0201c02401201034015010352250403a201d803034182c0c0506405071101d42c4041c0102480369610211072440c43d030310b940c0c007aa00d0341c11100c820360b0710070018002038044501c4140285690144681c3d840c81e1864405801c60030340b00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 766314550 1250 766313300 766313309
    0x3060c1107030f1112030a03020703111f180804080307030e0d05030d0c0512070905010e1806190308040b030f010f180b270a0f0b09070e0d061e06 64
    0x203015007010004580c00010214203da80311220390790500d8040c0c002110203401e002461600d001c001007440c00150140e0050400c0c3d031186d10340d0b202c042c1040d41c0194a840c8200812400504080249101000c00e907101642c04000c0b03416400c80e080e05525100003940254000824961001a01c04141500301088c050700310000c94150005400542d551612070003005c04602c580d545031481803c1d564050b6094030004141e8074124205803510210080c860f107070921809020a1212141094a04004031000384015100700c0925850b1280b10605c581760740b01012140d40f102c608140800000c60610040004200d8421503984a00740040601c81441041c0e214000e8800501c1d400c1000ea420030107203441c0038500c2c407400600c52841d5000704007031080030b5803500041603001c0c6030b150100e035100390340d030f4040c00d43c034a802c02102c030910002c002102c423110149940801164001282a4401c10500303200d1100900680c140700b0302a9242001c0d40c241c03107a405980000c0d042c0f483d003244045d202d40c00040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 766315800 1250 766314550 766314553
    0x3010f0f030f0b060102120c060a0b060c07030f15050103032312070804060f18231c2106061d0a0501050708040807061106011e050405180703060c11 65
    0x440c910340d10403100b00d4410300010408480100014036580c028419820030030b600000c4d5a03a41c2d02032880450300c1703940444412a01c1460b104055000e0708142c0e064a112202c43d400a0103001c3c110b48815070070302c600580464040d0505841c01d010701d015030140b64000d5200f52141c2d540008607240c0582034041c50070304003006200a003d80080c2d0a5000e4034960002d4031810004c04a13105c90400402402c200b40c162445a4280000c2003182404114641c0100c0e0003005250440a01207103128401d1001c1181c0b0714003544045901e400c0720343d40400003003040d84d180c20000d20052106440600d049041c180c1c501050743d44800821a0680006840d401c03010f0078102d0841c40038400c8009545100d42d405428100400410b4200c100000441101c0c050000402202c40150f43c6a0300100f29122103015202c1c24002c00c4000039445002741901c04416041c1d070144421a4180000d100c01030000401c0544100c04020250b402c414080c00154080c50083d5800314810104c2c410180480000b1606101e50707 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 766317050 1250 766315800 766315829
    0x120c05061308030a050a0906110a030c111506011b05011a091e07090513050402040e030304150203060a1e03030305070e06180f090703060e0c0a0e10030e0a050303010f 73
    0x510340342c03c80358010900c110010319600c995210b0401071005904c020030191403e1402c0403058011406480c1c000b4041d50103100340384200340c2c2141c500100c031001c40e580d9400403030b11a142c07071089045030764099018584005d01c404c41c44035142c11400d040e0010b60703442c0d544110124040301010300e0840543c42c1680c4c00c01c03460400c0140c1d1300850206480e44402c0c4510346020402e107900c2100781400410000300b040b0780d01d0350174040303440003031a065030102c0c07185280c0000d11000c0c00b004820350b449140c0007114042d640c00502e860318042d6100514140e8031011046022600c05181484014401045001c0d000414107528019089450240c02c42080c0f05a1002c9043d0700e903035a46c00c0302c0d10601020520b4040c00d451402080821000d505403950207002d04041003803c1d50b00d54005000c503042c084000909480b04a040000351082080036400110340710034445180c104510040075a40203480c0c000342100c07150200c1ca080004a20702103039150000801040900006100b2002034520013149070300d07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 766318300 1250 766317050 766317053
    0xa0501050708070308040305090a03060f05160504060f03110f090114270d080318100501060e010302130e1501090807062c041b1b02150d09120c050613 66
    0x2070240d05002410003042c1c05c00201014421401e031040c0034006801a2800d5880b40342050260810045009080d40b0f06800919840c1c40000c0300021600903440e40f610781070900c002104e0980d12510200145070b154000d403286481e140006011200d581d170000d0307440e10051800102103038022200810300c600140310248524500c56110046e0b50503460f080c0300701c2200704001c2a09a4510741e001781c40400040b0420030064007aa5081d2680c0d96002c0a840814500e05180740c1103400a00413000054924141c804295010342c4c000e020315615525140303407003580c03038280300f40050f0704450b0343c80c0320503013030740003441c1540c1003541d000240004c20b000e001030314140b5800415140301803004030344000c031002203040c0203011100c01c0d40c40f0000182040c04a0302103620f0400234100078185180000710034100b21a03212195a1121054a40c0101111020b5180385041c8206400209905100c640d07210080310020710147d0003048440c4942d2580310031021a82403803824504010106046030702e04900500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 766319550 1250 766318300 766318313
    0x5010315030c150c0f06091b0303091809060606030f061a0304080a0c1a010e0c1912060b040e01030c050109030b0c032502070f06030605010e0603060105160c050a05010507 75
    0x40960b450704007602550004414101c1300c9030010b0030b014001d046010b41c40d805004194110280050003021620074020b90103142440c899200e01c401f41c00100000390034419601624031035241030301a62004590281191900408c64440b6401440407964407403542080c032601d806000010300020030071150000780110202450b1000920003841c4040018410086034080c1320401c060a400405a555220ba011138036030740b400080c007079424211184c0c400158203402010403030f4010786403046501480c1800c10401d03103903131010340d020442c038549950307010803407402e03801c00f0300000e1104882c0340b14154554140600103044a4000c18100001d00d6410b0020a10360121a90490902100951386e43e0311001c0346800c1c02220043c03810000c0303101a02c8407055a00046c000182d0700c521710b03c0b071001603842d08207070120344c0203102d000e000c910720b042c0c01d5456103000e201a5078014018100740e498a0601d010780004215000d000b10f80000b0201414003840c10300d800c0031000340c802030901c140b0b04901e076107032075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 766320800 1250 766319550 766319573
    0x190e06090a030f02011e0804031407030c1401020f0f0417070506030f09030f22060305090a03031517070f050411090f032104091116140102040b0703090501031503 71
    0x9000c902c2c80c41034401c2164407a030440310810000007070789030410b0f4100c0c4005080300c80c00e5605400081360259030003c000cae5560200c0e0102681501c80e003032300c0112a40d4440841500b03608103080c42d58207110007901a01a90002c0c40324001068907165180d0501c900c140c0b01c41401c1030202e00c43e50040b0b00603c002c4e12104110794000402c0c0d06441500d0703490000d01c52442c03282c031030910004000810014443c060b20b1440b556101080d0341f0640e0b1480d142c3d070048080710411115244294080103a05021a0190b40054a00390a101c5080380180d2561351030300070007060801d075030460390200008020300c402c40f41c5008042c1c0012141804a41403080398030300a80034049450b84204042081056103a034200855001c1255298001c640c050003203882550640161141006a03800d00410041070310750034003100c1592030681103490102d24107031100c2c0500c180008480311950f50801c4046114030014001d000054440c0e907400b8032060504000501b55040102004001d0201850500000382201d640307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 766322050 1250 766320800 766320803
    0x11d01090c1208090d0f2907270e010f090b010503060f030a0605180708030405130c0908120703030605030a15020a02010209191401050309061f0803190e06090a03 71
    0x140d42c84800e040c240203616203d10711240e0780c00343d09204081c0401c628003e440c244c0c9402802c00e0100303900c8481d0140722035620080e40164000014000a0400c3d005904200c03485803200d014009414942a40381010201074200305000909600100124038203810403401a2491901c20721101e080784001819030700000c3c24141c450b1080d03400c00c541545041005c136610340c0d0000f8007400781e4144600d0f400404d13000341d00041c0b410b0240107004114611700108035400c9581c058802c80210040c1c9801d98000c101c40280c0b40c1c01c00050f03040c0040c1c102001c00c07030780415000300208259140b03403c2c903010302112101ea0046001390002d0407207402240c1b1903d00543c07172212041c3e0150396422021000c034028801c295075039902a070404141e0300c003800303010044d205076262903000142e000c0b1a5001910305000441d601c6101e40c0c0400300107100c000c100b400c2100360050841b034060015072580a04c07800c5801c51074800380034a2000d04c04524855008840c0d241c3c1000c2650340500d4440d50344081500c00303006010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 766323300 1250 766322050 766322069
    0x7080c07030e2403180f03073f0e120d09090f1d01050907050d02060a0f030e1f0c0903150b011b030305060312090a0b0f0d11070c1e090c1808011d01090c 67
    0x81e2028401004000320442c09800300b1209c0914124501800d0586d2200030341d4051851400c0c610086840064028003054540e140c08881341e240403002c41c0a4003170030180401d0f29445055103a03030b01d000140c0ca04003500144001003000c2c9454507100d444c1c0205035110034881d01450a04a0268540b507040342d550b10703461729040c68403090994082c0c2c060842032111580500c55490392104501800800c03a8002d204524203002d001020801151002e0080c000944240c40c03071680050b2403441e55010102d5900b042c10091908496441c2902ca0b40030341e0380e0290301094442c0c04010403490148940c448a0f040300701e40e903040c07001000c04109003140070300030305160b0030f00000c405001300321504c1610100170681c0c00a201020100036800c0b43c82c0c0003020100c420200e13103000858448140d0f40520307051721460100c42c0c0c180e80b500350241d010b00781c403007159010310224081c0900456192000c84002c1c100f4040080349500b40c5490001540c40100e40032481a49444200e00008000c00250804c4580e03003c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 766324550 1250 766323300 766323353
    0x30040209042a03020a090e0c011b0b07032a051602040b0d140d02010e031c0b09150a08030c0312060105130e07080c07030e2403180f0307 60
    0xa408554200051040319020402108400010340401030b07400c1030302d100f981c1ea40d91140c1d03115500d01c10303036103060280540c1c1c0e044807041400551117102e403141d10298185100940304039503100d171114045c00307a80e068002a1600340301103141081c150401c0300300c90180c1865048413a10403000303001c8d0160400e0240f10841100000040d99265041851046c0d002801c5400c407856600d44007180c0c1c94016100d403034501801398070050041c018440c1180d9003091001442c90500d024900e000116903050314103000c11b680f0001110307503481e020b92007032056428031080e0790340302400f404014900000f54083c8100ba8010044055280c0010007541c0c94400500c07040324041e21035000683c0e1900074007961542ea40e501280000380074014090b0180103001c1520780b00c205449202100c0414400d401d005004180000f00c0002e01d0308040818034a101c11211000803103868595503c100c0d513000792180300c0400c2c40a18a450600740500c0040034038450003005600e0b20405a4402400b611110300b08104600c242 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 766325800 1250 766324550 766324553
    0x30204020d061d0f070c0b0103080d020d150302040b0f06090904060608060910050c0a0c14010f140f010608040506041104020f04081e06070e090a02090a03083004020904 74
    0x640010010740010035050424a8000d0070314503e44100f01c030042a18103a00010609250040143c882296081491a682e50782584c40703000195100c031030600c5035980d08201140540b8503a1080740c5014000c21203e010b517a1643c010401511254071445200307a54200154105a40d04d030104e650002c010b480046107a03880f0706041008000c030380e1052001b1700612041007006080841c2e50464018241c80811442e01c400b02a1016409540b0680e000700c0c0d10000142c01003074204800c0900f07150325a00200e010100c1c0c2c07102d00181e50f4000945201564840180704982d0840c1c4c0141c2e015114506e44101d082c549600c603280d0b0742d1400b40c800b42880c0d10800e50b840302515590111140c1139001540c43c1ea840d5502c0d200b03160b507004025002c00840d4250742280e0702e000380101d106405850701c0d954100d039414855081100c804000307000c8075213082e4208000c204940790407120000031802504540e440e143c070098201043c080c1c071154800003d00d805da1640389221130040690300b10350107583c0401d10390340c1c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 766327050 1250 766325800 766325827
    0x313050a200a0630061e0e011a070204090c0f1e1509050631081c1d030a020a0914010815010e0402010e03070e060102120405280b0c010204170a020a03020402 69
    0x61350856050106550455540861614101c84c1150300c80c1d8080f000613031f80c82a0685e01840d02703600710f0015060800464025141981210318920b0190090f003030a80c1d55408000f0780590a41d00c81a00d44100c0c42c902c0c5c03090302c01c6d214030070000d189030306500001c0b281c6140010192415402814440c460100745292641007042c496150386e2140c02c0c00f400b5401036051004030010040c402d00c021442900700110198142181080040f80140c580180c910310060b00702c002c1210440104e905841212004400741e80d8074801c0318000c14156000140e00c402190524001d4181600302c44400e90203d4220302800514204040c11110340c40d800000310384a030f200403070b0b24180d05512542d05104081e804602226010350503400303013100b602150054840c8190380310507806688201c80d4007070503203070360703506158207171143c00346440c0c001c08403500b0440e22458640300d030307801400003a02c5603903011406011429004604800c005120001070440d801c4c075500003122428a400002d00503a0042541c801000300c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 766328300 1250 766327050 766327061
    0xc020c0a08071715090318010e0f041806050c0409050f040c060f090305030a090e0106090f03150902030604051b0909062710090c05060c030313050a200a0630 69
    0x150052404c1c0b1600b0980c450b11394070307003007030b44550a90048180b9610043d07000c0d480c90003030762102805071244142904200001071460a914503002c0070185a0540010564031401307126484a0010944440c105441041250750080641c019408a501440701003109214404100c60003441c1180d0290040032045495880c1540b00604030f21011403520349040e0400110000e54250400241041e070361264201e650f881e20f4800d8040e21561a0000e0002c10400203c2d444141402c15000ca0080b03416404285008800c46060b036641e001091540b00c1407240c400c0c800389600c42158102c08ea81032010b040c68541c480504500510341d00d6800740403400012110030840380b02c40780190790091415810050142100c201c0854028500d500003084514058068501001e0b000e0011030942da10426007442c0f4074518081596107202d4084010005140100358884840c2e044808283c2c21120100303121480300c1c0c5411400a0100703004401c8440d44140300c0d4101400c940030f8040c1000711044494030000d08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 766329550 1250 766328300 766328323
    0x1504020f06030f18010b24160819080705030f1906082803020705010c080c0102031009051003030e100c0803160f0504030215030a1e0c020c0a080717 65
    0x20004800c02100114603040280300b440c0c4d00c1d04540d09070721854604c07401c9400382d0b00c40c3c80c4e01c488100c0c113036403200b424112101100781c100c8110034036004c51f1081141e5084035805048070002000503400950b80703000c0f044c449101c0701600300094030381041e10b00540903000080011008503401d50000340c1d506503021400554080d404000c10800c3c0d116840d01d81c6945008a208104007003c2c0800300c8414181c035400819181c0590190004074100f5004583c8100300d86000d460811080c02a241d844a0078030003036010b072a10740007141989241c80d1030042a40c000401700e800c1e01e010510108007298005500d00c0d0702e04811249000c00030715411040e1101c885c0c111016001440100800c0100210f1343c034074001c0c00f40c09880714104000000b0045903103102d00c0c04000c2d048030358040c6032000d602d42d03d0f000e1034101c403112501285451001d20602cac00d03140744c0344101d40300341e4441074030a0765250140102019001d040d101c0c0411303581001ca8084d640c490520404580d80c0240c0100ea504500a200d141100e4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 766330800 1250 766329550 766329559
    0x50d060905013801080906011a07051501090f0513020f01050f1308062a0304031101020a0201050f0a0c0e060c010209100801030309060813111f031b0201050103051504020f 75
    0x3000501440441c40e03120283c802520b1842c00c40c035003190300600b00144203082040040585030309001a00d200040d103000200c02e1401c00384039450004200f404080416191032400002d19071400790a141503941c034502d0104030600e07040030320554003205811410b40c070b40c042e0b401464400d01140100c03034512070040e12030803003007003c265179040a0751840040c08403245501120340b5510b0341c401e1144076500f140c0160281c003003105132103e807114441000d154002e029042200d10401c4403e03001d426644006130180060f5550400c000104503482e200c41c0e00000b60724001c1103480b21000c0098071000b14059101e220303843c0821301805086094040305d55042c00a007401d4258908600e000d400300b0000e0000300d02103800000045582c901c6204030034440c0c40c0840780070603910450346850a194411160642d00105401e051881001d4541030304001c55070140c0d00001c0700348400c7e0351895032051210700c06045904001c0108041503001915409440c030003900c2c03251607102c610000345502141e06119421 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 766332050 1250 766330800 766330841
    0x110702190b130305010e030c03030f15120c041512110a09021309050f04120509030a06050106050703140c1e03070203011a030f010e030318070812040510050301050d06090501 76
    0x96102e426584411030744950001d00030b60411929207512030180001885c041c1d0b00500c001480c0c041f001c0c1440350452428204140c070300c0c0b540c002080c108200400c240c002580000d408200d0350500344a00380c5152142c03100034089a041000c02003310f0380300c0d00064654070a0381c0381701c1419a10719a0120081c45a42001c55035404e500488000500c0e103485080c132101d182031700060f180501c20000e0f0f4030550780881e1084010315100b505484a030400c110098051080b01040000030390300d0712074503002e8645030711055120744181c9130041c6880740d010145c80041500340328200c1d80c2d9030700083c1d20703606a1a43c480301c122042d01c2d080891443c001c480000e076140d030030001c0d5243c0000c41d00610702c80c8d810094041d00d409860055004e400d07a0000c181d4549961b00403c000390800d40c6000151909102c0c4074152401c05550305013492130a0103644a0080b81c4c0c0d00000c2c100300c2407906c402600c1d080700306410014115850070001403000d003090b140c050510b41e150121202000401e50182c00310554102c4135140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 766333300 1250 766332050 766332067
    0xe060c01060806041a040f1707021009081603080a0509120303010b18090709140301020c1501050a21020105160803100810020403051c090f121104110702190b 69
    0x10340300025101980c1c594501c603074000d00384050505c1140705d5a0400c004507500c41a6903500c0700105001241c07150400024040c140060399140c910b92180302da50390751120b42c01d04140d20b41341012541d1002c10848107030043c04100140d01c0c68190b50a89e0b009003051074884865030082104040841801c0303801d40030010021840342924405801002107540120b400d08402d0818005a008169100004520311203c100445011520085400880600054100819410204d1030701c1010086d030f0f10039400316001480f041c01d220016400510200b0718014007003e810080002039449003030040c0c1044070014824800d0500380e1212500d43d42d201203060794900d08581000d001443e5401180030501401c1d1405003403200e41d000340c80c04e4a411a000d0300051407040424501140e070075107150180400200300052060309415540002c2c07895904022500e155481c0c040c40c1c0700340408615100e031386441121a01c8420120541d003e40758180d404680100c504d1821948071030766940020541c04000a2000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 766334550 1250 766333300 766333303
    0xe070b07050d12020913050421030501080c0d0c0605090607120e12070501020714040e030c0d090e130204020711090c0c0615060f0d020403081308190309060e060c010608 74
    0x80000010f5034500100541900360b1205034454440da00c2d501c03150780510300311280c0c01c5a00c81c580141c4502403078041040c158010301c80480c00580c03008080380d0760300010000d580b01070007000d44900d030440384110a0112950785038500700e140e00600007000b001284d0001542c0b215070407241c2913908100349068000302050000c02c002008408940102004012480c0a02c0e00264803801e071a4160003801d8650f0404814010360104540669400798440340e911172001030510003020030061103000703042007c0200700e010300162120b511150011442e2010480d01301007251003070802c185d044bc1c016039200d2507810048064480d609180b42d00c66204000e00101c400c02c08028000c1082e050203646441d60740c180d54a420f41e1008207055044082000042c84810440c03000b00780c280141240141003e44980790103505821440f00340d0210b4030800340500c00004100201002032008001c0c000440031113640080032101c1f14420b40044c010b030150300d803013569244c0c41502e200c0d107010b2000304000355031045001e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 766335800 1250 766334550 766334563
    0xf0e040b07211e052e0e42120a021203131a090105160f0f11061c02130b0c06010911161205040b070f171c0e070b0705 52
    0x6035900d5640c0e20104940e000ba03009103031180d481c2c44082054281c264006008000d200f0109501704888240041004010b501e4401c1c05070071001181103511410030b900851040c1d03800c0f02500d03a503400c030105012901c075101d920720009a055805100c06a2664605454085021030003940000440c800d1220140000090288000045580b184003503550000354003200f015180516000801c0080c80182c0d40100700808050810130b014051104264840000c88022210200c41d807000d040d0418051001d401104414144200d9580d0b1130300400f65802d51a03d5500307410740518030f8020448540300c81c58511513000400110860540c1e0b080e400c1611922001d09000d01c0700401c2ca01041036107501d0065017a512117000c0d2203074080780d55074130352202c0c0c1e03406e242131454104000f02013002182000265010300342c070912542c4c3d801b142e0f15807440c014800304005540001c00e504180304c0c2c4152043c00c5904500100300010000800c544006065400d0061580000090f500c000410800b00080001c51 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 766337050 1250 766335800 766335821
    0xc14130216020127030f0f0b070201090201120204180b0310061806080c0603010902130b1803070801110d02030405030904140a0b150703050a090513060501090f0e040b0721 75
    0x41301c248003055095031000034000002c0403a440b60042003480080e9900c4400c1c0c4442c1d0141408064100090795042d4514408a580302d005035140d2041c1e50031560003c05044c02120160015424a818499a0100720610014000c03085455000b030004c030351018004a20b00d01c14080c6d0612005e07440d4006a01b510b60f03001c40c4000900e1420000041100001c100303c54407010080c111442c603468064404003a4000381030202c1220010341000a100001e40014450303225644010a5107420345802c05050030300350b40c4800e500740d05089030403030003601e92012200008140c820068580c0c4850a1551440c0902111107400070b10700051843e952004840151040e03d0a100505c40c402414040c03042d00022046c04010510052050100080c012030181c07881d10324038900421000e99620000f11500305805007100540d030b8070071080c80696482080500640b0312000c2c45043e99192038003030b40b101c038002040640420008008200c00301c3c440c9424400c2c94450500c00d041d680c00c800c01000040070030440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 766338300 1250 766337050 766337057
    0xf021306090f0f120c08190203010f050c04120303020f03040b040c0b0913020307030b030a12120207020303040b0c070b0309010c081602060a180c090209031204030c141302160201 78
    0x1a07640304080c60b2400d5850a1440c0d0361007030f1900e640d0a000701e8010808643c1054a13100c08030300300008022454030307200400c00c0304008200314010b16003112644040007040d01c3c01c0038100580da0706100304890481d00300c0814910002c0c51424118024000c41051301a01076000090001b030151120215004a0003001c84e0303403c00d1baa444017002507100d10300d002030b0045042480711114500c103034003660b0300c47e9141c1400700b00d0203c03100019003003419450080701c1e034013520884000f0040e400ba400c0d40103542504c2c01180b500c2c0aa0300003940c0ca0141c0c0c458500b0202001032420401441405071000504059610344e0316810100d0406000c0c04920041d140090500720000b0a03000702140010040d89054002d001d2503200c21000d0400781c0400c55111300c6110000e00054009029035041c003009001030300c40142c64004d41c800301401c244100a400e042c9402c1408140046900652190111404580003080010b09000801d010003942010020700314804100460303242902020300207042c1c0700f44d9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 766339550 1250 766338300 766338317
    0x108060a0b0c061e090a02190509040605040b0709080a081b070f0920091009050d08070c0b0406021203060409140c0a0e01080c06070f050115080c010f210f021306 71
    0xb030004c100300004680c1c900c2594400480700f8003605009140c0406000286e44a041c0d103600d8801003400311000751412514150398208010500540d4190341c0c1e000181d500e0400c1c00780707141c00300d040c2d03030307020340c040094443c00000a40c0d000300c0e412200405100c001d54810f0302c0d0907555900070365260b00418840d41800b94105005c460740352a681c139881c0701c586c0300c62054038201381c622030901010030000700021092112008020802d65503000c1708a0750756200b082c141e995a0003d1034042c9108006a0041089007424801403180c01e0f000b2440003400d16440c069140c1301d0f542d0800160160018400c040d1840102d4560383d001d544003c551492564402d880c8400c90990b503d80328817005200344a00b054513000010503007403070300d0044001e0035000c0c0564108103040c0041c2d250207084610f046054035a41150303c03000c000c241418048841500d07402d00b00b00305000388049001d4109001c414592520070b08558910b140c98a29500c00110364403400d800b1519180012101c0181c04102e0080001291500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 766340800 1250 766339550 766339591
    0xf01150e0906060a030f050a1502090a0902030f07080709150809060f04050c01111006080106031e021e220606110111090d170309060402040b0f0f0108060a0b0c06 71
    0x1410b10701418029040d40c000742c3c43c40d15400f00860040340119118000c0b000361101042941c1801d42c02103a814000580c0d0b1040101004030b10100c6a00c0320641764010300c1007002640000301050352180b01802d1803032955407040011100702105803c800000342080140312612644a00c1c440d11807892102200c2d01602e9104145d140d020f002c0f40c0c020602d40c4a28950702065201c0e8042521342c2403084103d40c80c00721207090107026281e841e00100e205a56480d810001e1203815203551614620302c4204801c001111b07008144000e5034680c503a10000511004c00b50180c4541c03030705805005150998a001d55a412010400307080140f08010000d001541c25000610061042d100c0c520000c0d02000d2030b18031000140010741c20260410b44045200700c1d00c00f41a1411240154440c0e40c84030701034445440e191040004490b8619030250080c0c40c0300310440d80c0c40c1c50304001041407220900300711344035a5403107000813020f0080d5000b900e14400081104030015800289a074020301403c140c00b85d202004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 766342050 1250 766340800 766340803
    0x501061511160303321812061f08010914060106052503140c0c01032304060c030e1509190b151c030c15020703051c0f020f07140705130203090f01150e09 67
    0x947c07a0203034503422010229100d07212002d8010040c0106080e501042a5505005401c5079480d0320705541c82c032026420301014540034054640501078034200366041400f000c0c0049100304401d00001030410304204c105c02854056882e025542c02d4185505556000080359992915908000039010a0410a502006c10007810030058600c08654107160140c1d0750b900d480300a0312040900c00d0074550f071030708003107000c607000d10010f1026404410042810f0070300c400468506099042d0040c00a0900306d254400104207150064010080304c2a01c3c4030710110a0000c0d68070f045003615940c1e00c81c40b050001c000c15030003a403170038a800d0040211440c1c272011105408160710416034000c000803002c00c462001c200e00c00381c2c2121540c101c0c0c100000d80c000e030a0104012644990715210340d040300422480d081200c103d600c295480c0244029001c1b040c40d01020612000c0c8518a540304076030040f0024000b00030420180c18480300c500001c2c40780b14004049450522403a01990342c140342a0000180302600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 766343300 1250 766342050 766342069
    0x2f190638060c0d030b0f030303090303100801050601090e0601030f021b19081614011109040b0d05031c0b04091103060c03012403020705010615111603033218 69
    0x100083c2c8401d4603440400c4008281a040d0380b0351145e89082003071003644013040a14454055079004550301d0801c4170500501c51815801104581c1c1868101b21442e41d00a1340801294440b90081510752a0200143d002e048a81071945030648040f07001450204140007542d110011a41a15190784d11906416500e4903030307100c090a004000c10251400704010340fa41500580144d040f1a07a249490b1a1a400d50fa07140201c1d4202400101e01d01e16189490301ca00201d003102120084030104442d522507850b40610709998011904980c0141405042900440180c490040040021002c5880e012956546600d0310340e000e403244800080392003e00c0d404983c180d407002c00000180419442002c0f00011500340003004054081c09102d002a400740039a0000d00804170180030b081d0141070004142c8010368504149550210200700480420180d5040980b9014135015404903a00500b010780d00c015654001014454004c1c2d084a824a08002d003041c19081c150603a16244d074401002036015 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 766344550 1250 766343300 766343317
    0x20180105090d02090702120c0105010314061b0f040b0f070308072a0809090f06090603030403030503010e060a0f0b03060a120201021b0a0909032f19063806 68
    0x18440d41015000d490000384c01030740914644101c405460b980d00c01c0c190f40750042c40348041c490791500d00610400124090400c2c3c051014030083c009850010800c07404141c034001034522041000900e0725140c08140d040350050030008150b155210505941d071007a41c1e005203001d0f8005158900410aa075215011206029031007a1071400d01c0341c220120701c9844102003508030745062082150070352030740f500c2d0041d0344682a8034201c14818607085d014003115000c020250f82c4250801c110505c00030b50401c0940781521403c4100403101d6454202080d05942c498010040d0b01031205800540510032500643c03041c601580c4000203a40d43e1000c007070034110440700003409600300050380f40c02c00072000304003021110024048004c03142d54140030812200740d00000d4000581c00304000844d0444815982e10303012810007034a024a132016107003601c07143d289103410840b1101440134010302c14030780c201c82d840b84803072106045245228085400c89641e02506040ac0040d45618642d0b2132804105685000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 766345800 1250 766344550 766344559
    0x506100b031b0906121608090c010504090e0c061207090501020703120c060f05090c040515010c2306070306080d030c0e2403070e130e030a080a2018010509 68
    0x25121041c000d030381c3e0450700c1010382100301400600d14400c581401c0354000d9034000f004184072010404010300ba10380c01801002203910510a810242c0d901504440c00c440907460001007504c3d014580c54240141c5000113644140f01080c0c980c0c00755a40c1d40c11900680840c1c07100030b07080d69204016611100184805040c0c00009105804120700907081c94030f520744030701703000070302581181d005200b110b8040e80e90804c0da90103216584000e04091181c0c0342c101c1a1b5107000409218400c1c002008130400440040c240d069092568016400f2042030242040303a54090364124905858020020002c901c00e01460b441442c1065814038003070b1151403062400c5686c1c01c40c00148078010b01822100c030400307103003000500314003c2071700b1805800954084d8038140e455243c40e21540041040c0644541c0081c1c41c018a4140d0381003006400004464061005003000c201e1640d88400480043c030643d03607180000b0074040820385c0c0e900c2c0c001c001403d10f00c05031802c0520f41000d040044655015028030107401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 766347050 1250 766345800 766345831
    0xa021c08010b0a1b2009090316051c021c0809070b03070c060908090910140904020d1a010611070b041a09060708030406140405030304032304030506100b03 68
    0x18160300b0b200401c0c03260031900b044445120400200c4003031101e001800e0b10200004c20026030030741c80c03800304a4451102100c8000b800c1c01d03c41d4520f6107d02c80c001d40300e0301a4000107a514100311092110015090305a0525409268102000f948500d001100300604001d60710708568030038000da0150f80140d84013001400c4041c00c101012119502c090034140a0141c0c2c00c000d1400550306014030083c4070b10560181c0c0d190b02000c024010040e0015046451001d03040d41c003800291003a1004d600c450408a4104102d901c890010442c00d000400018013640705413407081002c256001c07140c50407188a542c50320311414412001640b078500710700440240d603800300000c118a10180c44c1c00b00e007008555100d1450104400002243ca510a07a01100e6030500441000305000c0c9900c03a01c2074465072010520900d2520342d81e8141c44c0c7c03000800003028000c012001017080115450743c1c42c1621f84802a45983e9a128101260394134008c641c0709490101d40240402c000300184152030081a200c5410310301c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 766348300 1250 766347050 766347059
    0xf07030c05160210141308070f0501120f0f09030309020f060a0905010c0206042d1e050915043e0f1809011502010b1e1c170a021c0801 59
    0x15141c0c1281d0040041014045d603821501c40f500b030090190f440005015a08a480d2103003803400c0243c40e81c84000040c00b0020304108030f036000500c4c03641c15062581b0012319a210391300060002e00280030000c1c80b00e45018510750403da010361141485c3c500807103414868100103c20400c0c5ea2181d182e0940000d098002d00700006e500600640008034402802c203400c0c01e0300e0f2203048026000001407007100c1010003040d07122000112610703030040c085040a5488601208000815801940c0700b200d00800c210300004001c02c01c4540b0313164900c0f10082051004e58400941000d00d03001000141580380c0309981310442200b80800b10313131a03281900315210b083c0034451340300e80720f1078028040d1100c00341c100010a0490340c0d03590403114041e046c40001d03140c80300d0b41d01c90024216401e44002a0081411608100043d81040421140c1c610700322800c485070b849003140e0305038207030048100912181c00110138514511811018000540d041d50896520034800000c01d01d00700156101c0c1130100308128018072 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 766349550 1250 766348300 766348309
    0x201140c3c0405180402150a12020d09020918030306130e0d02010c030f02030103151130070503060901051e0a03080d0c050a080a09030e181506090a0e1e0f07030c051602 74
    0x300307002e489d0038800402a4801d6058090740e00c02c00d011f450f031a80d5000ba100c2146010201c030f40d00512484587c4016900060819a072417001509003403040074030341100780f800c0f403580d0480080c034004907059072150f2650002c068040c107100c3c0c0074900800c0c00d03e42143d0020355035200356412030f90010b642204800d00c05445000400c040e1103034283c007a008214908900491001c4912500d00301c001010289a0029222514410280c855010850200140510380c2d583c5c0901c0340c10b503102203908082254002e6580340c078812404c04d072980c1150b6203d8002090210a0000d40080c00402e1028010741c01204812038140c40b03202095030100340b10001168201c5455402084c0261080c00c11503031001d4400c1c000b50004454904144100861004000b10308031041e000c1242e008c02030b92000e090803d200001b4090703c3c158041c00401c0030360800000c403003e0040b0070714401c080400584143c40d0400d000c1c0700618040032140840820700308005149050311420446210f11101c080c01000c4000941c00c11 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 766350800 1250 766349550 766349557
    0x207080d03020708071b17070303120902011d06190503090d0503040b0103080306060d110918010812280c030306050307060815240a0201140c3c040518040215 69
    0x302c0c1d5421098901042040000085807003000c51f03100103110359859850001e02a04040703c1c104215803e00c0c0207800142d0b04044009620071016840800c40701c1e5030800b00e1080c0c0100e0403007814404485244038a087d411000035805001000180c400820340054296041c1c8410317600204811031440041001c103640c00061600010020421441e02c2c1034021117806035001c241084140b18000514000540780880420f00f060500d00c2c1c005c11250f00d4042c1d4103841b40300304400d01d0580c0000064200368500c08035a241c20f05100f59a007156400e500741d10050280c480b8801c100d000c00e1408902140707078900040d80c1070072103055690b14095955880700c5600300700c420101d0703e038000c000d10591610b411182824040a4046050b101c2d0700c41c81100c40087c21f6400150000c10b40180d40000c1c0022200907408890566007070640741c11074141e0380460f454088420100400c0711400c886181c0c502085901c0041085610888907482e0001c0c41e030320028043d01e41078400a41c041c41000700d1189050340903018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 766352050 1250 766350800 766350833
    0x806041a0a06090f05060f0d120f02010b030a0c0305121602060d0e100b030c180703200403150c050309100b0a0e040606032603040b1302100207080d0302070807 70
    0x420303010f5452580a007074640c031034040002c1540343c2d401c000c0f080c109003a041c070044004440694400850f038a8604a0b00b034154400003c2002d0900300100c614000d40201c6017904002c1e0841700718180508264203d82c40c64081154107000d802d2003160f96071300d20000d40d07c94400c42d10079150103c50990030821203a2182c201d0000703840d115030706008902d20611540c2a200f00e0114085015280c4200b0541443c45001e0114400d582e603900c0c82808214421902c0e50042c0e00f13003000035080400e000c440101802e50650b41c18041000100030003041500010450411403e16042c040b0140e8141c1c20b0b42c0a0204032120141a40005000d956548840d0405072181001410a4480daa2100c02e01c0ca070300d100840d800d8a0064503410b0070010441030b00c04601c20b101c084c040d040c04c40c000a403011100d078440604050818801c1c90702003000d450351017840c129130307507402040596080e40520019403100c140f40300c1c0031928080c0c0b481b00394019009008840c902070703004642780c3c50035000b60f58140846c800c4414 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 766353300 1250 766352050 766352071
    0x61a030304080c0105071505150f0409080706021303051b0a0501030501060c23070807080f0607090e07020c1c1103030309101a12161a0d0902030a15090c0806041a 71
    0x48180190405105440c01205400b2227042d6051311f00041c000d035940e00c03404446c011817501910201180040d414ad42c0210340c8024051780e85d040700a40c4010007000d682014205000350a0081504c4640c04090005103009540500507580e072600154203d5000344035030070200707040c00ea41c1c500045814510145140340c5204043d030440480c030400d454010720340c00101d01766101650512451034104070a00380c05100e20000d005a10f031070400203006070003a01c55100c1000810340452560f900038411418803d4015190441c0c44040c04a01c43d0b0340c00c52910305480300d000064500c03286040100481e440f800c84031004000b000030010a035401000b095085590b03201d00c01144139aaa1b580c0c00d5100a6000c0030700003401e20700b080b088050095982a0b00140000e202c0030b02c1c0d1940001c3e000305803810310305205000203039440b40c0d00129007480b0506a000300044244816005c030402203038020030205000d00d0900070030070f84401e078940d1303aa002558007410b9510485001040710440a030095030100d8180e0303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 766354550 1250 766353300 766353323
    0xf0d110c090f191a120d02070b1c0c0e12071a130f0e0f0f010f03020f010203120a020c010e0a050304051009030c06080f1612020d0207020607061a030304080c010507 72
    0x100703203904944c808034100d10841c441195021141c03400004011080050801900e495440c3c0b603000395a9420602c60f0800084010821080c0c1158450a40b0030445550380288400d6505450007414a007031450400e11030035220b42c4071181158002601015200481d520343d00880c580b06c01010b417900600300a0000c1c0141e05804216002a10545402070003003004204480c2000d240e0254044002400fa5004056040041010000a5200c00c08403501030b603c01c103024102000407401c5114581c1c603100c403103070140c0c14804101107a5005050b590700c1d0100802c500502c10070314a8403942c1000000d0a5a40140f10070b1240d880c00070303142c0300070340c20350300b0603100a0b5500c0da100152613085034002008a0302410410803a0300c1c444c401c245e40b0050501070000030341c042d001d02070001c0686407034800071986d000c2001c0d60718415070742c11240c0785600180f549455180785d241c00d0010703000e091908401c0310301040507042c141c10008181d805640c0306401500c1869203c0d8011911a040010180e50424850 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 766355800 1250 766354550 766354591
    0xf13080f0714040b270f0c070312240e061509040b0f1206150105030f041410021b070902161202010f1404020a050105040815060d050f0d110c090f 64
    0x20310107070b280c0303000346000346000105505c083c01012600403e05415032070503c0c10000c20000110440302d030103615040410040c0c00a0070346d000103281d0b5120480890702c01400011816000c021924201d88500c3c21840165540c00e0138442c1584441c0b052510915080c011801186082d4000c025810000f500103e800700d280b0b03000401080f08502400b41d6600b055003404584060880102001d1100f820318078910b003000b20007090712a10081000d414207900011011240d0313801d020070079134412a80810f646804610b0110070502200030038250b80c5205e00000028402c0e0b0f41d0081c0d400c48608c0800c40c0001d8a481e4944200d0f031a540007865086540c2c2e135a00c04110141c6203d0704045140c0c90a85081d140f800b4070500007800c1c425088141848818001004400f10002c1e084c4482c0c802c030b0340e500901d912a038010500c4002541c030010190f0241c7c0e403529403000400540e03000e4160207a6590140541446d21880e190b40c0011040754002c1041000603240700482da9a6941040a0141116071078126 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 766357050 1250 766355800 766355809
    0xf0f0303161104020f09040906061502071403060606070f15060e01150e060306010f050f0309030c060a02040311010e210d030b090609040308100b0f13080f0714040b 72
    0x719203405a1044210081007404480800100d91a6007543d0451500300b210800e982c80d03000f90001940b24075283c10034002007052a4009070000c0c8004101a01c840080341c01c00394882c1c15500450007400c500078984041ca1070000741303180c010840541311600c3c020366900d50030b041d41d21945013501c1420000d2a8064444118410780d0018a411902101c555040c150032103036114030707481d44d5010480c8401205ca42c3e0b54624080780d0300204242090b1b011601c02140513207041c0108801a040c03080d002c420047c040754088000c00c0302001c0d20301a6080340d55040f10b0341e07040b130045002c060300a4034410204030b60780d4011002540140001810788041084080b89052490100c01d520302540d000035980302940b83d0140513040000b102200d9a0541d4503000c000b042a02a009001600300003c05000c203480c104c40903410b40140480071112691101080d18030101540400801444e049100340001b03420140814080b4072a00303a0006480050318103010503003003505142e2400d40c80342e1f40761140d2680f517a4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 766358300 1250 766357050 766357057
    0x117040b06101b11090618420301060b0f041a0f0a030902030601170604020607060e1b130e0613020a0b071104050c0406080f070e09040317071d0f0f0303 67
    0x1c2000c1c10004e2044041c20301105420190200c1d000f5440d1005410850001c0320b00e0b550b2282040c0010540b05000d10035426400d080e00554101107000088507160300b50256107170840589040e0002e010140d9070310549c07900c2d881081181d01e0064028801400078102c1c2c0300c0c1104410440b4804141030046100c1c15244a43c051008940841d544407a00000c60605202580c0144a0680700c51045024410007548820004000074404d00c3c00240200811a5942c0400701e040711420880f00bc203041c0b9a00c0d250744102c0c030040a4071400700c00f180e4850b820343c50f0141340300320020140948a181c0f00c01009a410141180d02203a20501034900894581e01341c10240c65464000c207801252012110180811588043e0000011850030802401002d410080301c94004018100e244465518190110340110000c0f420503840300002e400c2c0300038590700c07844d40c05903601100380d4494540c49817001560b8400c807119440303584c0c03000510205c000d450103040c44400500d0143c01485607104660009040d0760 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 766359550 1250 766358300 766358303
    0x7050901080a0302060601090b070b0c0f0c0d031b120905150a0f0b040b1f110111040501020d0801080601140d05010528020715050406090611090117040b06101b 70
    0x1e000c42e9040c42415070400880d034200d0000e00700244068248000c002c40c40c403507014041d2030f00000d88003083c85220950101c90f54800101c0205444540c024542c0e6110000c0c041305100003418031aa41240c0042c0c168a1060030001351078401d00e20400411000241014001c1960f007401381846001c20640c0d90000c50344101021400010145031005502c001c990f428140709001d189030a0800ca0291980c484c8604212b60907580c054180c41c2800701100e020904d03c07441e140030f50808110800141e2420094030580300243c007500c00d000e003130840489084e20248200c10f600d51204004112140a44e0083e11801c5005000c5601807044d80d1951402c5d2036065660000e03c2040345462103865584a07a40813240481030000d43c50311006484043c10104e400014404e02550340021408020700784d07000341e21640e8000c00134488103c018442d85078680128050034081030a56124503840d500f4100716a2040f43c1c8240141415158102848580d900da958207005100e206000c100c41004010b5002e00104d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 766360800 1250 766359550 766359553
    0x51602041e0e070f0b030a0518010204180c030902031005070201020721021e0c0f01030905010f09020111010e1f15170d050408030a1404180207020301110316030e0705090108 76
    0xc070b921004441c6801c04a43c0a2000109410018020200004112900800130320004039085d25001990070440010340e490004540c40000d0020300071030641c1070341d00c510311920400c201d03d426062068007a2400c52030f000354180c00201000d041c1d1210f5502442e04009280b00050415189a8920703100454107150342e4003615100b01d1070300304145d04000070300d0b649141210440700100380c1d03410701c0e80d10260030a52074810401c0284150b0b00c8e0b4402d9000c01c0702d02c1d41050003808400d81c0102900001d180564090740054200c155903070140070140650354104040c10f005203004c00031031010140c00c154034100b0280d803989403100305006c4c140c0c60101001070100348045445640c24224214a015281c030483d030140b18051204114203000403040d50748c100a603040c42c2e4910032800d0b90142e40b0340f0480d00000b00c14482132002a0a8001d0350b4064118244254020030420108040d50302d803034001113031008113408031000e011021030b1117504044811201001202d440540300c1c07000071070405007600000100d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 766362050 1250 766360800 766360811
    0x3120e10091109010b0a2c1e0f01020d09030809040209040203070206220308010302370f05151e09030607030e160f0b0c03130902130b0901051602041e 66
    0x10741c54252007450050040600c83c9286c14007500c8042c05075018012901c400220000c848180c85100e000c00c03620042c00202483c100350500c481e004100440c0c2c6100c10b00881c0c0d0320445d182d40d9400058030030b40840c05600da0020071032075541c60443c154000504940c1064003800404820348440c00914011685034000d13001b03d01c1d00780582e1a80030604090022540711800300c80010a070010241030560707030182c42d22254040200706429010102951802c0d8481c00c03d01340300340c0c98000c0e0030756009a903820740030100026a01e9003082900d50001c0850782c4042002c20840ca4040b090703089004001900000e0b07603003040049000030707040c80003c13151071000c47e45500000700c0303000044c4101400c550190034a00811410302c03000f440c01040300e0058006811001468002c0300c07400f00282c4585c02c40380c104041d4141d855000400180d00b080c81c0d24081d0274a000004079004004000342c405c040342c1a991a03084c207901c403503100c1c0c180c01051f0083c1d8206039070340e00501c100c0315101c480e003285810540c0301082c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 766363300 1250 766362050 766362083
    0x2100c1b0503061f152703020d031407020901060906121b0c050708030304032303070e040e2a010809030a051903020d02220807030b06060702010e091609050d03120e1009 74
    0x2141d100748100206c4c241d50441d0140700590303891002003038058051500003903113120134584c0b4076548203192000c1d501050b00000012160390108030754042e590319035980030402d21100b90701804d541c03550445076401000c0210190081c0d02c64003500c2c00d1540500110741046542e6107280d800e41e070003502c1c1a030019524000601035213041080505409201005051551402c2e860050080c0c2503d440c2c14415501c4805903440920b08001c1440c401a9104544403040d0042c60803030444c590050394980841c018900007504080d0100c281d81e0103401589034107182500100101e5411701850b40707494189a428000f00d420070704c1c1403002d0203844400e54407103607009021504000c0c0c018010351050704940d0011006000107914800540d4100c0c10503104140c8910980c40141ea0740c080c01031032241c000d54000108030244943c03d000b054214919214079644230780383c800f0f1250a4000c0000600440c41040500209030940e5001100340300028040d03406120a041c60320003500d00781c50058880c1d0081e03c55604 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 766364550 1250 766363300 766363337
    0x120a120f031505010e010c060b13050411010c1e06090602030702010515040b03030a0c0c030602070516060c1e050c031002071104051317040302100c1b0503061f15 71
    0x800c02c02c1441030100c091480c2c500001e0000c44102101c42c100303e8240015410856940c02450017074400402444044900e01501c00c018501203906884c149903100070b00c082c1d5402106160348280d0090880013888089400c20a031840c04a00c7c100e9185039950102d502141c02c80c030185024080c107070700115281c1450a00d2450403c03081032901d00c601e1629216035800d640000441e0105030b1242001c010396002d50800c000743e407940d5400504010b00000d861000c002e40030425000c1c8035550400c4a680ca52503174400c40d9051184800100381c0301e00061010003140007074a9101070079100303c08a070081d50280300424180211001c041d06040e0300421610104440c1d039400744080e01040c0c07070400c4145002c001ca950051000800500315510818641820100c201c1c111400341d50050701d1403c0340c0e00c184400402c450b520540907036090200d16801010112101d4642d4210380c0020b00a29844d1075410704901034000707004500d0004c6884001c0043c4520410312101c45012a98403080c94803600c542c20310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 766365800 1250 766364550 766364561
    0x30301120213110409090201030905101d0111030612030903070e070f050c06180304092301210210231305010206071407062c100b0f120a120f03 63
    0x2c1a0356810301102901011004040e60110790b030421020410901500059004003103103180035295000d82d490741400039025411240400740c01c50522000d044003101001d00301c0d0f48030200d55100074810004960746160101c0c0c8494103c007e407040d030f85030210343d20001c1d1410555030b2246100c0350640041120f116000074100c0203250090500310302d040c1808070079030340340c1d0001448002900700c0101a800804130030029100502090141045000c002144100904440c500c0300000c0b07a05400011400030103685440e004032101078810b00b0401082d50801030540b1f90031214008202898a40300174210440f034090330086c002e88016980d03021444800e080083d0385403c558195480002406070540e03100c0c18140203061804196038840c4e8061400a02330010706418107000c594101000c0d803401b954804862811900204451203000081841c44c1500d8030440d216a100c0c0000c2005001c1d4100340155000e400b8001c0c003683e803c040241d42d10b0481d8846d00c075615000544106002d040c464040c8101c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 766366906 1106 766365800 766365829
    0x2130905031305030717060a0f022703060108070f03060203090106050d20011b02090c0405090709080d09151d0406080a0c050a0302300303011202 64
    0x302d12400c5458020743d40f1a010f24000000d400b02c030f5280503442100240040c0440f503840c50100e00082c5003010401d503141d502003010100c0002010009615054103201a031201e6008406051800005801c108880d5028000c2440a0800d50b8040d40c1125030050004d40c0d04c3d650310745000c5c090702d4150301494120b103054106004000c50300903081610f0038940382c00f400d10640700f4011540d4041d2101104c0700d034211030f816440941409001c82e5072000340c01d00003d203819030315800b1844402048401400240b401c1c141404030345414000c01c00a060b06152880c140383c1401d011480245940c501e000610002e441c040741e01e0a0540d000f0600e150006104104041c7d99600c00e80d141d00384498200da0a0410b400045514905104414240c94010300051703032014030b042104100d69010902060484000c1e40603880d900002c20040d40a043c1d580031030001d44429105000140c0d41c502079 = true := by decide +kernel

theorem cover : BRFrame.Cov 766187050 766366906 := by
  have h0 := BRFrame.cov_init 766187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 766187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 766187050 ≤ n) (h2 : n < 766366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
