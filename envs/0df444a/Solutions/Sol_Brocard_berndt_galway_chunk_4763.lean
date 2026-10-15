-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4763
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:39:16.362212+00:00
-- url     : https://prove2.me/submissions/a1b37d3a-714f-4eab-92f4-cca5772147fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 856474820 ≤ n < 856654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 856476070 1250 856474820 856474877
    0xb01030206070507170304140d03020a0209191a01080907080d23031608071d2e020f0601120f0311160f030c051504062106080c03060a050106 62
    0x10413080080703907003086000d04508181400c0001d542d548c0c0f809442000303104e2010780040c0b0812001181c40c0c0401c1e00401c0c4030100c0340d4115403801c4161307241c01713424000b42c10070788074409164600303403491168030612007103403a000c0003d03281c2804030345d00d50201940d00e0740a0300071900c5540103c045000024010900d01c00c112400150203411202c0f00c0d0a406040d401c00c607844c60001d058650800c0402d500b00004907003040180c600605c250160402031007401810314400c50052045040d11151a2803100070100e007040c80034480850041640d20003580c0300001995283c040c041c01000041980c9403034031a600d039a034003060500c440f0560303883c15585401c04681c00c1089016030080e00c1c0302a4580c1001001621540c0840c0c0c04103030642c1000c4d425203100390005402010b14070102c11002c15a80251800c80d070803460815180030151104000d81042c1008406000303090140124180c00d01180103d080c284c190708546460b86c5201c802403e4580070f11540d808590032a0705807a42c1844991142c0e05030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 856477320 1250 856476070 856476073
    0x1805071e0c0606090e07030f150c18090615030239060903160206031f0e06012c010c03021c030209030d090e070302220b0a17040b010302060705 63
    0x10304034411940d000d0510000900080304506184100304040c0b0038075001e000200e03020422a00c080050075600c141034000036003030142040e01c20041080090302e2140c0c50701a4101400384184201000d0b150703082d1041d55901d0420003050205050f1a94400e6000b11000521140340034060500c054000b90301c01d0f00414020132410002c8014030100f020312040b50050184003456002000e0700369818142c3c0031b041403180c0d410400c241c110780c9644896074140ca0750115103560341c0e44c5800710514040c0c4801f800b01444524090340015519210503030142c0709000070b0300c500c81031049040b4503600307128421007406a100c0c0c1458080702d0b654410141404558842d004869440d40030300210b20410002000c1100002e800148031882030a05110000703650840317052100c61a8184600c101018400601090815a01140354824440b10101c83d0707a41240e10b0002c10700780c4d40c9071301038000d255014410301d0010801c810070704031405404800145c4a1500201c40c4c8006908681c204000742d0300c03100702500d0a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 856478570 1250 856477320 856477337
    0xa05060f19050c010c080405150717010605091c03120c05070f0c03140a0803010e0c04090e100605220e0a02090a061d041e14070e0f090601180507 64
    0x580c00303418001c015031946500c40c0f050301c040c0760964803580008410490103205010004000107904900215030154158403035840a0003290070105900020f50390348400400000c0301500100104145c0b00141c0c0d20000014901c044444840044540100040c0b481c1c2160312140e222079000070a002c03218642245410419100c030042c0c0c1d9a200340a554003480c4250410030000c0482c0c07100c4a250a02e4098001080c058807840c0d1315020500c180001444280b0020314080c40c44002c85001d840d8001c000c01004440c000d09951ba4501e41d0024034441d46445000b0a4174940707103108213103124040c00e980446001c0740240b00302030001010480442c1c03150864820041e0b40300c1003014440c103595100011114074080b07070841d0908000b1981c2c42c02d00603500a110100b9021640d240d00c00510781125082003c02c0c0c5881100c0c60f400100f03c0c00140503154000c03499401c61000c1c00e02400304080710000c40e0305c903400d040780c941f0404e22a0101d03440260070b0b00c88002c1c4594000c6940f0403150b050541c034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 856479820 1250 856478570 856478587
    0x110c06041106190509032b0507050c061b060a0e07120507030209010e07022802011d1f081f05012307030e0910230d0804060320090a05060f 61
    0x741030f42e080700f0480c041400400c100c1d40c1030908003e0010304154010140100e058400450540c004140f1000010001d0000f111824020b007007005016404028040d260703034650f400c0b01001c2032803001540d070115015040c049a01000d1754050000341512040181200e02d10f0269452007480981d4403c881a0043c006d0000269451101c0d030303802440481709520301c03803900b4000241840c50182c28049107044010050901c4181c001152503206d1782030034960002c020540201c07c809094000c0c01d603100c01c04800c01880a00c0000081c4040c9255480b03007a40d070340724800d03107106039620780c1380142d42001d65071410040c030342c4119200e010000b12101c064060f0042000c102c09154845031059000c180b8044500700c00d820314000099110301c04504600905040c0b04100004140021120b052400400000340c010b41c4e44030003003c03480341d00400c216610769581c14040d015202c20000411041c00400820a00750070320011101c00d518000c02a003240f81c100300c01c01007135801111101442c1c00c4284490b49 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 856481070 1250 856479820 856479847
    0x1804142403030a090e0c040605031b0c01090507060f0905030a0602031306020703180e190c21050106091703120c0405030d0c0c09110706110918040204110c06041106 72
    0x3071003540c3c0c0d5209080030f030518152010410014010f40c4501d80100420007403150301200f620303001480455124114100c1090700c0780f480c0980c00510307001c1c0d40303040d0b2100c08000e00014004200d4900d070311111010480303c441980c1d0000c203845001e40507040100024002200c0d5801151701942e02c41c032001c0d40b2422900d40104981180074202d002c80c00e003540b01080c00701900c03030383c40081440f05640300e0386140100e44500244015104400650303111300400c034005009602184480244100b00401d0301e00545c1030f48081c1a0070300c195000320381407003c0821791440c0c0080303519078004c00340021440c00d03101c035040305145040113100b034150361414800454190303418410030503202c1c4113640f4616074904c00c1c10500042c2c429903008141080c98500036540025a48042da031406420110005d031000c0c40242c00449446020b03051580010140c10310304070f0000b0480c2c1e1034000c5000b51410042c41c902e10024545e42c2c410f072009400c0740d83c00800080c0000704582c1844402c0034014141074140400d00924a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 856482320 1250 856481070 856481077
    0xd081b061305150c090103050907120602030105100c080315030a0213050906060301020a022d0a030f1b03140d140c07060e0303070c031107030b0a02180414240303 71
    0x1007080c218a81000c0140311040040d840014820700e0004101d0805400400c042d10400c0a80c80c1416113130700005004400a10500005103035031201410f5801d400c1c40c0000c020b500c240203440c8181d00040b080d0008a04c1060140c0c0c0450340031000a00e1a00d40000309004410521400307a814403c02c084440180c5425803c0c3c003d407840d8040216103814a80c18443c10b00a006002c6070081c0e1041c0084c40c2c0c0107a00250754140301c0d0702d00800170320007080011202482e0015842140b80e5116051450b810568811004001509681d981400300904010142e071004421540a40020403002002d00034480716402030030496281c820008424440d1020440b4012048415048411001c078001c0c05002d130501842608a00c0c6034050340c41c5240582010340403070080500902000450303007402d030f4611410011803000d540c0100001c00c40e4500019210080d500030035114410400c004144031403400d10b070003411000007212608160359170307401601032041d00100d500844200c4100304515036544081c03006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 856483570 1250 856482320 856482331
    0x71b090f0509011a0310020c19291003030f030f0f0618060b03150d0b0405010917070201020c01080a15080d2607030f0e03031e010f050d081b06 63
    0x481d061401c44102d81c219107a0509002442e891400450034954011583c4251451807210050716035403840f51003482c01c40d034160794001004606014106002400d60641c00c42940080074035036000030040d6a460080096500c002c61a414000510005c0d0040c03420001e094207030b20700090110303030450450082c0e9003000790100401350754402c2030000200b2400c45050765031540005000340c84c6480302c030141600c00106030107800d075121184185207079210f008070103841c2d4104142c04005c0c102030808038001e1840e0034044803000c01e82226100b00d52000d0081eaa022178058003e841900001030054400100040242d880c8540c2c2e0f601020a0400d0143c641010b0030307900380100041007161102904001104020503c01c1c001038424061240502140a5000740107140c0420520302c1c400ea44005407451000d010103900001c42006081a02d10100c1c0d42d40c014800e0780020640d80e1041c400c0505545800394542007000d1019550115803003000802c190300049000350314545030080300506007001941c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 856484820 1250 856483570 856483601
    0x1e0f0b1509071404030f020a15110c010306060c02090414030706050f090f060114031e0123070f050f0c07080d0207091a01031d061005041404020105071b09 68
    0xd00c02000d003040805558809001d0400e02c10a821007003810249000302c0c0300003050804440c598000715102c10308500010000854a101201040d19000d440b5080f01c0342079208a20406440410642c440c0c041d00045503400c0d290118520000d409002d804c4170010030580302e10200300200620a9001c0005150301c5005020005050800c08142c030070b1003034040d05800f0998000810012900800306140c0d0450b04024a08644c42e095640400d0504943e018040e02c1d01d01c03010589282d0070019008442d41001c3c0f00000350b920ba41880c034007900320f20152100380018044d601d1001d0750b42e004030003d1800700703a020080f508000c3d07084a92880c0800c01e0700880c840d41c02c0502c02d40300d116010071103800580340070a41841224012080b5a6031280c1d5135100c80d0401d500da0740750140c000c43c101c04071140c52200000355242071a011542e42510790280c4200790050f45050014128400f00a0806004030b505030f44951410340c543c0c6a1002d0031000441c000d02501041c04009190b0660340b1400d0070b403454420 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 856486070 1250 856484820 856484851
    0x70225050a050406080c010f0c021c050d110706111903261b1c0e030c0d1d10050d05010909060605040b2139010c1e0f0b 53
    0x80c02500005980074902403420504207010030217022032241c208001c20704e031405aa20614030122980003210f100a90003000a050a000d841444042e410a0b40d01800440305010003445040710b100d078841080e003d103508540018080180301c7da502061100f845021640f152030400442030b10010340c42405c40210320781c4100e4a00f4005100c03c0c010100c1c0740d400010031285406050070011048220740343d0f00c943c400007040780c800a00c0302070742e850101d0464020004030351300f41082e0391780794064440b4402d540b24906860304002e11407044020b409503452110350041d401d034010311840d0340752400c0c11000c0c02400e028a460546452003103900030820b030382011a00c4040c0303081540444001d504040e020741d041603186030081c3c850288480c00121442040c40484080501e85814402401d10140407040305a60f848242c5813880f000d850714424030703019120003500000040d22804440003000f0480c4040f43e5403c00594105035144101500801d4004e1100140350380e0100304607801c489021a058107907 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 856487320 1250 856486070 856486079
    0x1060b030f07020a0305070303091703151e030a0809030a05120a120501051806120307052401080a060c021504030f02010e06010f03021324081b06070b070225 69
    0x100c91690402c1e074074000307006081859100280b003840f440320040d05158903a0fa03000300b003040e641042000d05a40102e07045d1207003030a01e420801d00040d0708849100d24540702010380f030340b00210703101c00c105e12000380201484501a6510f5207650811b83e94654540075500c01791020031814021604001802e000b0381c1c0d1307108a0944080c1201c820200e00301d941a19000040c821501c0310f2889282c1086003013440c6605640340740c0010101e110400c200b00f414003001c01c00104222000801d40050700701054a502d1241c156882c4030741041e002d200740c861a510618900b408941c0d560703c41c40b41034081d44180c40810800c0e02c1c03201c09080e02600d0840c0001c2c0040081d1600541c28480e80500c15050000307855203514200308441024000d0001911030640005480f000c01074540c00110300b54060340582a040d000801c00e0149410700b403180e40b0080c020001c0100d001d03030440074520302541e0300a20442c1071155544446a40010013840c803415441003101c41d01490400d40c0242400c14440b40100d08420b060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 856488570 1250 856487320 856487341
    0xb01060f03060e062101110a17040b0103290117010f0c020705040e0316140706140f073314061005070206070f0c0e060303271201060b03 60
    0x22180e4181050b14004040c000600d40c80d28098102c13508413810340720240031400034188001c01c0c1e0321850003580303404460541c40e1031390b6028011030002c6403549810079800030100400d045003101d0080803118608014000941075000302c0210b00c1001c20801e003c00d40100101401c0102038101400f0940d8200106004c400d09000b1111800564072040c0a90900080060740e24401402014411601c2c0c52142909000820954400320302486003151142d03190300780f102040c11150884a482d006070100414098044e1041c450301c91f08819119240084a000001c129088117400f122002000c0040c194406110070615451808411202c1000e514440002c82143c1c440f5041c41c08100510007048031039906c00c080c2d2455203456081c440d64030409440001c68503c1181030041603039689501d420244841c1440d08029213142190880464851504046d6a40189004032962000041714038182c01c007a00c904007160240940110401020039492600303481e8141c120010a150110030054240d60 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 856489820 1250 856488570 856488587
    0x1a040f08041202130c1d062503020f07030302060c130308070b091605150310050907030204090609050f04020f0406050d050307060b0105030103152f210c340b0106 71
    0x101140c1040304170380d40716020742112548081145920000301c0840815145d900481d201582d0351141e200fa8140800d5141005950342e503004d800501c1829071361302c0c007220001410b80540c1e4054004212641e5191500e100a03801140c0309500345400040000005500b50050486148500c0b24096140380c00d114552421065454a80e003181910800700000d0300d80b58003800c041503d4480a50b0f484e0b8484c024520081c4c090b0b8095a0840d800398104807000e40d040c6d025105803807099000307206032035031940740310152001030341d10034050200c000105005113000c01c2d001c1c0c42800080c0010440c0fa0303441c00050030071619042c0944160b00002500010400d803442071000c07440302424210f0465066860701408070b800800c05000403940c0346801c080d50080e200e8180307880c0f2100c044010b240108820107201581000d440d1b05032185c080c2240d025185110340b009445510140309060070038000071855800980384400204840c85005803440401012000d10300125004d007418031120b52400c070004102c9034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 856491070 1250 856489820 856489849
    0x31b3d0504320a091a190506030a020c0d1e08060a090905010e01181b12151503030302070b06030606060a0e01210c0801060c032016080f0d0c1a040f08041202 69
    0x81510064010b1b40c55405141d9080c2c17403041d2200ca4031707556941c004500a100c0c98002408034460502030030f105680c0034001c0014200015029000c00b04014425100c2c280b01340d81c40c950040b03070b11340c2c2841503580350761200da000c0340520008603100e03401d414070500310b6900c1001041013880c2e03080080c003409076551010350411602401540210b18191725180080840c0500034480c814240b100900713052160010407100c4441038400c2452070740e82c60084e000b540401002c560240403980041c11914010070040c0c0b0814001c1c150616205140e50105e4005014030b0700a13041c4401c601c1c904d2100403d400055602c0f00c1e2800700082c0c2e039081d41001030f1521005074000c0c0d0800001d6030107600080d80c0f00d81d0703010f84142d2940c3d4642c5e00700348043e1500d09001910031100042d1054640004c3c000f140095000910220308040c2e52121030f98a07000c84041e118040060f001201e050307240102c106210701e940c0e0340709000b0807a0000c110807558807003207c3d60041e0f000c49102c403202a002c40640c0b030b2000807071000c103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 856492320 1250 856491070 856491079
    0xb0a2003071b0203031608040f0e0a1b0f230409090c0b070807081e0d090b0705040509192703030605040b031b3d0504320a091a 56
    0xd80070f5001030b540e03104208003114615501c481e0710007009103110544003c2e010381c030800c00d2400c0e10f5030502600c21304200e80e0702d038540d400d20000000c4e80e80301035600440130016644e049a0b1180d488000c0e900701c00b6155480722404046100064240f20520203400038002c5044049070600300d80c2400788081d40903420284500e00708100d0203002513590f80481d80019404000c1903111413039004040442c00b00103070260210000090711304181c29059000c000d56500c9590304116545030000204c03503a00880c041d5030b8010080348003240c010b8034241000083c1c111020740c0400c5060340840c0e41c54000c2e500340a82000b9140c14030400080503014013400d005801705490420400c811480001d9498400408942180c1d040319480240d9866005c0c05c62400400d0320080d481101d000c60745028103038200c2c01c10380207410120b440d22080501c40e4080760200c601c480d80c40351810140200c440c2140c98101461012000700310900b25083e205c1e0810f4000508200f04000b902d0840c09802061107100c110760380340318 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 856493570 1250 856492320 856492367
    0xc020a0515090a1e0606090213060e010e0609120d0c0c0501030510170c120c0a05193b0601020f0106060206011206060512010203160503040c030b0a200307 68
    0x114030006201c1c5603098008009442469240d95522502a00800003401c17040c00c2c03620120b09460320750000d200f89000581400351103944d49030126221118251050f00203415211590414640000507010701900200003c41902c00283c0103440d0081800192000c1506c1c00c0b0990203002c03010134a00028039003820203111900e00242c140200c1045070048040d103604045140c000c6a84c2081040c1d102c00001d0f21900c86100c05032085541e44400250300d5114018182d00403a450504807580441060003010f40d2040c1e030300b803d0885007050b6503044604501804161184003000203980d00c50159012a1900c55103030505c600024201104990a500d01d0b80c18a40308010250b40004e4190440d1203008111031414824a46903001c1d01445d400590720446010720610740300810f42c0114000d085055212a0740008000c0c19a4039000854010303000c0034a0800410104101d20602540b040b0782038000528820b1941043c0c81e0580c190f0800030140401104104d1841e4002c00790600e49000c44004c0c3c1d80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 856494820 1250 856493570 856493581
    0x5030c03031641092805030a0b06040c020307051005070815150c010608030f040918050a02040207080f0c0a0302070b0421020f030706051315020a02220c020a0515 71
    0xa01d0781d062075440c1d0360b03900f0099040c00b0859200300f075480c11200180000e605800310004030341c00e520700c1c04030341085000107071000810f0b107400a58100040d504c0910f4410640d00c210800000380612251801540001c1003100f00080050050b50b803d180300440000700e50a003c035000b0421000200f4000c8101e0510106000d01c0c2c2e0f4003c0d056002c220f481d030800e60307198030145400d030141a15900c0848144004205007a40d01c2c0c00320042c0c01513036a5910301b00400c440c40c1d640d4903072102c0c0c0b1103800b4006400c142203038005403c0c80c0d0010034215000f400c11034a01100100c7d41107441d4442e41c0440843e070005c1a10b0010513034140301610052140c03040b424102800c0403100d1740e40c039204082d05042c0311515a0030700c046480300540a190400700400381c0b40c861b60380d410068000d6000070502907400c85034180100741c130340d0a108143e540340120790040003400c1c1c059003880102440001c8200c3c00140407241401e1003903440c0aa20602c5605501800b5001c500d403601906d04003010a0b4106040381c1c2404000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 856496070 1250 856494820 856494887
    0xa020301030818150a0201021803010203040201090b070f020604080a02010906030506030d1d0d211403071d03010e0d170f0f0a09060f06060e010e030d0c05030c030316 73
    0x2c0340400c41d642c0a0420520003c0002c4407883c90007550f110085010540740003207074041d0b010301400d0b00e41c060505206200c11007018200e11007220001e000ca030f850389003848200c0111014281d918490085445c40d01510780014106030850380c043e00040d80010142c500f1968011480002411103090610640c14603000198403004000b00b01c000300410b0307500303103619030030b101000d003d0b00c1401801c008000f14060030400480d46054030390940d0310301108900034505104000c10840c02c1c02c500907407411038460143c215501d040080c0d0901d4003003503616480000d42d5080c8120005160520010004401c001c4006061140b0303182240b51070103540c000f001496104034040680c8452a01440519a561583c8840007041d008a01504d9245007039848403404403140c1c81501aa000e6444401c404000741c001143c60012850b0000d1b05508120451600366001d00d92000000381300d13400796030400e10703404032007841e40e002100c0004009070084079061250360071114411540ea0b403039612007a480c0500300c0c0d08 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 856497320 1250 856496070 856496077
    0x230102060c0d0c02100c090303110c031b04290a09060b04031e08040807030201110d140c0703020315010f050d0b06010c30080a0b150705070810050a050a0203010308 72
    0x2c2c0070352034442d5501d0710994402e00c244076200200075000c000f08401800010b0064480e4001207021920380d0b807400002c02400203403011b0a800042c005c0c00c01083c41e120742600c01c07200b032400d42c2d0456141c40100101c0109540360021a580c0801c07140d80d4181c020040000c203c0c0e5a600101075245400b8060003c58100002c880559170042c5288e003100724402e041404a444441000d0a20b4001140105c1c8200c0041a110f040328000d984481011601c140210785800b81c0da0b5005001c80c60542201166035088009080e00e030700310105031401c055480e0007090074150745a4280480c0099180180424510031402c40c000c0c1100352040c0c042c514080e41d46080019002d4245818402d04019047c1040405c1c40614075000e18404a051060981c1d102c480c8a511100c0401c0d010584d1400002c901862034802c8078010300c1c000300003440309c06145581d0700c5258802c0e2010743d50360181160105503a07804007c0040300c501282000225450541401000c90b440070b040e4600c05401000108046100300069 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 856498570 1250 856497320 856497337
    0x20a03060c05070f1b0501050903030a080c0906040f0e011527051012142a040906061d0619050c0f0601060c02032103070503150604230102060c 63
    0x5000d580c860070645180c050310380010301495204008a08121440e8441c806001d04101081c1a0307945490040d1040d004103051640c040e8001e100b4022182d00c00c21402e90404011100705151017620300c00304205600a409c001141b58900900f0052041c12020381801000d0f050303084403d02848403001171080e800a80d83c0b080c605489a25070400e40e041044031002400003c0c00e1017400e2242e0300010f040d5181c408080c2d40401d107030049011100803030154080c410b0144805c080b480542141810b01c1202c00c001f00400348040074040422690401e1080d100a05000d0703d9510203045413000030318001e49202c0001e80600414858010072040e00072003c40510900d00700349464682042c000c601d42015480d4884882c801d00000080c0b03a5048881c2c6d1210900907005d4074000d4841180c403441554101c540c0110b40c01c0100005000d8034072440c01f541c1c01c8094034403035595046c403080c001807080e0000e81120400f60101d140c05240202d05042003412140280060b081501d001080503c460060b60035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 856499820 1250 856498570 856498583
    0xf0f0309060f03071214040b10080303061302070606170708030c0c0402070609020a03121101050c03060402090303070b09030301060809060f01030303150302131401050607080313060b03030d150b07020a03 89
    0x8540c135640219060340c0c200084003420802c0c003103420103081c00381c1d10035034080d50781500c0003000c07696002403020b8480c15203101900461542d111181032106085011090480e103642c00e011005c0095a1402014010a00320707051a5401c44014240303802d000d0190300848440c1d00400c449250208045524120f1079412100141c640149081c20300203807503401c0c1c2c0254051003120011042000d2109404441020b40d84c804000b40d80c0102c2d0903080b0b41082d100000b00c040207200007081850726400a00c103005d40982038a040002d1643d40c1c00081c0b000b61a24012508040014003002d42d110340140d52000c00f1100911050400c110b0342c400610040c04040c0415440d4601440c0d40e41800642200459001d40182c0d6417804802c02c5200601101908840c505002800000e2524004013560001c580240e401c900d107865481c0c40d03030850f00c03140304101c4805842e0160300b85990b80c148068045003500c9000420480107881c020548400b6680204066840034800040961140028907040c0c0c2d42c45403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 856501070 1250 856499820 856499827
    0x10f0e0d05012a0c021012021306090519030f0f0b040f02030c0d03170c0f0c0f0f0c0306011e0f060503040b1f1a0d0e071a090d11011e020f0f0309060f 66
    0xd407c82e0040501070350a0300d6140009085101e0000c096a8807080364516a6150380b8240c892041240e02445021a41901e070f807245000e00100703410003031074891148294241884070000e5959000304641c2140c0950f42c0343c2144006406504060103e02017244007110b200c1c004050701e070307406801c84649904081da0644004002104050050211418a0034890400d0344900c6550720030341c0d81d10040824850140940c4410031141d100014000403000d40c020060b15803030303003450304500b600090800d42041210210360000780162003100210060412a90380c80e507030b0318090602d000d2030035002e0000250101c03081e4480007030f00801c00c8000c0558004078644800d9802c40d0b82c81000901038051205441440d10303c040300702c504002990380490300d4800b01d034000207013241103803100b03405441768581d004a2655512000101200803682c4a41814141559018040300a80d010070f071680c2103980259100941000405070104266050034814500440c0352818110104900e4000c0281003c0b0070070020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 856502320 1250 856501070 856501099
    0x503041e020d021903030e0d05060c0706020702060a030f0b0907050f0d150608040203060703020a0e0f040905010c08010915080a0320060406090308130f02010f0e0d05012a0c02 77
    0x200d4581d0345030010078580130071060482001c0c0e1620075100031000320f11080c0d405442c50404200c541049078002010f0600f6a880c6010030105500031642114140e608212000041c1c0d904400780448041541c0d0000300514040103041c01c17a00b840e00c055120f8110b00c0100004154020104ca81410b004a581c0351904081030414024084038990700284001c3c00304040b50250340043d14a1156000702c084603001d458030302066080744150444100095030310b580406407070900c81c01d51140c0c2031020b070001a1822540c0c0318582118600360302c1c0700002c0c00e400010010b10b01e0b10300800c100040c04512101d1260f1504103c40e40d5880d42c03140080a0149002d040311030030f0090140740124103030350002d0703a50625003450058018562080c085000c98861000315170840c05c0032401c0e54440d03034003610441c02c000c9190019241e180f0008a034a082084030b4000391050744503010000c6c1558440c4c0d001080e01e04941d50402d589070b0007000c200c10000d0f20800220080356003c000490310503015581c08030080c524 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 856503570 1250 856502320 856502329
    0x150402040801020409020c0607091d04032604020f0a050904020f0604080f030307021507080723280f050d0e0c09040b060f030c151612090e01060503041e02 68
    0x325402080c140d44040b40000b801c040c550018852503050b64155400340e61407040944100100303000c2c4500d40344070b5510000314070501035060782e00b290090400400104500c9418203108503054181040305000710280021402c007501e6242424904440301c410581c02c000200b842040014006485420994040011921454102d6019080042c151a24004c1c0107408aa0341d600c192040001842400da96806a240110350703a4068800742c2da860105482e1030008a41d030301e08201c10640340101034107528002860000c018600900701e22006000321280740403210211111138566808c0c003125040c00c42600c0d6000084441d400c08012002502c00806a03420740341c10301c031040158103d00420144030900c0f0383c1100291003440304903141c1a0303000100c4207258407141e55901c880d8000107185010000d40d55980301a001d4141801c809844191a03511040306a0780080f03100f40115030030110a021003c903c000c040d001d1319103410b1191039818541c0e80c030003122103840e0707081300c00102c100b40321801c55a0b03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 856504820 1250 856503570 856503577
    0x10b090c3a06030506010e0c090108010905090c031609060b03010f0303050f120a0504262515021c0612062c06061002010e07030303090c030c2417150402 67
    0x107040e00c00b0000e181d100d25000c4e40c1c0700340038090302ea1450107490002e0540840c10003121a81308041e5100a06a4a0511410042d007006464550b8138048d404c048201a1000c00c04a06001043c050316600300d40751036420740407910103070895a0b110400f0001030005103400c0c1e0750002202d03454a00b5030394804038000300104c28010704081c0501c1480c4202840990f5615802683c010b50040c5003e8054070b030040c1d03620103005c415000050740d528040c069400107042c9540300403842285c40c1099a204203107560303014a502c0882148a4480e40d01041000782051004c60b003074102e594500c01000801c0c2007803081e0414480c06003000b4a01034942d00c4000034001c403441c0f40c1c144443c0301a0803085944003040d40a80342c0740c044410a000d40e07072140b40e810040740b050017078030000d0700200c000d07091007803c41c2c4084015200b0140309803400703450400000001851900708400510040d0000c51f5945000342900040560041072081044000320b00c0150344940700c2003154000682c00303401c50b9000401c02c0820080e02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 856506070 1250 856504820 856504927
    0x7030b01090f0b0d11010e06160506040506180a080a05093718090305091327080d1a0312030108012412060b0909010b090c 54
    0x2441440002000700540e0840074122203445000d0098492007400c1c050840e00c4010050440d10441e0b51042c00c1b540100010150602c0107082545400c2d038501c654555000c0c454002c0b1040c0d4000c004100c2441070910116402c8140340f504003c01b0f5100d4030343c0d1566101250005015504001807840c00980103404440b0b0840000d0000c0040d084032810311f5101041140740c00342c02c40c2e402c0b1481c00d2900301000c2c4002c01c4d1278140410610021042013100c0c01000038010407010b21008100000c2ea65035000d0207001000a510320100300408500d41c281400340d1605106000d151240407032000141c2004107441d04110143e4002840d4441ea0a01d03206468034807003599010f00440041a10b10501e00c0000c505855080009022200140f1921604149001e490320308078a0442028402c28a8005403243c08502440d00032403209d00c0240003c0c0f40090582d034600d5183e41d120300c1c04081e801c004100d2a03001040701429414807041c0e01c40300e840808001c40355002c2c07403044201031411100320707100f4004c0e01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 856507320 1250 856506070 856506083
    0x10807060f120204092a05030601050d1e110415020109080909091513030206061927050a020703030c020c1f09120318170c10030e0f06070e01020705030a030e01020703 73
    0x945003c0c00301210308003506c4004880042c044003080e12140204216406400103a44003490101d9400100005060038105004080226000502940c24600880302103400500e0055070300c1d440c0a90400401c003140f104681564103249083d008208140182d540d58502586d80c05031507078800c2c1d206418440521964114550320b0b0041c0501443d240d000079001e90f11035000c44260f81c980c00108071071900301804107481c80140410038018400c0443c0307102094048481481051400d102d40d020a40d80111020500c0710743c0880c1d0002810b5260145410401c80c900140400d8135801c1b020030084521000b41103058420001c0b200350440c032407407403280108007580520340329a0b0039150041030500a0b00344041e00d003010300c101203115070000000d206130b5135803640200443c10000083c00700d201140c5035044281075807062030b510b000c4020701003031205207810000f800c81440d11510140900c2c041e0f4070014115845a40140020707140040d14030320300340d01400c12080c0b40040a0040345003d20301d40006020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 856508570 1250 856507320 856507331
    0x120310091806022a010225020a03140f19020a0527100306020d0921020a030f05041203090302041d0703080919031406070f021b0411070c0e010807060f12020409 70
    0x4901301035010b040d1441c030310700c441003074190310b202c0c1d844a0044030017000e0340c0903d01e490100002401101c05012050700c80064440442040d030b4610308100110302907401118400c003221007140b03400501c1d90302400f011505400602b00b44050001034100c0d0070b0f41140c10030700100200724807404a404040045501207402d558034101c1c45800c801410203445e04032103890b00013034030041303c12050750900800d8110758006e0400da091038400311401030001d5880400d01404210200e01c40f6880504000214003a4840e406040d00d0362040c081110070004800109890701608122100c2000c03840300d0440e60005030301900ca4007980001541d00f5580c030001d041c0082101800002c102c0810704004c1d698841d03405940241da185081520180d4040303400b400140c01066160211400320f664402046d00080e10005591100000d50303882a8040d500c26075a014030120f003008202d01c0b2320705e118090607558000d0705186150910107020000032054480c02e1041d09807403600e4408595050310300034a4486810f220 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 856509820 1250 856508570 856508647
    0xa0f02030c010f0f060f0b0d0c031b2105090c090c04051c0b01060206270a050d02030d060f050109300605190c09061b0512031009180602 60
    0x41054140c1d80c1255400e0500c0019520010b00c406800c40d44c1d884400c5180440148c032440050000d000319005044d0794035000d04540000841c01040c1c0e40d0640c803080c22040c0c80390ba01b0340c0034400e1071611000c0207003802c0402c04440340c0898900c034180803d0720b10003c03989600d0309541c00da0103075400050704190802c0b480343d4981401050142e0803409001c6200d0540d889060490721458111004500c2211403030140c0302130050703403c500541412200507a81da0010700c1d81d0705801d01d00c0070001e40c0c00503400840c1c0802c44628900c61403008001d0070560b1403055152400103000348010748614a90300303044550060b0b1803401d4072a048406240810403027040200d518000000701000e07600301c40113104084402004032882c1c410304a0007410794460550007894008200d51401880c49000d00150200100c04c00040c02005140301a101541e4450340324074010016481840c9580e0000388800e06000c40c040c41100300c002091000c54000782d0250b9224400241c0d40031405900b07144d0403100207904981803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 856511070 1250 856509820 856509851
    0x4030504061701050d080c010902040f150f24110d020d030f050405060402091b030406050f07181202010519080117010608030d180f030203040501031b050a0f02030c01 73
    0xd0790019100c20103102d4200c03080b210405001d008098114040780c81e608045003008020704050820003001081c160a03a41c0032405450a0a0701000384645034100000301c1c003655a407100c040c244401c18010424980350207008440d4203e1403ca00654480c400070250500c10035058603507045080850b100460144402543c03141a90303035600020f840c00c200e204400400340511801542c000000f44100d846d95001c210204034080c000c40c400c80c1c001080f803125258400082c5100300d009540000f6a40f07804c0d6440c2856003c020b02070001c00131500c84106040210380b42c0b42054030070442c0c454602400e40c1c03006840300e01c9a0b241c1d118140505002441d800ea03480810a41a14891110440c45c1d901030f41109090b141c00c2d0181011a41061000d5003429040383c0c031410010780000c4485a44900035120501d0700041c2a400f600181c200180c2071005580500030040072081e040b0131000c013001c0ca008010568014607940390b040103803815580680c5d502c2002550301d40701c00c0c42c8c02004903c0203800e00c00e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 856512320 1250 856511070 856511077
    0x12c0a030c03060b0411120601020c0d050f250920030108060a0b1c1e170c010e0706140319050109021c0c02030a1206150518100f03020a03060b03040305 67
    0x4039011404c284aa00c43c2c0d040600444030841440c00313005040030320071700c8142025a00100041e0441c820701c2c1e4007002d199070b011543d82c07507540990044c0640e28a50301c05281014280c0d0a40f011110010316085144041e0b104284116201c0074000646118034404a50890080160051050b10044000301d200c0b42c0105006000d00300d00380d41040b9540c0904248050445100c8c40744641c80c105804140204200d0600082d90500490494034036240c1da07a90503044009510054082000100d10401da140c1c2c24414880c00020001c020090285000c9000b82880028a040c00c040302020010940c0c08403140c00070b00850f00104001e001c25a1941c0d6003100940100d50120301a20000c483d4111759012441120904050342d0b0107146030403606c00c0b056030301c5988035000074041c0c1c1d80c030a00028080090034aa0140918aa03251551181c1c0c0ea0f441c008150342c4280001d1094480b610f90042e02a0401103e02d429403190402603150003400340194000d0202e54413805022500104000c201907206005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 856513570 1250 856512320 856512323
    0x4050613030614091504022b06020c01051f0503030f09060c010c2304080606010e0d0821010b031510030617070501090b030f04061d0d120f0902012c0a030c03 69
    0x125800400c810005e001000016035000c0d40011500541518100d103001601c104021809084980c440d6256030b80003c076440030204684c40d940d0b92003444446141b416940412007988142c04c01d80c90700340382c000390300c03480f03100700038681514000784c1d52103162a030078103a031a2103181200801040c42c03c03802c09020510b100e00c03003084402c03885981410f500310420035982983c000d180208140d6441c040190341104440c803006510021110440000a2014004003994030426504106801040a0f003501041041e0012807032050188200a642084c0c070311982103c0350304455640a40c10040d109600802e5036422800d034801c10305000020f05440064048121182a0303103c01100b0380c0c1f4056050940800e9034494811480a400704002c502c00d0381200342800c0c03040c580c09824180d2203021030314200380c0f45200404071b407000018030342c621118803d001c80520075010512880388690700080c55480c0036058222145120500c00014201081084012a80250813000283e449081a030000c4410340b00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 856514820 1250 856513570 856513573
    0xc0302030c19140d0c060203090118030201050a0c0813030c030203060f0f0c0306011404140301060e0c0a051c1e060801062121090513110405061303061409 68
    0x7126505402c000306514031a681c0319014829440c1000c44000c650807040110030b030300040c8145510081090903025400520440c0c00841d43c1d2141200058031030342e15601460b1008a91410810140c0d030484110740c241c5103070380b8000500d00000c0c45e09500030301402500d00106810b42d04d01004100c18102000c01b0ba0740200c1c04c844165a800c150b840c4003200485400c080c080841c001b01d0b407000140000b030764100381e0504103200080c03c64501071030786821641c096440b070320000580c00d095080038850300011b84000082403440740340c0030b00c0c040d01e54420100b10000b00013001880c00c003c07010b1600b0400321041c0480c0c00b4410300c86105c1807001801d00100c0a41e04461410038002102581407068000310758642130130071203000f071074612281d0403010013806696030300798959103003c14001100c6005440074142c42d6071640e83c1c03c0405200c8100c100d500d078a01018031780b41c0080e40c164441400e4030200c640c215886941c03450b44503405c0e001d480069100410260401004a50a28210b11914880c880703880 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 856516070 1250 856514820 856514833
    0x109021e0a0c061d0316060e1b10021218131406011808070302060a050d05010b1b01020f03180709090303050615030f04120c150219020601211e0c030203 67
    0x940e8226080d1008008002c683c02041b940500c002e0001080040d10700441c3c0c0000c03241501c10213107080c90045040015001801c0e010b085d01840d212840c0f09910141d440107102c540310015000f20304d1710950342800c1d092180c3c01c0d84400695a0076481c04a511000d520500c420072003601c10b5a0303d06804c0d80c00740d002c52100c10300c95400d100488004011144568001c103491443c40c1c017400219840740d0814010010308100e01d0b00d035014507002d150700138031540ca0465519002001c1c55804140c1c528600140c507401040140180c618101c143da400c41c48031034550126075000e1f5009450301c9030a030701c00c0b1100c0741010301102c141901944510300c100d02c00c2c2c1d0102d0036140343c01d51161492100f140c107550958010004100482c52200c0114040741c6182864614022903403601620f103814000b801c0d01c0a0707000501a400c56464561500452906000030b100c0d55044c01c8048501b81c40400700e003022021404442c100b44610032244c00440c543c0550080419801400d042d401c0400754001640a03104a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 856517320 1250 856516070 856516091
    0x2130c03111306030207150e0d030b0a120b06030708060a0b040f05060d11030f030c0a05011512260703110d0504050f0618060a05040801060501020c090109021e0a0c06 73
    0x58125407441c80318500400e1582c0c10500c0070b03002508211b40646501100184841440784180700301084c03624214000c0003071040b00c020007421360704540728860254824540c204114455914110a142e03130141d90803131150703580d40103c1d240c040503a01c651260b10030b4401340800d41596500c0058241000d850521001000f070509409554090300d050b504a4200c1d85640f011509480c1c0f242c512440c0101540e20b040d000c0640303180756400410020381d180e0480d51200d41004001d204e80340041081c0d2004034206484c148409640c40810200505414148035003064500307070300d081d075182d10720351440d9450700c3c0e41031410010079000010080c5d02c2d00d44162892440083d003d5400d940450700002d100c21001d158403014841207800c8007002004900320f0303072420103265403118058092010a1713510182c071289000507890a651b00c0d41d0015056400101c00d00c3c62580798141c195066600b0313100701680d281c0c0050b5074107003e8420041014403010f0b01085c0d00904552000035038080c640600700030301002191 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 856518570 1250 856517320 856517351
    0x15070e090c040501030e0a0c080c0109170a0b0711070f0303021e060a0e10020d140109060e0609070c0c0602100c020c030c100c06050103211107030b0c0702130c03 71
    0x1d96803811082000d01c0208629882900010490f510a1040c0e03001c1c6c034040c0d5070700624022180c010784d10b80c0d0000300c00c00509581c80f405a00080402c0704c0a004c0024869040d00c0c0c803880c240c1005400703104143d000898580c0140303528032118200004451070355550b0807100b60041c245020803001402404246200c030203030ba4003034256070320140001c0c1416032a02c012a000504001d62818018043c58088580366182480503080c0305001a4010468401c244204185120140c02200500b45000410b00550340c840040e15444501503c0540c03081d01c0321102940c04d038840c440010300001d85184c020800640c08103040d5a207410521040c4001c0b51841c80591301c861810b0240f03030305648840c407420b0840c035001550300c1e041c0103035041440542d00f9070740b40c490540e14240c0056903420800461039140400c1001c060403518a2480d10303607008024a00741e10f03140d00e0b5501c400790200007a2008615075800210031100d060ba4018410745140c44030307035448005420b01c06266000702c0d190078651300d080d064 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 856519820 1250 856518570 856518589
    0x260a051c0b150a11031b010606020607090306021803190311010e0319111212060f011d011e080103020307050907050a1803021e090703061401030905030c15070e 70
    0x4005001500407403511461000c143c00801078541002128025110302403401e00081076103000405c603003440703003031341c11281400c0d5480d43e801a400c43d80080d04000e006680f040034030b42075a510810159a404012105d0130343e508181860f60b80c50700520850210b99556051110102ca100b6140c426607190340d03c90141c225842070714404442d8000700040c0085981204004503c000c25081502d0070480401400746040c10310010000c0010f40040c00d2065142c52050b441c0d4041c0342100e0840204d084040020102c55025808078a15150848030003020fa01400c1c480c1e00d01c0c0000b81161561031420000108552000e00c010b80c040d00031410302040324100721241510484040d25180d26001744000e003222007080c511044508080142400700041c0e40f1203120254051f88169018401d900c400200f200024003c1d006c80181450f2220810009202d214418034074642400c000074420558203201d400c610403c2c0c20403901e8011007210117101404100864040e4029a4600104294200900280341e8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 856521070 1250 856519820 856519841
    0x150406120f060f050708010f090b0f0d0528020901090e151b07230a030e0607080d0f02120106030209010c060c1b03080105030111120103260a051c 64
    0x900400c951408125440c41c1d0302141849500009080da90460295040390070941c0c85800181e6404d00400900882c48103a201802da1050200165008032000070f6503200020901130007022810080020300c803042c07140c000c0031964036800c200d40d00264040c2c0051901180002c901c240d10150001c9141c060a21583d04250300350402808000c0c00c1002510300c40744024030150465900305017610000c90040c010785020740c032403e004070300720b001010031a00403031041c601550298031049684011987c0000c059080c1e800c01c0d81c3c42c1c3d68603411824401c401c1d00c608072890440074280048510140010b50040000c00d9000410510f96604c4440c100d00f0b80c802d85420b980000d19005160002c1081a440034201c00d05500b00841a0042d8140c509502242c9403400e90103e41000010403c40c20300307000c2c10300080009000d00749400d03e016041c203804e80d818000a8040d48501c8043c070108500340d04841416110044125281c400001d0018900c0c2d003c0b03c007828994008040f002d6403000d0034000c4040d140c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 856522320 1250 856521070 856521089
    0x606020f0627070905041103010b01020c0103020310170307020102160b03010513091208010806150604140102121303151e2706060e01060503010e15030a020604090203150406 76
    0x251100d1072003411903042029181003100b8400301040340e114040245074000c0000078401715251426041207041e250340d070380506001ea41480310100f2160380c081840310707030900d09080040e02c0b0740b55003091154441c5aa0040c280c1d031424100c00a005400000c040c08140313200b682100c0403512035449031050400e2501c03d00711460424001031009103084a031040c83c4140c4c0843c000340003041d903140c1401d41681142c6d4800400c88803001404284018040315034081c1841451388465204003003c11501d100754420800e00c440d100c4050f010350b81c82808942400c542d003051142d1558858444d148212178144800c5034800d4100c0c0d01049244a280501035000103906003480005c0d0bc2c01c0c42c0700d809403c0c20900d080b4101514040c046105c0381042c549200c85000b001c00140c51418a1a50280300c90180c000d03030184002803004004403514440e9507607020540d60031405070783c02c1c410080791030300c080c039400258040804038000c00c0241190303000d544650006000034151400c80014001260800c1c043c91651 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 856523570 1250 856522320 856522333
    0x60516080703021011070203430e071106060904171303061d060901090206041a0c030a050a021c080a0b06130303080106120b0904021c120f02010606020f 67
    0xc2800400a007403620b01030700544500350b8503c0a60070032120000300c117405610010460009500301000130788024400c0c6c29281c000035840c1c4d5142c0c01c1c45100801034030352900111000d88020440b01a000c8001c109100d0906c213207051400c0040c2c03086c07070300d0080a01148100400a5520b1420301000c6004540058401c00c2900c0c01810040d6503a0190a00300c544c038100380350020003d0142e1082c0705224605001c0704180c1d40c0c605a203182020f401030401d00040c0c3c1040e40c3c0c08096580c5800321030880340380703020a0b21062141c1c103181c000c9009400342e8250601000c10b41c800d240da00070006151044159080c9c1d80c0525104150340701104115000ca800911303003c000400046007039202c9003080340d00414050818514039403440b07021407540c0040703000848660040113501c0d003000502e9290780c10880c0c203026401280010440440c4002c1002c0c1c414040d0710a01d0902ea502c00c01d004400c1d941041407910f003601450b80c00350030140100c15140c019881d00c40c2c005072051000c1440c00340007074584040e01c007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 856524820 1250 856523570 856523573
    0x3050601050403150e06090c1203210601120c0504051c0b27030726040803250501020d05191104120203030f0a090603051e0403121d0f010501060516 65
    0x2003c0303040e984c2c404005659144c0e05400350303600300301451059420764018245c0c4889082130050101d0900031164403940240a6100d46c0c1003c2034400c61400711416040001e41e440e00d004840242c000c0c0d1030781021503e007038501500140e1044c020416260151041c10311010a104c040d506200d40d90405000c0240d09c6010030302c0e501400c0d180141c00044103036054007400490010b2411a800100211024190801c14904180c04100d01d038410706441031200703040a14141480b920b80c41707400081c0103001c5610741c0c65030b80744440426040f04540c1100003191207086506000f0300130301064a515943c15541c0e03000c00410300c014061141c0341030361142d0480c2064130305500d00031000b0300484102d9142c001480b0700109141214041e0031801da042d80c64225092070618060b0456101401407030f519807109100d085540b124202d500d811641c51300d421000440013140d007000401100308112107040c00c180f500384a42000051603403a50b18100001c02031641d0b0f654040c2c5143c8a1072411081e00c4600050060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 856526070 1250 856524820 856524833
    0x80c0a060c060b040b10020616030213030803040203150c032a04030201030b06071b090c0903030c0816050f030a020c10091a0f04060306150e0913050705130b030d03050601050403 78
    0x3c0394000b02a2001c10800414000120070301d02054500300103a11000800925226031000405000c40b01e040031071a010005107000c14100d4280005032958400101050854030304000460195a204c4201134281c01e1001c00c5500b02c0d8020f0310f02e07001030110386070003500300c20002179006220317110b04031081e1600d49164010340140c035500541c55407100e0305001030801305515050034144111900440702c2e005050400c41021164009c481104110b07540009100080c0c114445c1c00c2000e400101039a26400c0000c0583c1e40e030309580700000d016010342c1001c0c0000d00380000140107180000d40a07a40701d044480c0a002c000d501418034640050082130081019000d40c4107442480131034a00c2007403803c25465044681e542c0260300840c0003980c4c800081062040c1070008100c400c985d840c011403110048030000e41d041001500d034420400c0306070640d50030440c0800c040c100804014020b04d0181d2001ea8274940280400500c04c3d009000d04050ad1590341d10030701c182e504c511016101d4905050a607160113 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 856527320 1250 856526070 856526081
    0x112031e081909050607020a030f140a0e0d060e16090e100203040503161b0909050c151e09010809030408070e180f0601051219290709080c0a060c06 65
    0x3102c07210f6441202e4030102d44140701445c41009a0f40007805006814603004180d072828104140401030000c100d4206c1311000c0c0100c4043d58814500b00503041c0090001480c581340b6040010200b46c43c0ca0040d030382101001c10070340c03c162505600c4c1c01e41c0681e2000c3c1d4500b41d503042100000e90390480784100701c40114030b5014507005030045040300e00b40324007005401d80741c0954030405d6854501c40d44418010100242c10f440140c220400284610015903490650fa2400c0a03075851207080014181001d02c0080c0c0706641c0c04800c40020102c040c039002e0b003441c0c0705a1000300000e00142a0f40c0006028039400000c603012920309000078403085141c600710b19401c080161180102c01540c3c030002c5641001003101c1070188100c80701514070355140c1010090010184d400307035410341e044001e034110b08417415148801d1494009141140000c29122240d80c1c41d880d221010071100650380a0248866011100381e043d540c814048079a107035030520070007480d4641e901c1440c000803403800c100030005070b554110307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 856528570 1250 856527320 856527361
    0x31209070909020a0e090109081206031207111e0409030302090909072301140703020309031b03070b0f0435010203220213022b05070c0f031202030112031e08 69
    0x1901c0725249c0d4688019074007522498061300c0f414030910a8920781441380c12034560500b002d1510300320032581c03a004000f48040d94984114100e040d0480f492940c039031400c08400c0018802c010401d614500940250400c83c01d42d40101c0d68040003542c3e005001400e4019184005c0a042844c580c52240080c0c00e14401102410451403181046054402a02400c1d40510a4010707549920001080c94078200d07051540405c0d200034010303100705546000c01ca28041d00c1a03100816070302c1c141c2009a18040c80f032071b4045000e00e030090341c603000500d03a11400f5101192100040c0314922a09211190a07070000b41c40386803142c034000b80110001407652006003590392004d0035840344c104580020b00100e030064081664820603140031700c2c15004091200c6582100d5044040169003016000100b88140c4002c00404082070103503e0340c140350144110b8554040b03212002c0d9a25178469201030305c3e040d81064200c012400d0704800000b40c03249400c4031800003090780d40f840096500c01101c8078a00c00ca9000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 856529820 1250 856528570 856528573
    0x15080f180106060c1a01181d0d2d0f030506120609011d060c030a091e1b0b090f061b03070605041b08030901030203040c08031209070909020a0e09 64
    0x295034280c03403000c0c042c40b401000c468980d0340d00c0c1002801e040c00909440010301d0305a43c2c122006000d10300540b5000d411601040c44001000042c01c42c250341800070f40000c2c100b02e44a080c051854040d072000d4404004080600f0b41c00304607403251054003e000703810603018003280d5a403405d80047da11940c00103034001c13801841c010003050904211414140b0545050009035164207240258030340c6222071060f01d0b8404402001180f030034176612b0a45000283c0307600313680c94580c030380750303042c00000b0b0301545d40306403007030907100ca850560b1038030495000c800380444202c1e021200380000c1340000e1100340c5100c210040c046022600c0c000007041100d502401c0e041484410340428046070104c1003000c0c0580c58883e0348001218145070411020009861001d801d910b130344440140402034001c000d51701c1c2400700b824096100d4450789090941d00550b6004002248008201c402c5904001c407145802280b107a4295124180c50b140040140c0e000c092020307410454000d070801c0744104510708031364003461810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 856531070 1250 856529820 856529851
    0x30c03030b0f090f0906070e0a030f0c08060903180105071a04050f0d090f090203011208070606030f03030c0917120c010b2206080703030c0b040203010b04050a02120115080f 76
    0x7000580c20f0f00f01600d051001652090400100d04401c0214a803c0b4103141070403a401d800ba440025040c0c682030100800e0003600192980030010440141006400307004240c1d00c0500d4403403030342640ca07080890500741c040c0320307100d41d01c0855000e9130449040b1900003155001440d6001d40484042c8800ba02c100d4144c85048010405160f041c0f00d258101c00711940d50410013460541100451a1035401c820302e8684108010444c54540b401032a6001d60300c01341054941545040c07070401051154000341000c0d15400d0210201903155110b628882d2140d10740ca180a42c49184c0f400350284c004110840682c494414200500c40d81c07000b4194100120001040140b5900041044001514071011110722050741c1c1c6c6003410b0b9140521405410040024610f4a00c1c584006041d4007901401034201c45034480810195242034002403900d500103003091004e81800a80200250b20651030040c00740041d000100b8180420180c3c603045442a60b1143c0d51340d2030300c003a401e61055001e040807203001c03180c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 856532320 1250 856531070 856531099
    0x4021602040f0605090c190c14060f071724030c0a1502060f060130151502010509030910020a0b0c03070f020307200301201801020a030c03030b 63
    0x40c021040d80b200250b0012414500d040d090004514019000011040040c0050031f0a83c140119024219895161035185480740381400f8403050100550038200c0d01603502081003281007600704a0117042ca6907507100305040e454100713400e02c6074261021500c1494988010440d110006180001b0312401010344401e003484d50b0000d05901c1300c642c0003417401c00b050381300b141c412501400050343c802e103540e01c1e0100c103182040000349503d81e4020070400c215100c41c0c0e00c0403000d60f003040421030030503030030b07403c01280d0941001006120702c64441c5809a80d075903001c0e000d40034418081c2ca40508248402036013095155030400400b83c064040310300840c8503000719080800d46030214903009010100d0101c0d03490424040082400c0301700004170081d075004100d14400107020425220343c000785641c0c41d240700aa40c2001a014025080d1088003440c01401000108060b41c8001c2c0101008522031440c010408801a07803070b003a0030040940412482c0c2d91b501c021a009030000b100f542c5004004103240d5808 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 856533570 1250 856532320 856532329
    0x51c02060901120f14101212030e06070c14030702133204050d031802040c020c0d0606051906050d0209041811030601290d09050d020f070e040c0504021602 68
    0x510f40704c5541e255420280400b02c1c170403107960040c8107810a1582c440c00c100001c0d00896200030010100d401d00c9254001a03846580402c005030f008000740c8010f41010f1f20000e121101070b00c01520079004110b034240b5860000411200e0740b90303002d003a03048000c1c001c4001a00500030a191103044405a010310300381c01d03404600525020075200080303482c50401e0b050051800013810040300a05240c04e410b106004102c0310983c401e1030341190045410202e02000b01d091110500b811900400034151240411140ba048207090344d1040d10850211a9020300c6110011464490140420006c00c1030070310710803180c7c008010700940034101081c60404075442c0b2400b07246540003514203035500c04c0000319900d0140310660040c104043d905002180d01c0d08900e4900d40740c4050071710100b400045100600e0015040800800d8024040d10701042100d030303010b9103a410100d00b1400742d01a4501c08550b051406001600031a00403414515240c00c0c072051200943c40103564440356480e60410f40c0040c0d49 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 856534820 1250 856533570 856533581
    0x1d0a11131802090603041202011b020a0b090724030b060d02070204050601090e0c0d0608030d090b0a1107080d021611040c1103031b0c0106030318051c0206090112 71
    0x10552844a165450706801a60361009200e01a068500412040e10155104015207800c550014000303e014042c212069006007d10940360200001da800c3c422802500419200c07582c80c0945a100d20950b5456800c1e52200c003503006181d156521801000e10402c1c000d040c0440000f40c6090025044500c0d8002408541001b1820760b40c141d00098100b003181804d00a4503040034007030808071842414413540d0800503100500030188a040410240050038064111a004100d502c1c01c0d25602c164201c1c03088041c10201c2d10941d4a0400d42003c505041d4881c491452203640d03418015040016039595181240c0c80040c040242d02d40030312004c040712807643c0f1051200380c8140e180200003075640c400d000c01d030b50b07006d452081805021401441c42004c0401220f501040301c40340700c56000c03e480d40815035400b031200c00c1c0c0410340c80c0c00008010160000300c00c01265003520903007442150350703c1c1000003681a420560580229034047c1000500f0b1007000703044144014145003010030b8072003803ca0304484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 856536070 1250 856534820 856534837
    0x6020c010911090601080105060906120a27051011040509071110060b250b040f0303050105101e200c150301050a120305070602070302160503071d0a11 66
    0x955440c201d00800050400360305541d001078508080901e400c02c006850081c0c14402c440c05828001071660481d40d50030100d900404804506010030b0030040c3c6110001c10f580c0700540c6000043d03002036500006090382800c1c407940d000c002082d03003104e403000ca100900a08104001d2100c0248004602c03641d9042c5054843c5416a555108980c0301d03c44240c58010501102650a4a40b030030501070b40500c2401c50381c0740741403510316484a11383e480400c401d0124050000c3c5c00a44540103110800401207a180801c80c080c3e5014010380c0d895004100d605012480d1034000b00311180f955540c201c0e000a412904041d56060504803500c030342c2041c1c4148450581020f145402c545d400350302c24905258484018452403052034210360410b804540480000c7c0109840c5124200d03601c1c00305880346e81200c031843c2d80940c0a646907007081c540a580e40d0000050030702c01c1c481c040004900b41c10001281c000316202d02c100100f44006c60513604c4100000034243c0c00c09140c036100b07070588841a8800415140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 856537320 1250 856536070 856536073
    0x313091e050c0a0206250e060405090c030a0c1e0305180319080f0c040605130306090b0402030c01211d0f0c12071202060904020706110405040e0a0b04120c06020c 71
    0x4141d4400001d06025008101c1102e051b182c80030b00c900d00345085802c44040526003441e01c014a203c4c400145140a0703a8410344e840b401400401c141e40c919903000c1c41c004c2d1015003081c084051780e4101034884008800300101c0240c00c140840c42403500c07a4200c0f540008501c0b0400f0300e803500611586085a01c2084d1102000d0161580c0140c801d501c00c07d11940640133111551803401e001c0e811080b40e109511441c800c0140200302078011002c9200da4400456020a00300715101062a1446801c0c00868059210b070140c140d00900f00d50003810701101e0320651360035145181d0711030781c130140042100140c426801030040c03084900720942044001c0d01504c3d8040141586080390b4104204075414404250058024040030801c11b80010a0080126030450f825034071741c80d100c3c000c503000b4003440304050081d0382400c0304006100c088600a00c20345009840610000340704038800f0b41c0e50b00c444070703004100d0802d420004000c50710807044080c1401c612b140202d1000643d458440a0303801128100505 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 856538570 1250 856537320 856537327
    0x3051e12010305160608040f14030408030408010c030b030615040c030902041103010806060a08060f131505010f060512150609060325111b0316030c0e090313091e050c 73
    0x2101c4c40b0380000e0081c43c01d440c1c0030708035203000c0e60b030288500c1e07506c44000c22007940c01119192001081c0305440c0540960801c0341d40710f980e501c441d1030180030318910b00f0010901c1c00c1c0800c203982c10f000c29202c0c8a43d420036000b6640241d48018840103058a104000805680788002001aa114020000802c4104040c25229418561424285407001d8007092050314440070400c1040c10200e4815400750302d200c414841030303030380e44401c2c1030950f1440c600400701102d00e14108600d030700c15407001c0d05031039104a980948a890301001c0e80c0790312510504800102e82c4000141600e1441141041e0b8100090502400c1043c00c60216a09807c191a4030840c10303840e96814030f010100c06581c0301000c0e8a482c005480303c0704a0150b80d00c6158140141043c400c41000405040c0c4041003541ca021008131400ca403c3c5949081c140d004801030b008003542ca1003c540800c0e4112000020744008901548100d03482a1801d40c07214014100c012844109849003c0c00c0146168144240d9100303100c40d6051664 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 856539820 1250 856538570 856538593
    0x906050406080f0a0803060d0c0303081e070203040e1f030804090b010c1109060d02030d050903010608010903080106200d050703080906010e01050f0a170307021302040303051e12010305 81
    0x5403607050700552070990021006000515001511010860300403184e5079a0380ca580021a022180d030020240c0f030b041c2081ca00104169004030b0391880b034031000a40c002c85c0400900c18404000041e0f0300710005a00600051002d41407149007140c00c11701011813401d1480c0000d045055110aa600c140c840035404141003040054501403c0c480c20f01c2480e0048001031540c0e01c1540e8030852681050140380902d0005075545c0b00c0c20118000300d80c0003003c8408641c40b03403100510592282a50f980070b5402c200c80041c480205004070a0800d51544507011543c6c24048102c8640a60064a00e00b0b0080421303100718868042c01100600e04003650b80340e5a030651410003174041c0750080c3c40114640e000000403c060014410030074103460703040b95094490840080051042c20064200520f40e01c9071984000000781c00000a051580c400d5078041001030302131060004a0181e8072028020410802a0400785088207419481401251403028180852500c0078400301d4000d8004541c0c41c0d008101100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 856541070 1250 856539820 856539829
    0x6180a2d090c0e190209010e1f020705121213150801051005031b030c0903030c0f06010f0e0f070903210e03010c090e0907030506090c01030f050c0306010c05030f04090605 75
    0x5052414500c14036420000150030610a4142d400a1303c940e0108064290780e225050b0b48002d00030050042c0e1244500460300d003554204103c041c0d01503c9240300c0001c06007013100c0c003800b00b0211000a054034140034909120660b01142102003082100d2001280070707150741000e404200071540d00e240d03496040205100400e406c00ca20007003446800e10400104d80010010051407818210703400d6240c0d01d0701b0442c084079000320846a40e1501000c80c0d0b40840e0710000502001a05a280441d5100c1c1d0740d400e03841c11105454010011481580000240c0e144013002244c1d400c00d460740b5007540155501d8031036003180400b601d01c4804001c410f01c00c00264541c494208846800c00710700800c1082866040541241e900f48106560b200030240010703020305041c08024000c613004400d5514a28080030318070384803442e06e0312644c0401e1420003400b084c0c2c610ba1103428810b2818415680ca56190300c8015580c59090076001c81e0315120422a480003c09840050002041c5042c0c0115426044c82c3c20803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 856542320 1250 856541070 856541093
    0x6041e090905030a1103040b0c030903011b02060a0504170d0c0e0604080c010c061506020303041b030f030e0406180c120b06030f10030501020307051206180a2d09 71
    0x21580c890610101d2004900c020044480303a4001d420104110700808200a045014540c0401092400403510102a0a002c030040412107000c4000308540c261004800d200900ea8480c05d100581c010400104d150303030140e125a410500031580ca80030100000180c2c0300c940d02c4840844d4a1503240c140c00302c50243c20410040d181441100d005013461306190b0320b25941c14882000c54100031504038560700340585903201c8114000984128102c01c0d03107130703040a9500da1080e034003203600001e100b950306508403c2404210940f50310818003031b10300c0ca05440c101d961024039211641c0c070580d2080700154420080d0300c7c09030002c8503081c2c0407910302140207028014581c0503580d0000d481c04c080424446540384001c40f94050241d10f85900b50352a65401c0030001200b80d00004c01e19840007045c880344a0308580644200b60002170008202e0751102c0900175441545521004503008a90224010400d940c10455400380502c024031564103884512044000d00138440e82c0070141d032a40d10b03030b0501c0202c0c510b2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 856543570 1250 856542320 856542329
    0xc0a0908120a020d092715030c08160f35010b0a0608010e0612070b0c0c09060609010804200a1e0807080d0e040905010f0f23060603070e06041e 63
    0x440d5040d8a03002001c0d040c0350485c06070b000c00340b8443d40b20703100c9000c040c3e0050307c42d40301035005160140d480385805003206c0a42d0181d60142d1140b00d14002220110f011840290348840329070003882ca00d801a8072000d6003092203800011040f40f010040c00c111361030f94450609006000200309110124148501403480d60021010850010014001110307100f402c6604a0310640d4240070210340b44030b03620305054a98100000301c510001d21403104038000102c07481d40315000c13900840303291941c004201251103158074080c00304442c070340000c02062680d031020110201894125405010300000240d600030380e500030300c01c9016504140f517051824403560101910f010307001884207505004082c2e81c0d400402d0907810400c0b0070b00c0740003c46601c0300d07042003818a0740300009100c1c4a1314921984d0103043d41140c904002440c0503004200c0400c1d1034040d62a450030f116031841c1c40c0e1100e205008090740020804418080301c04e81c1c80b030140c0c5500340100002d00020b80266003052a0105400140007507600 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 856544820 1250 856543570 856543577
    0x6041523070c050915060316090308031e07030c020a0f080412060e010506040501030309030b0405032107022509110c0a03080405010b3001060801061205010e060f0c0a0908120a020d 79
    0x1042c0c180f0b484603030403613401010700ba1900ca00c02004235030446056030315401c002c10000009c418800d000190b81ca1500c2c107452201e20700507030750703403042d8049045411101d00000182d01c0700100b0030104074048180310400e80a0007489261946403e2071040c111200c0d041211890303524a0300b0540320f0800c0c4150341d000a07040360184143d500d1501c0061070103100340005071070350041102260410000300200c40f45402c01c0ad040f00d542d503450042145404100721031140c0075004601c6601030300c010760001e0800c04102a459200543c0c02d086071100140380481410100e20320401c06418018010003488840301c1c42070750346807013a20703051416038290b40140407170034001c407003401034411113502c3d15901e45003003140f074140c00074a0b0500c180e0a50142402e5448694a540782480c0840d0340328103d0b040302c4105010b00000c1c04007400d03002d0700300d41e5103034120b4840075002c1c020380106003000d0020004020000d8589010a181034035040041d003030042c003069103c0500400105090364680500009800b08561704 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 856546070 1250 856544820 856544851
    0x2010b0d02091b070c090e10111905160516140f01031112040b06010f08060f060f0d05010b04031101020604110108090f060a0507030b06041523070c0509 67
    0x2400b2072041c003030191041003d0b006090400034401059800d8601060b000710031810002e0b5140e100e08010b250808141f60b240c003a01c0d1400c5017808141c0280000e034142400000d1510b944c0120104c00700103d83d481d2000c0010401103200c042d040480c010b00340d140500d000d400031200d40310030005003030301e07581c40700391540e80384484020a84d8942c03403e0201c0000038240030842109103500051144548195903002c20105401c0c031051114412545120380d000780c88003040400020800d64105004450155000c0b0306600e50603010f0800c00050001c45481400d05801c10882129003c151202600148140070300410108148140802e03103020815080c0094011428292038060580d150a000300381441f80c080c0126481ca4810000c011404986030283c0711513040925021021340410345039400024240008008207242100c1260100c408214002105524031301081d2044035119524805460480d03501c001040c091000030519a4440c40120203828140790401c4003807900500100d2000703030700380e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 856547320 1250 856546070 856546073
    0xf0c0609150f1302040903110c04021201050d02190905070f09080303150a1a2d0301030b04060b0a0303020c0a0f050607060207170703080f011a070813030507080a0302010b0d 76
    0x719401600840604040310841c0d842c01c00c43c20801a20141c02500245000602c1c3d041c50fa1041e80e0b10031400e034090030b5404c2c608402c000c00044c0d000700c1c040c02140307848070401000286440e00100d282d10707101a1020318040d40a01c01031510300ea941c1e010811003a01c1e1010454851b60140d01c0c10304020790350411001c80d90809245aa0300d000050881c003020444482d034a407156200c4500c1401040000403600c00e218030040c451b129600300c03088403070a607002c0245128a003007080c00038a6641c40d880f00c04500303680c03858440b01c0c01410068025204d407540d884880c456a11420f0790789000e0b5000750000c101452800c801e102d89489941c1c46030308541040c0320300780036581e41c8608032280f05421000143e2560224100381c94608202c018510034020006000340c00c158008098505c03510703090240c8100c581e82c600c0100041303403a0703007149501014100801c20000d100e0700058141c1d4043c0ca0488405242c80765540c500d8190183c02c06115a0f024180304030401d903090103607a903080d20aa8412002d800f25 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 856548570 1250 856547320 856547353
    0x1207050d1b0803060607030c17041806080a0f08120f0103030210053306030406060806091f1a0a0e01090605030307020f010e060f030f010603050f1303031505060f0c0609 74
    0x160405110f100c0c0080c1c9030b020f15108e01d02c8110751a400c01703070034190600c20100d07410196000c0e105181d00200d140d0701e2030380400a544217510480380c0c017102400c2c0c82d004070b1340c03035000800300088207d807003035420311051480307100c460349191240060501c240703841d505605001e0b240042001310b203200941810704121036000c202840100c0d500420400d4203548051440c504030796940300c001c1a400c25000301c1000144111504444c00f01c1e1f008409881064441901e10b43e101c551903546a6101c1181150401c00817130268004c81d122103240715081c1c08070608000240d80340b25280d201500c0280f9a03c01800030400303500c5040001c103002c40003546840d40a502003940005440c00650600c5001c1d140040e42d034581404a45003001d030400c01c00d5480c83d1041c00f0340c15060307080c003c1000080c0341000280c44000e0b6a6001e80c0605d11050040c030828038070b82c0e821405040201c44030f6003220a5103200148689030b034000340580e040280c8203d07446441d1f20461525180c0c008080d0207407a80000c0100b00c0c1401c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 856549820 1250 856548570 856548577
    0x9051e180a030e030a170702040e061315020408150412260a14090703033507050f0c0a020f01230c070512010c030b010e060a111207050d1b08 62
    0x10b1500308070b00d43c1000c450010382401064800982401c480c0c1c403d03c420f4205903c02805003501c00c44003084001e07822400c5a68a102c100c65110005030a17525220200d503101080c07158804412074051700d0039441d808818203003078007000b4000c0d0100700c0005000c100701000c030b0409120109803401210300d40c11148000300c6182c0082281900700c0e0410045590220300d9004018403050504a203403860070030003840780d0707074641910054000030141003d624280800c40c01445070040c1e60811140092618801d16140340c201034640410700c542004018003c0d150080504079101e841405440010150b0050015203021218054104000a00340c02e040211f030040024424040f00349503625602c07044003940c544230468121aa0161403030800c0000c2d80415040f0100c1083c40e507405201010364a401503c0c0c113030460080a41c002d04c24016003807031521490b50040e08000c06011a01c540c020000e14420651110074182c40c01d4001e4002c0d00d90b12500404030141c200454480310480b08034544a8964a01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 856551070 1250 856549820 856549823
    0x50d0207080d150609090501060801050f030a020a0b0903010b04020a0f3501090e2d1908040807060804080301061b0c0e22171309051e180a 61
    0x1640030640205200d03201058800c2c01051040820240c149229100c1c1000802c1c4a2100041c600184c0841c01c030304d15000341c504071368494030382164a90800c0100070440c400c802e101505132299400400c003598a08104800801080c11141d540d0345034030b81410700b5030350503084290140e0f00400602800550003c02d40c80038810381d1070b005000c003100030764580200f5042c211110905032810311040d009051182030728121110a00b0800c00c90b009985025100c00901004103000c0820410810340c0d0305003620b0040762880200c040d0340c0d90134803200c80320a0900200d68244e441c008042028486000c00700700307800c05132a103030a0025440c075059031122824803050040f0410003e40c040a1485001585540c0c0169a80314400400351030302c0e60059101e0410403079104454000e03031900450740346900e1070b20a02da141c0207651550920300203002c00c101c41c0e125141220521140900c00a18240c0c03920645000d6440d0340350040c640c0074003004a8400810280c54400b0f5281823408541e4a20740004010110a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 856552320 1250 856551070 856551097
    0x4b0f050d031b08030a05060f0d150e03120406060602070b1e07080f0304030215010501141e070213050405100e190303020c030c011d070f090e0319080703110a05 70
    0x108a055082c11400104074001c048100220500440946075040302d8451641980c0c4100750700072480401407505000f44029003941e580c000800128075203500050210704014003200d2401202c0e507500032401c9800c9400b03031240350b5620780c02e2020a03814401000204071913a0300ca4101000c40e40f02e920b5515000f034442402e10350004544080100320419510b0305503a12020a031649018200a5243d0300c0250031800005403420004c078280d80610701ca0741c07424290400c0c0034102440403140c03c2c1898069a5a9802900244140b9005944820b0403000c2103c0f83c2401103118102450160700c0e01590040e8110942d003400d0308018450400110300c200e11491b007403c0c1c0031455490070264000e1281c903d0354420b07408005040e21002005400200100848150040524009441c00d03900c54409000f400d14103445050200030307401c0d90350080c10202e6805030a5900d0280903140701103002c401c4c840c020010918440802c40382540520400011144101d4403c2c035044250030300801034850a10301d80c1c1503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 856553570 1250 856552320 856552337
    0x5070b0324040b0a14090c0a02030f07050c0d15110a05070b04030309021f02100e0706081e04031713050d050f0c0a0c230102074b0f050d03 61
    0x41e50b40d40c0180b5a0b500c00504141c4816803141207074941c1c4e00917044401d0089540c6004140c10540c0302d01141c001000d40d90241d420071200d4603121110354000d030020340d003a20545090084c2940e600d140a1a4030b07105101060440d40600010350654400a000100f0020148125010701d500071003101c0019074081c1035819a0750300d9240c203030020140040c0180d08516200354006c82c80711201104104050181c00b12560f03445120040310a40d00502105011900008002c001d01801a8101071308110000001180f929070303020149103c56040b41c040e030003c1c0c0300c4a220220300c504949416000118141030424440154035007a40d0b52140b81090001c00000040345000c0760011800e444072603c1800030b8400582d05420505000c035001d01520040e20340f05802c41030301118909404a0400060b0080c2c43c0c8030b454118038141c071b940841004e1421204c41c1c1c141402da12850481d0b51140c08c002a18955001390303204201071a05800d4000642c01f40c1d01480501495880d080c110300056490310b0000709 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 856554820 1250 856553570 856553641
    0xc1c120e210406090509130f05190503120c280c0213020d0c090311040f14070c0b090106031110020712050a0b24010c02040608150405070b03 62
    0x1d0501d12200d0480940350004a842000710168018001c42d04150b03a0b018020303446030f007082100d00c01a540c503191240c40c1000036001070030680036600294080c5041d102c100036080c81400006a0f0b01c0d408480c650000504a002c000c015070703051342c02002108059013001070039400205401212518800b0130900c481801c1c622901c070340403500d80a64060208996180c50110b510007a4000e02000303c8800c1c140200c180c41c051140344d00c002240d411000e00c030301c001c21000c1440000d10f0701c8412510502e48501d544030055210101d403c3c02035689680340200705a0600b40300341c1030400a0710b41c0c001641090410000b0a8020707500c41d40d042d00c00c17030705c0784116110a041a450007200360300545030b4500c091002c2c01030007408200021803d004070700130403859032070194100c00281000e401c04800c1058060031101c89d403080c1602d065061000d040020401d0310f807a141d925284c8404e10000115004408120030490180001d0b0010040000f248e82142003105c800171f00792a22a1a51003080c503810380740003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 856556070 1250 856554820 856554823
    0x604060b1f020303040b0919120509180601020705010534020a1d0702070605180d0b100503010f0b10080702011506030905010b01080c0d0f060b0f0c1c120e 68
    0x440d1441c441d121103030900624807000e5100e410845050f40d0410310200054284200030614080b25026415074150030170b034030354401c44112030640c03481040000500c0040001e442e64000145070540f0080000071074030b01000028a81000e54020504112060068480e500c100c107664040c882c02840079070f0782804000c042418240900d00002c0d40c0702108403030001e403413a5240c0400c2d035040b101580d03402d415510207000781e0369007a16100b0440001d4040012640300100401006801440240b03400210320355038548981d1000d003035a2420907000709403070801880c03400744180d4110407075400050141c4450500080d80f10b82e0550034050501c2510b2000a2045100b03501008811a1080c2160800c40e00c8610040040c10088030032500b42d807a045001107190302a0351200e103d491079044852038002a0040c9001a214006041500c1a16160007050340c004010140c08440b80003982261203140403031005240c4aa4508e248205030310100c000080d140d07215001c10a9540c0b40500460300030104110503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 856557320 1250 856556070 856556089
    0x15150a110303040309150503010305070306020d09020a031202011d0c010f110f0a1104050405250909081e0711090c2703011b020a020f040603050a0c090507030b030604060b 75
    0x802030703000000c00c2008058200c0901000d444d81d80c0c86072502d071160a0000e40340c503c001c1c0009856580000d40400008400f078004121602d44c51074041000c2407154085044464160400c65071055442c241141c0285c1c24132441080c4042c0000600c0c1d4010012900c6880d403078070861a0f41007200801710144054041c258412002c2101030403644001c84049034552103d06a400c21240380300d1a842c0c07500c1905e070030300456000302c4d0054040e0000c2c0d0500d60726040d20b11076180d400c4900f03400d80c1800140d0100148180724125004141103275640340010343e548900c0340d20801c01c0c20308000c10300146003c540c081e42c040c408440290780355002030700c4e404042400b900070320268006444c05408070007841c4003400380141c020305c0c0036030091020004040408c1a0012410707114001079010324109000361030f08030003175030448030013500009405840ba12742500f0301241c4031080e41c100000d24802c000c160118411507030703c505240f6040040c0c41c088000a82c031888040c2010300032070345880b42030079541d680710401c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 856558570 1250 856557320 856557347
    0x405040e0c12011413031e02120403030503100807030f0803070903151b020105070c0828090611120a050d110a030b1e0f010f02010f091a15150a 63
    0x9504a615902e400c074080d054024002d2102e603021008628900c0405840d603082c0b55040d120700128510b00700000c00034140340c0740c0ea44214800c142000241c40791280042c400b1310f001381c0d5007596a1070404070000d00c000c80c540c00111a540106400c002240c1605940d0844551210350301e656612a54030403210040c8940001d0710015104e48603219581e03059000c0444a0301500200d060900303540400e90884004513031040216202102031070003e8412001426a9082e49103003100181048541950400c0054001404076480b40c1003802515040400c450410030507900811040505010807146402640a000d081c040003103a1000c086405802020241d10140d20027902c418071a480140075200ca000c2d0702e8003d074804016141e003240074080c940000321000c1c0603198113a503c0d078011a51030940c85424402c555907a190500d48041c64011071b0030b118052440000e0326801118040384150700640a0b140702e80600000c0d03002ca031500d012030481d0300340c0d900c910390300c0d124000c0381611000d1a1400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 856559820 1250 856558570 856558579
    0x604080d0f0f020403060b0f030607030f020c0d0323070905220504050c130605100503100e0114011202030f0114060f1b0705030a08070605040f05031b010509030f0405040e0c 76
    0x1d0680c0b600c40a60b0281c81100e00034141880200c01100c14007a40e00140e0b07040720382503000b582c002110f81e802038000c81003d0908010041c0351015005170301d424001e2494201e00006d07141c1000c0c3e170150303040302000c020381200c5480c1d0b081c0a0900000c064901d600d91b02c1080c1c099225584e08403c0141501c0702020329034035031442402545883d191640d03c91841c0d1039003500c10340c400c6400302503400c0c2a103d080d064910243c0003110710300c9030003826595900011b044502d85a030b10071000c6285080445524006c08155001507000740e01c40700050015025003040050003441442041040c07120328002e9411500403004807808500d100c00454061711903036030755803080003000642020002c41070004102c003021400969214a886008164803800602005440d0b034005205490100c0c646a1101e5007251003591145a0344440c0e580781c600f5a008800001810083e9410340b406aa0303003800380640c007105d444061031a10b5a40c0818000c24002c41c090b140c00741c4d41e2021400840e500411464081c042c0c000c5c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 856561070 1250 856559820 856559831
    0x1806040506150d05101a0702040213081204150c020d030e010212280203070807110420090907030c0912060e01061217071a151c0501050115020604080d0f 67
    0x8001c0303000e0704d026a100f000c0c000321603030002000007040105170b2032420030300300341031030809642c013000065040b00740303282a54a5112400507140d0400c01500101a40300c0b00d0003511107140144040310020791000b044180201e0040c8400182d4805648070340c4240d25040c40e00c0c1d86028540100e1510620309065083e80c2000a051010f010500703240c00b0b170340c80c1c0801841b02d46210b110710490300c1c1d0007440c100601c0364400f4455100000c0041c0071001034440c001c0c00004c0d2403058100c12203c501004601d12804110000340f180d503e05144a10701d6000306103040910031541c0ea080001d1410400e84204543c0044031456a02084800d4100401454001c4001d0141e240c40e1b248805240b5102e84044403e2480d8820007030500c0341007019904116000304d5110350001121100100c0741d031000744411442d0300d2020720b40c405aa58039003100e0b61682d43c483d289c184001c8501d422170840e081030f0084801078544005040a495001504a50050303101c186191100783d0071a244001e8003a50303000c40201410034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 856562320 1250 856561070 856561087
    0x30b0604120b100317030c09060a080a1a2419050405091e011809050a030806030c0a0b190c0b160815030714060904020d0203090c180604050615 63
    0x20101189a40151141990780c3c985104100103406180b100408494500c012100320344070f0740700034552050300300c4801c5183c000760b2000114164041c00744040845c075403a0070b1100348481d901c9601541c0280c2400ca1180102c4900004c10b1039540040d00c1d23401420310044040940c02d048151a00c04510014a002500400c1c6000c0c0503500326000e100d000701d25490014208020030603507900085400a0b201880741d0030060b80c41c0c00c40d005040a81d4190b80c031000f250b00010420810995120300a039602c5002d81860402c15007013410520080d84a00824001800341100c15002c88890a4044110b50100402c1c094241c0c1d91982110000d06040f050104000d0340c84020300640d82110095550f1441c00d64800c01c400d83c40f0100421929010f81c0820014400c50059140000032810f00900c2c640c14010f2172000079090f82e0000d03a9a0420680101c18032407901d10411000f81c51036011a50300d102c4920038407040460701c1c8020a1a4482c81d100d030041055900c0f201c0038540000b0300e4010103951440c11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 856563570 1250 856562320 856562339
    0x1120519060e0601030e0a030c0209100315050a0c020706080604020702030c030601061e030501140d142a1c110d0209070c030f020712060e010b030f0a03090905040b07030903030b0604 80
    0x80f1201c1d8007003402d01c0d01e01414040f0108000d0311542d07041c0c442c42546046502840071000c002843e283e40e06c41c0300030001c0046200f0040c821040d0500700390204040c40e0014a45040d1b030107082120702075501c000e205014650b0000c01496020350203940058440e0003a00019143c06080f060961b00350082c900081603540d03000b2004d07035103400171402c01c4035059440c3c00100c1c00c4800034402d031001c407001030109415070b10307061b4100100980502e2018000340d41d0004a1810441c0f4011902b007050b000c0b031081150381c1c00348031000c9402c02044030f00a03451442000c480c2945110b00e100140b110030001081000c0d41d0702d509000d100150003803c5c181562070102d1003e4000440c4240c2980030603041e40f091802d85d44005103917030940703100304512406006580e035080b0140081604004155482e810b407500c05440c20004404114090401044049101e0501030803d0805800400105040004000c04913507500c48035074212449240006031400d007400c084004100c40c003012640803900150000d0801c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 856564820 1250 856563570 856563599
    0xf06050f0703060b04060c1b080607180801061a0c0106030503121f050f0f0f03061015050c07030b13140607030e0102090d02041104120627020112051906 67
    0xd81c0d01c0c200f290940318243c00400c0e004510400e070024040b000130900040040110941d0f41d0204803044d18110340b00d20302e050800c0803c0742c03820000b0300049111412000a400312000404924008202a5040c0030304c0300d4003980100348940d80c40d030000402020920702580501d000f107400c00240c0e038030b401d4502d41411555074203480c2d184240e9580c1440510b07590022200804545000700f81050003d0321005210110060400e0198024062500200c441d00c0a01c0407504c105218400300b5061401d040f0040c000d460f2003800881082400c0c02801424500080c0a2040d2a0007481c0b404080c0d1301d001043c020f074101100002c00c4480700034036804040b02c0016040b4040c0c0c00c0c50f1010300100c0b410071103490807030048004d40365000200f40801405410180d0043d2a80158200c000340751640f580c00030301e0302c03180003c4200c40c0c65644101c080c041c0c2000310f00740214488200b0b00448150120b0b0002040c0c1c006c54000110010b5884010400303900d051214040081206041030240a03a5084132180c2d520 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 856566070 1250 856564820 856564831
    0x5160c03051c050118050f07030b0d06050103150e0a05070605031009150e0702161401030b060c0d171e071e020709150815060d061a010f020303010f0509040f06050f 72
    0x314007071781d4410f8403050380a6144104008000300046a50b914402c8003d040025a96500310360311444000c0421454042d0343c0c06180107901000c00b0b481c0240d120011034461401c032440035081001204005800803a00c1c104072842c62030031945989032248540d420684a900a0841610300074091440b05251490034040b6a074070031441c48160360b0700d401640c0fa600080348008440e02d440030107001102c80701812000e80301c4180b60001e102d290b2800405c2c105d07440700c111400294071046202200340e42c02940f02c09520a0414100448e08107020406d811807140130f91500c241440500040b40e40d032060301172101c01d407266000043e000c548200041e4480f44540118841281407e4140f003d00840e0a250411110180000d2078410020f82241880c1c0700050b088580c800c1d10740744180c0c00700710980515103c130003d182c6c2c0f40200c0302c0e031400054a4100300103c03900c1590803c2c401000401d04440c41001260310940344078442d9601c508d0a00440c0c0c10420303000304550b18240502c5050307441001c04a1282 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 856567320 1250 856566070 856566089
    0x360d02010f020408070501030207050c2106010503010b150d41040503072a0b0d0f0c1d031e07050a0b04050306010306020f0c0f0c1305160c03051c0501 66
    0x4407a402084040c1e1145000d200c0495101980c02c0040d54800d5004244403800b45c020340740200c0c0010009500c000080070410106840070410040501041c0902401031400318000c200a5a4007004992120004114018804008104201e45010f1508146000c64000c154101c882102503c220f80c49413881a81c2d030503101180d0000c00c1d030000007440e60341c00b454000300118140000c0d5a41c84500402587c0000d80c1c000d100d40551019107000c080d003201030084c1091280d160984400b403001110350000c00c81c121307281040f4101c0c4841c4d4100240484042d501035105140b4801040801c0c60600b50780b404985e0b40170010003003900c1040200c0c0010544508545500b526a48c855880c0301d81c2c000e0303006255040d0044d000400001c0c03440d80c0107002014901099600b090780f0314455904010035602202d265401c800e02c050032600e01203480120076a44198100920304200c1000309204202d40034550a0054801d00d40c020b06000b8402d0b81c00c805200c8220000c4910302c0e04600000d00820310405141 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 856568570 1250 856567320 856567331
    0x203030d0c1d012124150305060d030903080c0109080f03010f060f0824120604020f181303020c130b0108010b030c03060f01031d011e02040806360d0201 67
    0x1a41c4510303011400c031900b2000d00c0003ca04d05042040051602551804d00c288500c541c0c1c60344600e09015900091104900e060203541c0c05a01c00307016034400500140c030a1155442e6480003c4d0010000d0082e250003400300c0343c80340c8003910010300420307001f503000c0c0c007124010a4540c2d0400c440c0f0002c40c1a540b841104041b41c9548100c1502c1e42d600700c40b40b81e00880c10032000110882c00178007505403d01d860502c4d007492243c401c40403034100c801d112268641c0c1d41001b401c200540c14280c030341121602042da0007031440b0000100407100440050500641e141003d80701d001818070030865102145c10007041c056103100c65074900c07030041002c1101c20340812204000010141c010a06491040840707a0805245070f03240f4040006118050200d40e050598440525040c00303405501c003200c2000d803000014551f0b60550102c855850000001c0b4a01401048144100103001c114a5000b224400c010042c2149400c424004042c2c0308000710009011807110320070844c00040e40e284841c440e174008204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 856569820 1250 856568570 856568627
    0x1c090513200307020d0516020d030c05010b01140703030b04150e010e090a080904150906090c031d070e0703090b0c07061a150d091b1505070308130203030d0c 69
    0x71603010480d59200540c01c100c0100d05194010070003840c1003803150f0744090828209900040190001c01d40507000102115074100401209100344202e0050900b4a1101e004901d800c0202030311851034000c00701034440c103100c509134032541c01c8654412090145101403544410540202a009105600004003842c0106070011008a00100807a400808461400148100303104c042c0c03010450482907040725000004c0c10750210b11491000c0c042000000c00c644140b4a0b00a0903038111100c03500780e03030344d07003080b40e9070304000000316007040340c010b215080700c9982c44800070380042695002c040c1040d403451081105544501c402050350a00c41d0008104480101420200c9102c0b8582e0360707074111000c0f00800c030150440602402d030003401078201040103e0180d0703450302d00442107001c04801c5001c2040601000c8445005c202d10700409140090415440b62001415864094001d24003041e01d0700c0c0340410340d1020300c102c030341c240a100e100340000c000c14a0010300740d00401816124034820508040d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 856571070 1250 856569820 856569881
    0x3170f010308030c030c07050109030906020d080108150919240b180a090218060f01020d091e05060a08010311121f06030b10261c090513 60
    0x40c180c903004400c0034219507844225581990001c0c00c036903402c0b20244980c1000031401d02419249902c00c0e50394004003407038400060714000f28141d419050010409c0188012400062142100c0c01102403103855034030340c10300040c01c2440d0a80d0750811100d6902c204c40c1804074562500d401d440003040c020481990309a9240c040314040914544d106000891042201c106a14240c0d0050300e00900041c20b596207600080d8100702e0403031080200b0aa04d410042e06150286688402a00a00203004807400f50400144050030500400480c1140200d4801d440c005809000c80588400b520040d0749801d505809020046c0901c0100c0e02402000c48014180c185091201d01d1030444000410041044c0080415108020600d034504a965510000040354150303008034040d002c40c4150102d69810958800080c2c92a015040341c1090100c4180141d240001964505640c40400c1c2c0303031824421030801c80702544d00f6403115a0000010f01c00110b070190b5648140409401e04041244401c006881030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 856572320 1250 856571070 856571101
    0x1d0319050304050a0f0201050409060f0311090f1b0403080304080d2403060f020c0607092c0105460f0509040b0c09030a060b01081b0f21040317 63
    0x10003c0e0400965a00041c8007004401d405c02d105050141c20300d038860119000321042544010300300550710004106020741c62032005032421007912003000e41d10700004074103400c200c058030b15808400c4041d00036100c80319160640b8084d5911500c02544c030b04143c1454803291300f00d00020b0b9000c81c9040000810340141e040c04201407901c500d014450185141c58200081c00d840410740d0a0a80070084040142801e2010710b108a229031502480c4a0620221b100c001c02d0760120381c07014950420310f101229445050722411a03c0454001d00f9981120154543c500c405880d0030180704545410f1041c240552032009106a80c403000015200395102c10416004903d440b6198100c42140003080104826240b15940a5002e06000b440c1c145040d002c207181c03a0a1860036604d0f00d80d100e8400780c42d980c0c8a445107400910302c1c0000b0140d55540d0100f40d04620554480c807950a1001410510248058140c6c0104450a0f4000c240a192900380500b000c400c0304031050001d49400d001a1180c405064a03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 856573570 1250 856572320 856572323
    0x6020c06090606240c010e0f25090b0d0c03033c08041e03050d1406220609090c0509070f0207090c0302070b130b01090b010e06030a1d0319050304 64
    0x7000c42401e088130081c3c001c0c0f4003404120969500c20000340301a0f030424041c025140020100031b01c3d103215030742c1c2c02ca4205000381452040741c40181c2c05403500c88075541c0400094802c00e11000480c146820001480e405120100800c2010700d44000014180c10848034054410314403011324200d8146841210b01c9102e80b00c40c1c5d4500c15620842440482c42403034843c1d0300600c540e800c071403213812019001400c2620040c04a00007400022680d030112194096441c60440601c80d404a6080150000c2e5000d40b1206500314112620060210040c4091b0410001800d900600b08142c0889080c01c920b104814000c1c00c2c02a0b59600c0450b40c2103101d03080b031126080f2a5405481e4039410401c0c11809001e851846200f0550280580b41c041111300d800f160080f01704001e640c2d6215100d00d44100c041c42c0591094859034501420700b40a83d030040c078025080c2504035042035680d40c6443c2100000c0840001c1c0907221403565503010b0381840000010243c00b50780004048981d54400030423a168801103c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 856574820 1250 856573570 856573579
    0x70c0308010e040c170f0d03090f060b041830021c020a3e060a0302070507090627110703031a100201201819030501020706020c06090606 60
    0x40110030450801c4a403c94440c82041190a03500d8042c0740e096078030281c112a1a8104503c0d411820f9010415080700000f00d0600340a0114592103800c0315984010024042d00e407144607090460380e80d0b9100c4001b0b4202c0b92203d480000190400105002c0d9546c914100c1c80023002451000071644040e03408420308542c000c222035802c6070000c6201c1c54002550038203610035050b14000141d10080e290480e41c61f940040340c2208044440c0c0f01e401d00c018a028442c58010040e40701c4151a02c42c11102015010b09000d0780c1c49469103410b5180095030707030002551070b14103100403903002030f4030025050000f80e5902c8503804201070000c100850b110090460541c40080011000107806604901286452000910901a018004183e50081480614006035501c9850307960745001e00e17801031a95650203a03501c1c00c19041205451a01c403030304003628881e600c000c008000340c0064203000b6010395031000003903495052510388031002c0d411001042c0303405e02402000915000780004c03040d11418000f0b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 856576070 1250 856574820 856574837
    0x406050a03032007090c2c100203130305060f09010b092e03110a090b0303090f0d08180f0f01021b18010b03041707080a03150905040c0e070c03 63
    0x59055030300505100b02c0e001c00142c4515040e5070f24105000c010014251280041103820150b4801006489188001500032401d4102020903164074079520301d0000041d10152413a610b0f0713800683c9540190124000790340f5181101008020020070034070b02070002c96003102e0141d2901d070006400d030348107410781c2030300100440001051030307454190003403440101000700c205e40d580600f500e00400d02581c0017610b603d14074148184150500702d4000008040c000e0381003007101001d00000f034980c80345004251050ba01546880c42503a00c0325803000c1c01c03640c000c0d03007030359200c7c0d501880704200402c00814038460400505020040c0c2030508500301c220300c059020303094104100c00810a103000034031719650031890507050310b901002c40d95003039070103000c3c41500980c1b01c2c03030a441d1081c80113054402c0ba800241040c8444000101c2c0c210030b0b514680c030242800704013074551101c00741c0600400c1c0d00001419082c54280000d002c070150902c402d449064400014a81d5020001c2d01c400c100084018005031022 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 856577320 1250 856576070 856576073
    0x30050403120f030204030602130e100305060103080c011415040606050405180429040507120b0c0307021207080d0605031908070203070503011b0905030a0c0905091c030606030b0406050a03 82
    0x410b400c85410b102410014241a120f031604800ca8200c06003aa482402800042c4056500305031200c0d4440c82a1080b51221f82c119078440c1d072294011b06c80200303503040100d000d40f0014000e421124200c1c0403019060658a002c07000c403444203150b82403481c0501e2a04902080c454031a4003250255003015240e40200c0c07442c6041582104c03c0200150b0307075106024448680031100302c0a0303294a001d020050100d0382800c0c10440e05100d490b601c9110103501c010036807000188a181c00b142d00101c0c0c00700c481c1d207954480ca020b0f03040041c510b4502c2c5040f1800141002004800c101030030014040303c81c101300c00307074036041815074440d412503a5001c3c08032241144400510008014040584003070b080c0c840c11584c075404607081d24a81030041d004420311030f0510120a0340711081d0001804220003c3c90144802d03200c030a01d2810601420702d0301a00d030f5000440e948030400000412a450410150049002e90b41c010001c0045000744000207050459605003032a042c0035140c03c0e103000800794a440c80c9903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 856578570 1250 856577320 856577327
    0x20708090f031203071808191e0b13050609010515040b01050d060e0103140706080a09110a0315060b0316050703210f0f05151207033005040312 63
    0x14030021961503c201c0421000c42c69404024600895030750300c80c040c10140d00d40000011903242d8100952581c80008a50350010040f48007006643e080286800a0315150408151211001708054040146401401910344030b800f02210540d001e0011780d0b00640700d40200b2802d0b5a0300341c85220140040c9090b140c050b180603800301c030003030701d05040141c81c00c0310800d410f500ba149a603110200c041007200041050001c004c1c00100030102000c041d101c02810032401812084019207c80ba10964a540181c1040300c0a4014588484000c1065801654900e03141c629015100d2501d401c5505101c0001021030103e02580e004e80500001c405a580e0700240c102c0740390b040000241e08000c04440760030401c0d5a071030308030401110001d2001c00c8150442c6943c1c03040d035100c2c1c4c6520703454910381002c21980f400302400c0c4801c0c1d58412103401c01d200380c071031941c9da00d480c806802c0541140540142840b510742c4c102c402c4c00710002c1c0780c0c0c651401ca40350014140e03501e001d68030010b0883c0c028046c03400e003410710 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 856579820 1250 856578570 856578589
    0xc12060f03031210050117040c030807060b0d050d02010606020708060115051b0312130b150f040e100b030c061206030703060e010b190b0f0912010507021501060302070809 75
    0x15089034204951a5501180007005948144c0f203c0560038092041c0e580c400c0c170314105400c620041e9102810266140c2d01c0a00c810300c17001d0844500032411701d00f0088260881810140000c0116000e0140340c1802a103500300c440e0040055072921400143e468004107038030045030b884801418060b844c00c1040345101c0251901d40701000300c104561030449100340010010400701000440e120503501c0440c10b00e40c1c101905038007c141d61164840c00242e042031080b503200c03050080501c0300400510100c2c00b00d41012040c65801400d1000003490070000180c10361400b1380700703a028400700301d4400c2403540300d80d6808a50303a0051003c0245410f4000300e00c40e002e80041010b000c1b00c07a001c0d603a80b9081d0440c0d400654032070169444014040c06860000c40b14403c90300c01141e1702c6a0140380c0340c09103144c0d10036012460000b070f4003c9207400040d501c8480205204d01701b20001d121918000b20001e4075201001504661804442c0001c14402d100b84281c446050b4881d400510304105801040324a50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 856581070 1250 856579820 856579849
    0x1e0610110703020a08030a0f02152206020a1101050a020306090f09121b060703050c19020c0a090501061d241c050604060902130603150e0103080702090c1206 69
    0x807550a0010058850030f220720020b18102d00a151240410003004044600000522046620422448020b100c0b103554407030300900e80e60044103151001c0c00c0d102d02d4185620358060141071000c521402c802d9006080e16000d04a00c6000b00145da50742c0e42000201e0000b0f44249420441e0200014208403070a00a1134024904100f12042d030320900341201d4055000b9034042e8011101c4c4000384e00c46003410001c0384e401400e1802c0c18000c52a007c80104114010601242044c034801071400c00c10074001d11030500710000242902400503120700d01c120240c5001c1c030418001501850041c1e01c403c001186110b0340701401490800c2c00e071a03068082441c010b04800c40070960303204101422240c181200c11680140b101c00d408201c902c1c2031010041240d08650040c0724940c010004049186840200d03441030303c2c11401c0000350341610501da401d50a00c2c1e900310070740746400d0000200600145d0806000350a1080f1855109a900e010303482c0181d000710300409041001c2003001c1800361034070003506039056 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 856582320 1250 856581070 856581073
    0x20f01090c14120d094416090b040f0b030a0201050d0209060d0e19080f0a210903020d020a0503040308131d1501140d240e01150c030f12020906030a02031e061011 71
    0x8207c03002007000c95604590040100c0d50381c4055480046c00c01b4008d12040ca040d0880410092100002007a100c4900f494006e0420030005001040f003002c0c1e90545404140240c401511881e00f002041c00411118207910a80d01c22404981e80c484018a010031b44540e0050ba00ca040418842c40001c0c1d41c0c02c82c0e0019001d00650810049040d039441840018010385d000d00410b403112503040290510060700b00c40400c5410212030900464030000803501201e920956150b52070b0314104490840303544030707042000011000c0c00c0c01182482002543d074003500c030f1080b1001c81c1d21440e10054520324414606052460fa050110305e010b196940d0121100c03080d030540000030320320540868212079005030458280c0c40016001808000d500c001c1c0f14040c0b800604028003000e00603180503241002d080c1e1003000b040078007103842c5408012a0140c444510000d00b40d1030312401c040300000702940040310b2642d02e5607100000c581c1d8261400e02010f00800e000b0304080d0328549039410499036111146241003d6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 856583570 1250 856582320 856582333
    0x6061c0605040f09060e0303070c0b0411090f0a0f060f0501030905010624021c0e091503060f061c120507021c05010c020f01090c14120d0944 62
    0x1640302c07805850348540b00b941000844100910344a001c88043c400d204205a0080c0200064140c20000001000e40c00a802e54443e81c2c461030010140c40b1100c1844d60400e40303010600035801052055117006484000043c0005000324540104a42451007204440403904600300080d501a50200e590180208004103101d9240e600716418229280030303000c070b8010b0201950500c19418000c42c042a03002040e03c140c107240c1c5204c020080d0a81c90222881140311380301207002100040d403507900806000d41615021303c0c006800003503441c41201d09600034016261036070303c10342c044445440c41c0c65122035100020040d1120444850308440c0c1c00300e810001c10303108041a0110503d0354030381d00e4802d44c004503128205003002420180c0302894800581c1c1040c0c200c0c00000d600442c1d007019035052404490318050490009461f904140980c0700c0c203270280300c1c070309149960f000b4072480c00d0b00c0c40d10071603521200f507004200060f081401c940081302104454051152240c0854a170031802448044844 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 856584820 1250 856583570 856583579
    0x606131e020315191d041115070611070c060f0c150207060f0221040c140409020904120908030c0601121407080601060813030507021302220906090506061c06 69
    0xa8034285078454580f91540900d04211441c0e8004407280b481d17290425200003403c140e520001c11032803c44041c0e2042880320465400c20451500342c0b241550849400c2c0600c401d006481803541d8007240301518ae02d030440c500410410b009440d140c10310b1203190345444a007009500e40c500c803181c4003d205000a60208203000104070f550180201c1d08241d503100507541c04409110380060104803001600301081281003001051040c071080040713504948141d51300064000001b40100801000250f0201004040c0418451040d0484101d440c0b10307290205200d8070b171032070a69640500180c102c02a80204018404400d8840c04408503600c29822503001001c4070040d5400d2420f00e400c08891907004100401a45a1101781c0c10b41040d086401d40030b02007001e4500400c18425844044c1c055030f091a01c81042806c654100d8030040e0050702100d40303c0700500d0041c4044440d40c8614110541081b40120b060151440b48074002c4100074556031511054410100070a10303030030003060500b40d840c9000034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 856586070 1250 856584820 856584829
    0x15070807111f05030907060f0f030b01020c0411073e13090510150506040509070c06020a0c02130b0102070509040606030b34050a0c0510060303020606131e020315 71
    0x141c2c0800d038032440d4a901d0209901803414101e50f01c000f041214482c2540c0720b094000d00c0700030006003640307804241541000d0041c1c0c5003800645440d50020b150640c1800310f0003580b00540641e074891104200c18020440c0c3d81d400c228080c50a0300c2d01e5841020682c01491028101040c2501c03003e0110400024100c2031141280d48044050321b05400c040c8404501010f107120319071458400d4100c410160b400d280214a490055028490007031000d0004201914020300018440640c1700f20159502d04140c1c030020134101010f8001c90081561a18a1460140c2c502600ca4055810f034000c1c8411894102002109130001e1300507201c20796500c0c3c02001040c11a40040d12a80400600090707010044118800c5043e0443d20484c040c0094040c8105840d40720040b50420b0f0442d00d40300c106402c881c01e01c3c0d4108a01040320400561900900100301500031800501c200404c8070148420741d0503403494400e07039044081310502d8a00c0050100718803401d6034040d60300b001900403046010701d20100804c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 856587320 1250 856586070 856586119
    0xe01021b090126240108030a020717100c020123060d060518070f030b0115080a110c0f16050907080601030515190e0703020c1002070501021213021507080711 69
    0x119480220744440495040c0f050401301e00600711500258544a180032000351154964000d40d03450700e5103002001c05008041245441c444c0f2145020000c0b1a08510043d000705802c000d0180c0061869500d640721b83c803d8050b5621444000d0030700c54800406a03a81c000030140180304c03c40e2500308005240800c2c02c204800c402500c000980b0981507800d50600304002c01c0305078480202c1c2c203103035002802e8071648448a6a00003c6c0c4180101d07060790b00400e4900075015025a001c0d2520440c0081d04001070006242c40c2c01c01880c0f01c481d241c0c1910740040c0300000301d0440709440824801c80105102d94800e900003036000d0700c0b0302d07015605101110005547c104400750014912101d401084c80600e00d40c0101c0b50b006012800c045243c82c80410780c9a0b25410384503088881e072070740032902d04140402901200d20700d04c001c80c40d4600c4c1c0e18001c850b551450310130413001ea0180d0440c100c00131650000400f120682c0342c100b1190b905101169643c070f0030382508138010981080311540b400460640820300d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 856588570 1250 856587320 856587343
    0x20c2121040606050d050a02040c0917030405090c12010b1309020d0c030e03091806030f030a091403010603230106080f010903030b150703050f04150e01021b090126 72
    0x10046142402d0524009449440c1c0000e40314002c801407090000301e00213041000c0540c1694085050700c0b010400f43d880403020b40c01210950740c2c002282d000f0050100041013034172411102d83c0074545400358049001d00940815065441c414001489803802c00000340110000c243c00707000c01c2c0d0b40c03130303406407806c7c9d03042030990a0708681c482400741c5505405020700100a07494134011810420310700001155500585203510400d601e000201e8682d882c18808048401e20350001c99948010006c80246070a04602c02c40b00c0361040000018600d2506008000450b90000c0003a0300442c0840080c130581c410320080d0485a40d640c400c005100041841445100703c40c0c0000011410400d003009416541c0340d00b0818422043c2802088141c48a1016a400c094040c501152642c1c44400303000d2513031107540c121000750000c8040410380345078070000c0700d44968000e9090b20015102d544200050000700003180b0381c03081c80e00300107024040c04081e495404a0b80e4207017081c4a07200d038409140c20714851130b49 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 856589820 1250 856588570 856588627
    0x23040b1003081c0b1f111624020106290912010501140609030d11150f01062c010509010306030b040b100f0b0706020a0917010903020c04020c21 63
    0x401402c1c3c0391481461410702e0700b42ca04908120020445801d0741850640c00000e2040f94000c4115007039041052a200c2280316540da03004941b100f020440010121449004d00d0401070b2031030b00c66601c10701030078048607000808003444c0c1120a001608c500810005031916410900c581c24140ea00c21420880d107034103200002505504100c5498481c9186448080c0100820050b00034242c40015000b052132400d440c3c0080100fa08042c15804c1440c0403146200300710b290410f22407401464490310307040b6041e64880c8800c54070100300c1c03204000e401501190305a86070300c840c0b406071b50003031004001d904414500040e29980b2a544d5026104041d1800c0d0b47c806c6030718007003240d11085074200750301603d04001890035482c0b4020460178544140600141520740104517070a065000d0210340010344420700b0819030040d42e564006001f40000c040c02d40046c490101c0b030107080d0816208503000c40c4510b5015205603864030328207120364480d145111007085410000fa40e10210b0500700c01155482001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 856591070 1250 856589820 856589857
    0xd05060f0a0606230901180b03190b18061f0309020f010207030b0a0e19030807171e1015050a02070503070b2208060a0204050423040b100308 62
    0x80000700b102c0450f04000140555038440c0d40c0d00c404100c8800e5110301018101554442c8880300484032907d6084100400480c00000414850b194802030341c415411380c0f8000b8000c14440400034181d031009956250098110700e91000080b840d00c203e04c0e80940e001d8141002820390320071010300305041c50301d45000a541c0d00c00b41c008625207085400d041d034009100900402d0f041d522080e1701d002c4054440703442c440e074449403014042010301c07a105448615080b403002e5002513081c0500300a070111560400900c41010301c1c01d101d03e0600e402c44c080c01803140600000100d50b2501d05010303201030444602030383c0703442d40014a1000b4901c0b4581d420742c0f60351102d03242c00026501034a4543c540e00042e21a4003c01018040d80000e0001d44010a6910b00402160300502d49a812001c3c40c1d600405800d020f00e1007003140c0b12400c4c1e00100226042580e04010708004200781c0f01850301c0038000441d1071720388000030402107001c01045c180c005405912a81c5541da90340d40d00f01151b4800700480d06140d0208 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 856592320 1250 856591070 856591081
    0x90402040b0a30121b020301050c04180504031d0109090e0312150906040f1b0809070512030327100c080108010b0f010f0e0a0807082b0e0d05060f 64
    0x43e5000c3c40c80d009210310074103800aa90fa500c1016081301c070800c41001920303814804e200f000d00d044a00f00a4010b0000c100a0502c0c3d400384c4c1080d4064005d1a01a20340c00c210440704291511800d803190b5015a20000c0d05015600d0388840080c0a107012170402070191000325001d81248650040000c1c907800455480311070070480c002c8400010310054005c0071140b2103003070b141c0310100303550384c80002120005450801048200d004014541000d4011078010803090b0205030043e5201d0b000d0001c0404580500d0340d00c00c00c20405800d82d03252001e4075041840490134101c8410100000b548410359080300065039100e40f40d1a181903034003031104140d260008078042941000103039014000d808002d0001110005c0811880d90002404904005480d42018401803154100241102005202107043c0e903682e0400c960754440c40c050000107024402c0c644810f01900004244014001050080c00340740c06407083e1030240880d064175802204c5240c00900280080c01003034403401e2011120b90003400c10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 856593570 1250 856592320 856592369
    0x1e100509100303020705091b12010503120901050d020f1b030a08060901060c030c06020c0706020a1704210c0b0705030a020d091208090a080a03020f1603080306090402040b0a 76
    0x40c1c4012040d00780103400b4000700c0da0110b032080c180c88056034041444e0b12103001c4034002c040c051343ca103900904c0100d03415231066050409107048036800c80071100000a58043c1c2d0407248200809540070071000c00c524008200c1075000390802c48000283c0c00e06021003650507200b018551540c0c0c1805030000200f884c00203410072456070304102d09561040e401d40c18a0350141c0b140c0c41c80b9001a0910410308407440030000150115000c60819500f9103020390794402d000f941d101c1851104a03640c070402c000000b440d00c10b0070103640440d05004c2c6403100341c8401d1811041d515245200544040411040100d14061824010020148103100640c0c1e60300f00f03810007d00300300042c51401d081082407541003011410a00c02891416001140380780d841ea0080c000881241303042d80700d00094040d03000244185a00402c60b840403492410031f0b115400c00b000d800030f0900d2071600000b000c140042c00400c616040c8081c130258010300c0503100042c5020460001034010841d036000c42034103240c1c2450110003428 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 856594820 1250 856593570 856593589
    0xf0a0813083f01090b190f06030f0c0806100c0b01060806040b0f13020a180f15110a06050702010906050c0405040609050f0403030b0109030c090203070905030d080106081e1005 77
    0x10282540551504141e03400441c014040c81804d0706030f030b181c020301031055a5840c0619510035080c61a0b40c1110f584d0f000380ca802802900c81c0300c1c082441c00700e1600c0018040e010b001d50402496586004607541c040401007030a0303910701003000300500c0150a42c0024030402499018100c42d0303d52901d40d02d400310421094410100605000c0c00380c1c13055100e0992a50190342614103d40c0300c0250b255003009074104c0341012000400c01011246010010700780000802c140c0903910011882504c0c008962029107212040402d511059800b1200c41300c042404c0e80e11081e0407002d144004280303105151144400d0f18020394401c5c1c2861700c0050100240c0c82c05204040040c046010180134034a080c0c140e41e10140b40042000d4241a2030f401e445580e80e100c1c40300c0e031002c0d69002045003046600e49070410700940040340c600340072940b640d00c0400c26180c0020320380d11040185c1c0d00d20450b0382c2440000c891140019001c0c5803000c084265188440c07144c1d025840c07042d41119031031141e440c0f4240070040c4081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 856596070 1250 856594820 856594897
    0x12150409030903080313020405041b052b0303020c06160305090c1503040804030803041208010e0108031b100e0604110609130903020309090711120f0a081308 69
    0x5140c94140d90001e90404403000841e50802c40c0035840390b50f200d2900f5003800310309000030343c02480e09042004110a419001d080744402461040c201030b00c800c144504104903158410030300081000d01305643c4021609910072503c03e18004d8140035400341c14524148059a6144010f442c000000150650601c07407280c0c0310012800900c0e1442c500390108240c01d420074641002d804000000a090002c0081141c00855010004581d2803605040c50400034007012407000000741404000543d03410b415500c54140c0340306d68003651611200701d41d0b4400000607a142c070b800500901804202e810024800c407070b805124413014000034038080c905414141d0210700564801c4405000b0900c1d02c1e1141c401070304106180000c009003501c42800d090f85540168070045901c0318a80040000d110b601200e08891403000760700700c0d40c070030219003c03c01c514050241d04086010b8184000d60002d0f1050164079004a0b10b402c5003c00d030388143d150300c0d100e60f000358144810280d0074000e8518055210703a80100c0d08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 856597320 1250 856596070 856596079
    0x121e111602010c1b030c03050c030d050306060c120c07061404120b09011410080d080f060d0c0e04110907050a020604020d022e18051503090a081215 65
    0x203054010422410400400041e0400074005070800820031801c5103400b141c0340e090300501c44a80d0f2450410300f91011800212050700401c1d8070901e0174100022031501c0412582c0703400b41190f660b034081c000a50070482c41e800b91b80c400c4d044040e120380440c1000b060400070341000b44c034101c2d00700a00500b41c88200c00586407920402c0000b04500411304449510300e5600541d1003074184c41d0000100e014000302c000f080c92150348003041c0400210424042e10440d0002e9041d5a004504904c00352103000c01141ca0311a058501c82c0015058541644003034200b900c44d89440b410542c541662104e210300440702228054101250302d8100d1504041c0a0740c44840c0349012407400e02c94482c025203d00001e000240640241c4030513504550300d1030285070001d00c000e000c84074280e03503070410000d601414156040100d0040a0181000c0d000300d010b42050340c80103441a4000640070010715050344c001480e0b0005401450000c50014001000038104030503409400155801c2c40d0001e04801000f40002030f214 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 856598570 1250 856597320 856597327
    0x70b090c031b0d030311130602011d01020a0c060c0302070803090604030e1909200d050105091803070b090c09040b0106080708160e040b0316030b0a200a121e11 70
    0x82d42e482030501145103515280104a41e11400d0340d04116001c0c0b80c8034684560010400885c400b981544000d84685808030b40ca01c0a05d01e0702d440508034482c0507a0701c07000502c150142c1000c20241e400c000c0050350703a80740061400c41c0d1501c0341075480d001907502040a4100302c0601c0306140d0300100e075500d803880407242c900704d0b04501044190711056038400c1c506441c0d16035208280300145004018800210721074441e688189213004040108000d0160034821a07074140455a40380c06812800c4072003900300001c51034600c81c0c1d2200801c800d0014209810345c401c0c4400006e258603202d00d070a0285108405034007083d418484040d04402c401806e44081002545c10440903000e014031036410303c955414820502c000200110b4060208900b0003501885103448002c1c102c0f104028040c11203004480c2c944240d280c268412003580c0e610f010121846503440f410603913079454500202220030060400c0080540708184060554081c40c00d00f00c0045002546406580c4071800342003180000c01502615 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 856599820 1250 856598570 856598623
    0x9020307020303040326070f02010e01150b13170a03170403092102041104060305010f05090f0a02040f030b0601080a0b0109180906050c04031a070c0b06030102070b090c03 75
    0x1500d000051001e0100002d021b128080c691403011401c4050101c1104521030b4546060301521900107d5440300c0158a406007180c2112018401c40869010729203101e00c3c10791a0488500d516080200300c00394108002400060005540d01481500342106e00a000c0c1c0880c0b9060103000010f2002c0e50010404190381000006541f0032529400c1d13400201051482c5054210100c41d605c00c3e40710f00941080c40c0400507818030400c1c8002d04200c6210760350a1280f0ba0b01d13070b007859480540510a081c0c1100358540400c1101c039111124981c0004010001400c10790b070b59480c1903c0c90019803041d10451032900502285591042c0340d0743e80035142000a00c940408500001d00c0c0d8031a5100f03890729002e141e055000c6a034695017200144680002080c442400e03d41082e072902d81c0584400c460f04c00c03101e01c10f1081503842d2030529200708041d4580b1041c0203099211000e1380c0000a202030740c0f41d5030802072180060844541c0f280500d4121004001030031000051501e09000340110100c044800e041014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 856601070 1250 856599820 856599823
    0x1d100f140901140a050c0a08090301200a05161b03150b030a02040b0301020d240501020f152e1e14040c0318031116210302070f060801050a0902030702 66
    0xb070388003c520401c660320b1052a43c115142c0c0945003e0030003500415011105000003000030b01007103a0128000c0001050140b1403000000380d1445403c3c44c00003d0042e141c10f58003800c050304104d11444003000344580d0035030b96a155001440445088025903040c11700078401019158040c40b07a103a0807c114590101c000240da8655180b070080c4110340350b00e504025502d013074050303544050140d003045c4040c0400300310306807204655076884482c2480e00340340080c8561002900140d0484442e01401d041d02074203030802503074803004007142400c10a40001c42030310b50000b4100708500018070329110020381000840c5101d1244d40b5100159042144028019040705410030950080112400240000010819400b17400c010003241d0340748034a5804c00c024150444980c0703001910b0141610f0105010305c1c4207a09418041c024080081d614400c80400090100c56100355a8000c0c0110340900c1e6603001d266088200039017141000518201c0100003078202060020081c5c8240c1400354218034040c10000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 856602320 1250 856601070 856601087
    0x4060b1905160b0a050702010203040b0403110c100e0102010b270432060c120403050a02010609050a0b0a0b0702060a12020405030d1e0801050a061d100f140901 70
    0x18003412140641a1001a008a0840e40da900d040e000c0c07001120481d0401c4001c4550803030399200e00d903080c2000101c03240e106200b1a44103039440305c010a0241c81e25207003216000c80c8805c1800c001d00c0340c0c89501c800c07a41e0381da5014611101541d60f038440c103000e11000a003903495007105180a08003074403480803091a9500300c41d0071951002d049525580e00c60400420301141080100d15000314014150300c100c526014039190900d902d012500503442d03c0040e00d07498030480200c2c1d44551034407408540001c1c0728200900704014a80b0000c00c2541c1c9826820040307a000381d5600c04403d0391074600300c0b0303d81080f482950061961001d81401d00c1c1d040c2d00403a1140c440d41c1c11304010032101c0c9a4005d650341c41903042c0e44c05000060211220b60244130409070100441407000f21a60b50180e1503036a1031031040d038109050318006080c40303900d40e26050054a00c640d0300c030751840540c1d00e03861007010b0070707240c040c5e030340002c40f085a0b910440d400e070201014081540703401001c4411142003004040b10790304281407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 856603570 1250 856602320 856602337
    0x201061e150e3106030302010501050312070b130219080c0a0906030503030f040804080114060f060711120a14030a0f08011208071113090615240309020a0905010f0504060b 75
    0x38941daa01500707600300f000c038050b003a045503e190540200605034154000c0e41a2002502210082000001e044419011b2028014826042c540c00183c01038282d1410b02c076494409005100094048540100e034515142c20211140d4040b02111100e441d00e0a44100180f00d6180100f01d034604545680d5240d12004100c1c520000c00da10105041000c003d0071640200310182c02044004004812070714503400545403e403041f10354240e141c41d2490f00204443e0f40039400095080305201c2d4105114600304403044d0400c5a010310109000410060300142d0308561480010b15654106101c0140014001502403810000b00b50011b105051401c54450005900004190349071001450306005403a0940b81240d003042c000110010700410130740110100601ca5542400040380748400d15144520034401c40403202007481205c400c04102c407400f1070416007140b80114150302c240e004640710721901e1703000c860402d5840004101d0141c00b9030720100548812601030200616160050059005040a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 856604820 1250 856603570 856603609
    0x17061011031804050604060b07020f0604090603030504211e051606021b040c090e1024020118030503010306051806011203180506190201061e150e 64
    0x1186011500031a441012404660100e9541c0c0880701109204140b68068950103542040c012401a00d420300504054600c01640b039814a58941c01300300b403220614164580245c0d04210102d104170440c001e220246020b80c4030169030300d1504844082940c03052400c9012180c0c909100e400180701e10000801e01c2c202c0c87c0058200302072a082450500c0c0000025960780384031201c00085a64001c25410a81c2800021503840c1d03c0042c030030700098a070245e0140e000503070211418000a088040c4060708a440198440c100c540c03103d2460104404144500d81c08041d1280c8005610340d0900076008628418038007101044000d9030003401902040c003000b00320507212400079541d03410f940b500d6985090541c040b6201075a40b03214401d42010300c106c3c16400902c1e0038411502c41d0a04072181000c480000c1d140c02d1a0101c0303009d00c03000b520b00039031306c200843d503c81074002012030489680b030381e0380d9400201c1d084000341f4115549424091351a9600148603c009060041d580c40c1c580e8400c00950010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 856606070 1250 856604820 856604839
    0x120504050d121b0f0809060411010c050712050115090e07060f02031317010c020c1003020a09030506040c170606030d0e0312040f0e010509040525090203130c061706 72
    0xb2081c101030001c1c10b111907581504201c8004001c0d0340303d80440c9a50303c03680c88840c8251144060741d40c5906040314050b00e0303d00d058010140f00c3d40b10340c0c2058003250213481a40c54045c1c4410b02031902e144540c4c0b0a840c50b030345441071850b040d404101c02e00300905207039004200c204010284203484003130b24410042400141e42201005500038400c441440ca2203210350358034551510b102041c01030400758590785c19844c080943d620310b400061003070540c83e401050001c0c04490300f28202c0195018010040c100702c100500000000e0080000d00d0040d44205021743d0001d08081c064004401b002200410540c050021300445072000701c1d6280d1042c41d07610f484c6000203d400c01007460000c000c01000c001c00710020740000c00030a1200c0d0001078851000034450503980e50020880407220682d170103040358020300c03d00d2100202c03454215490b85080c8a210414a50300d055000c22a00110b0b558142d08042d440d0b20b004100c1d4900790900030b0030441c20110141a130b491202140c5a2009000702d01079100b10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 856607320 1250 856606070 856606097
    0x80604020c030304050a060b0d05060609040807151e0b0108071d1302121005030712060609020304050a17031e19050c070b090307080a0516170a120504050d 68
    0x160112010105200c00700c83d900e050614220f550361021a400b5119503240800042d00c5251056066095680040c014825610399408011654030b002e030040b2400c0c2c3e010496800083e009201003c80301c01419400281201d04030170001004040030000904507140001042c1140c0e0403210440e00704d402403410f500310035420301e2003844ca41c80e03008549510501400044c4518156500181268030901d03070f80110640f100010700340780c00824010b03503078150400603092012000c0c1110710000c3c180030f60000b288542e0349078000400c036031043d14151004e412503581203041c40840c1481042c0d11140d0351009145140c25088105e0b48002c44100f000344c0000d560100d09803840e07180640405401c0c00d00304105504061800c2e40003036100110458480300704000103514100040700396510160008080e92074216a800221901d601250b40b103030396918000405c1002c80d490410094450403e0b514103a0f03644d5805202078144500c00c0408849141000100700c00a6004101c0556540c11401c2c0107038080c086 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 856608570 1250 856607320 856607329
    0x40516020706030603080d090201171906080c0d0b071817011401240302040305010c050c16031709120d09080c030a23070e04060606080a02070209040b0705040305030c0c030f0712030806 81
    0xa0035002140305c100c0380c0a010352101d0348500c91404503038a8208100d802e40cec40c0c1c42c0760b440da110240c0180c1c1c03060281c40b0500100740c400c1c04072548454a45003000601380319410001117100a500903044c044050446101d50701c0c8248600c11002800c6010800e4561600c01009404c070160040d56048104000000740c8160180c2c0584000d50750280081c80141c2c89210024800c1d006101c0d0b8000f60301ca904000c280420914010b002920f0700091815441420400410302c2640010300d8a5003105120304540d405110500050b9010821a9a4a180e0030b01e44001c0b1480e140710508170380d10030340205da4450700041b503100d1682d55000c030101001ca55030714a0303c8207a0901021354000003100030450700308001c1100e503034440c0c0b0564109407a081040c4e101d02c18401d00300d004034840290130041c1c40340414003080042c1310003940a6034511703006103400e0b2039548250070740d0040749518800750300c010319000d89803906010204020700d0243c01040510b290500f0060766211040c405028084140f01052840d200c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 856609820 1250 856608570 856608587
    0x2090c220b090a0e01080c0d230a050d0f05120901061509030213020301030b040f05010e01020a180812030c0d020f040303020d02100203090706081302040516020706030603080d090201 80
    0x6402a4040c00315940314a1440d45501860b8a68850b0070b08020100d082e400e98a0b845043e01d0800d030041a40c14500750034403940301011002601d03002d480d481208102c00c0300481c4031900c07801e807d002e0220a210703403034550300e0154821a01030038095000398955125602405030303469001c00b00c3c0c00c0c2c600354a880004900410f896004041c040d241914910925508042c01c4804c407442a100e40041c200301c042d08030f080f0b020a000080c01c0039480008100401ca07100142000c541c022030000642c0141c0003000e901b2a40a011404040751642820514181060342c00c20020b09001003e41440c0c0880c10021617188002000321026040214040c6111010f41e810350340e000396084031042d901e94980c28084c1d9980d65a404560051050810244a050780340c0252401a01444004c240003810444140c4014000030004180f00c24800ca042002d80d03610f014882c020444007044542200740e04100a090181c15006070040c5800c0c810104002107900c0200d41003190130100c0041c0381501307840122100710 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 856611070 1250 856609820 856609867
    0xa03151505070309150f0e01021f0603150507050f030a1503240e1902040b060403060504120804020604030204110c0a0b1602010b03030a030507141602040506040902090c 74
    0x180c080e20604060381d005001000380390b010f5200e07500210307034076100261204209541e04e40091000006030324040d0040012109803032050040d01e40002e502c2c10354006106159104101c00b80d01c070441041071003105501c1c50f1000036650400e000310328010102a2040c403541010007000040040010107083e9581d0103070500000341d4000b1078105999040422640340400c44501d0b0203c01c0c5280500c2c140054843c429041440f40094102c0c5104c00020040003080f104041c0e0300242c40d01c01a80d06c40d59020b0051015601c510310010b054109410700c0444041046148800c0c442d0035804d0001680c0d4000558045030350454020035001c200b15261503550041c3c0c07011611030320454000404004013591814418108030b1a1503207584440a800c078280d480e2024040e0700364200b08501c038a2180b00760007142d031001041c2031002e000081029072880a80c80100c40503501d080c030580c214210f24040c0100c58002d4400c4030207000d8554107030000303029200e0180032110324144c00589006008045000c00c900302 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 856612320 1250 856611070 856611089
    0x90726071406130b1305040903020703030809120316080c0301120b0402060702121516050d0f020c0706090302100822031803030c02101e050f16050a020a090b060a0315 73
    0x3550741c0344c0d404181c2c5c203c0031001071685084c02c0046840e0415200790102680c040d0300420085155850981c0c80030301c080c14442990017401d0061110071156001507000d10341260500d03455810030003000703040f401d01401ca00c140c07003000c0004000c8200e0014003101c609401c4004654261283d20010780702e441090f1000f50844080c1c400d00ca43c500010804051846118030b03003c2d03550381da404040080f0034240030098080b8209011481001d00a9800004208034540c001031500e00e003044c000c1c0c03414241754402c20002c2c408920500c2103003000c01075000d9030b100c00e040480d598200661040c00f00341c2201d8a844203100c04444034410b0500c203d015600e0b541c90f42c100b4151264480c1001007000c1500101030340a10034465010302124030910340c148c5032486501600807540300a1008036041c0d070015078042007001c3c0a0002d941e60841c60803042c1c5400d44a000104400030840c4180203111003242e2241100a2400209801c580c40d0340003101c124009c40e1230001400c3c050209030311500f40c010382020902 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 856613570 1250 856612320 856612357
    0x120501030807060509030309030703050c1203190b0f06070204021e0f040f0b07050c10090504050f010602210913060305031801170106020706050a020f06090726071406 73
    0x148a4103000034a03903203004510501017a40c43c1c046030b59592205403280c4420360b004000c65404284100090032604521005a50200021740142c0d039070398006803040f01c2c5041c00102d200c81c11028074410031400c003030300b510745000c2000034200003460740c02800400790040da000511b980e0f910b607200354940c20f407003894982c6030340f03803a42c190501c44d05811502a00ad070b001e039680000b2440030002410b0318541a17200004084200f419000d00c84902582d08120092052100c404607035a51140036040c4680705a99261429614000d0024942024640138040f0103000200c4a81161406000c5501d41e1005070b50030b024a1401484020042601d50700103001c80c0404640c8a09002902010300c4888500340d0301d1640b070a030012000d10007444c0a21400002d43d101700070401420303028030050250002c060040e079020542c5034090500303000d82120007101079008180103105030103c41d480c031900b80c00b00410404041c0c2e002c412b420355941c0b44d07008038200d841004043c4210355541004a440d4100400d541100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 856614820 1250 856613570 856613573
    0x302030a020d05070b01091512050327031e0c060d0b0f1504090c051c0c09090204031a1503150601030612240b10080402040c030e1c12050103 62
    0x1100d80000429800500030000d6072940144954180d8140c181c1041c4810602e03440e1902e660010900340c6e140402131000c5050000394500b580e580d0140d054003420195a444a20320300180d007120030b859a114513440e0b01ca82c140e009480020b64900b001d9034490f81104503d062005a920340405540c00992094000039508e002000ca0f80110400140903611200c40a19030010400c034a140741840c66092a8184020400700f000c5801089082c1c130709050043c83c00054141b10b0000030780c0c40842c1144580c99218070449651310004440c010a03200f0303000c41c141030959803401901c006c2041503418080503040401c0341010703c504e500100d45002021113a0f561080150005c010504650090219280080018034041001c1030004250b07030007901c40104810f0000d0013100908c0e10054201d0903a51540341c1b64654440b514403185035480c07600c0e55001ca02e4540304102c2916034100001c42090b007440ae1081c4840360002c1c00b00c4240c00b04038500d540400340b007182183d468040942440285007000c00020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 856616070 1250 856614820 856614823
    0x9140a0e0d0f030e0a0c0e09190303270b04030e040e070302010e0f0d030207060807021f0218030105070302070215120117100216060b01020a1707080c0a12110a26090a030302 76
    0xb02c03550064547c145d40e0781c0b444443e8803103210324101100541e90942100010f40b003a4406450f80540704801034111190b10320b0880070b000989000c603003040d440c01c1030009240c0c20400c801040e84e0115400d00c50220301c010010b4032205e4030700c0000d040c031202100801503595900b01d11903c0f11405445202003442a050003582e40202d4070130640480e5101c8041415548080717680a403d076181c144ea11440150000c900c8002c0d0b024921030f018010100900d681c1c1c40da000e0041500444440c0c0e00540c4a4249004010151000b0441c1c54120b02d0708214411080040784465030464988100fa0322560300d0b4036490a080861140d6002d4085100282030708100c136903a0548a10680038203802c000703440c2900010380e5a94105c0350058400004040c14141c0780c00e5160042c00824800e005850400402c001080d00d40680800115075400707018045528182e0b003c0810212141220b0080c41e1042454a5000d030032031101c10329802c2e0070000f105a24000030340d58112200341ca0042c01c14002140c3c0da0800a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 856617320 1250 856616070 856616093
    0x3200d210f08100608090f010603050f0106120b060f130513030f02011e0c090801330b030a090204020408240702070e0109020702030a0c09140a0e0d0f030e0a 69
    0x503004542040141d0075241c0c41031801070300c6440803a002400075424040c042d501c1c80030092003502c60784919080a848400c080c040c000056128500330700022118080c0307942507440c5070300b0102c1e48035208c2c01545d020600e5608081d0304100140d601c0d1512045800210342d13101030030fa0f403002d145030030041800380c12104103140681d041d000303a0b61503074511000c10049081c0d0781c81112100c0350582030202c0d121070310001e03030001d240d9805508013a034866655a580e40d094520140c082103485950030a0134500002c24142c44110703180d20188902c49a04200640d6010702029102c11055503a800847c01103484603811100036010000031180b00c1150038040c00c03030303030b410381e00c0110300340c030784040200d82c43c0750002980100740d41e00e0fa032084030a42c1c00c0110030b800030b402140d0300780e038984104a0a540130440007041304001c1d2080796000711302e1404603000030080003005029024640d10704803440d0100c01d8081401c0b40c070142c0700e00e0170166200503200d08801a22825100d03e10500400d0096010440c0441e8903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 856618570 1250 856617320 856617383
    0x132103030f02030c0706110d0906060504180305030a050c040f0b07021315170102040b0c0f0c09010302010512040c050a080d09080109030903030c031112090f0a03200d 73
    0x91081c0d0a0318580c01040c0d000660311142c841d4418012400010410f03003044070310310442c040e102d00f005482c1e440d02080c7c4002d01019151550350740c00074400f500342405241c40c1201401c1d90201c0c030902550b07004244c4d2000420040d0703d503543e540401c0d401c112141c11580242050380c0310644c559152201c0c0d048603032140004a00c1602102d500001407005ca025000151940f1844419550f107032035038040c03107207140000401c0d59540c00c10001c11540000301c085c24010030860020f10390f480300001d8262901e1150076841f8401c091003001000183e0b4000704403110740140700840b00c1ea07520340d0314140300c007030815410481d400031503800003142031800041d48000c09450342d1340348245a40d4440c005401c1760002c0308040d00140405500b480824010000820b60510038030f020b200d5943c0c120303041c07802c003a0b00e10b80f181c50800c0f00094114aa03d450075081d810640100c03070140c0380c0781c6190b40c1c80c04070201d1a101d41110610b031501e204996541e0580d10600c00750860205030880341020000d02400961001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 856619820 1250 856618570 856618577
    0xf080d050f1c0c02060a0b0a0627060f120207080d0c0e0a09050703060b0405030c151b21120a0e0c040908070605011a030606160812010311041808132103 67
    0x403220b500d94051411f20b031724054003258003c0d0030107500f21000103004024810310100ca40940c180501320004e207000801c0c1d81e80d2081d401e9206228010304e4080e01240d1020954010304c11003003c81c005404850101e44510030000d2400d003040700540d5800d00b030319a00350340042245000206040e680d000144a0943c07941e00b0801c0c0d9845082040080c0101e0042d950568040704240000e070070a0103d0a0080c40303c0b01146041211281000e25400204035000700113030440e1118001d100c2090030101015000c007042c560414206840c5a80b801c03200400a0000da40c44088126244c0c8051140c49448000500180146606414429215800070340200c0380c580c50840001401d6200c10002c19400d18039603811444c45d100c102c00c0220307c1d000200c00c00520350056150302c1c00107842800800c03200805041400b480c0d851410040e04200d03011020500407030501400c019131440c11125071040560125507640c4421a0101c0c00702c2500e00c0b0f40010a001c6c1e42d183d0b10090146c1d0b210f442d403920b82d1081d0b5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 856621070 1250 856619820 856619833
    0x110d11070519090209040605130b040c030b09192009130b061204051029010f020705040911060a05040f0605092b02060a090608010f080d050f1c0c02 65
    0x400b40324040c51815000003551510000501480442c0c0d00104800d200080000c9445501c5800142c02c030301ea202d008110041d55140750040508160240d503580601c035080070401d00e101000071402da104018104044164020300c4508038002591101a480207400800c00081820800b20041c5911982c00c031171007240045030b401d078402d5240c000c00d041164081e103001e06041001c010080c24810180c011152409510314a844408091142580741720194500c603110042c030700b0901580d514036240141c100400b0b088124109900003648100300c400c00c0c0d40015190400c0e041c03d1340149241d07100150301240014061030030340d5014011f48142c0d80f06145403a40d403030b135400e011b0b6041e114005d040b540040c03090b080c080c0c4200c2c0e0620761400b1001501840c0803681142d60024a1681c07202402d500441c4140c030303041c04990760103102540500b8903033343c0416170f140c00d20102e2659138040340d000c681000b6000412084602c1e106c810345500003410613641130081c4c071945405014118071802c8400511a0b003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 856622320 1250 856621070 856621079
    0x6030708040615260f0d080c04120f020f0a0e1305240609071106070509040f090308090f0f1203040f050712110d0f06020901091d0601020105180304050d03110d1107 72
    0x424610344c41702418000381003104101405a817140c800415012100030301f03000000300c1807400048807150501c24003508410a4092040103d4260f005130402d0084441600070702c01c00002c40343c0346030440c040c0b014400e1031001030b140140c503000302c82800c070401ea4030b0050300350500300741c00d45524040c110071a100c2e00140e5880c0c50817600544610300004941c0d0008020510003409080180036090002e040840c4da0441135483d142035a90180086000500110402c1010f007000d100300c0c1030b18030310340c1c01404a4070200c00300503550341e519039942d0042001c0000420100701904203c03910465022007030740ca50750303035940407001500c040c0d44080d0f40b0308246100e498001d00d0070391805440c0310b0b0300c00b940e10b004085549440c07000390800415641072092810002c11507082c02d40740d01c00300d41515054600d481ca0407030700090039100042c01f1010784035845503094102e040040140c5069840680b000d80c0f00240320700f01158280c011400710701d160b01864a1080761540c0c0003606590f541c0700701e421039241960384d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 856623570 1250 856622320 856622323
    0x3010806090a2409060c0c0201030606050a020a2a031208060d0201080a1109040f0b03010f09170703050f070515010806060d0314131502070b03060603070804061526 72
    0x80510040245000d410f90100d1030035019800301c100707801080001444c800035903450003140e0454aa5002003082d91240340110740c5c1c58001c5002400d0b480ca481401d04440e00c0d0007940d107455214006100050700c0040700d00c21a6401e411545000070029441022035890410f0700301408800e40503000241504001480d80c20320106011500c0d5041c2c1d5240b65583c3d0300c041c0e51000b48403106220310301e590100401c102980c1e40b4011414070180118002074020ba0b250209070071200902200320046051284040c0812880910080000f038480411b99682c151440c04039601d118120003200c10301404100d00090003c0054441820a03d400c0100d45070f0741c0b98010a40d50742070449129078020515804900042d00c104004003401120580c0c45080c4901d400720444007000c40d0b08514040c415100d101d150f12a4104039400042158540e41465800e100010400501c0024204424040c1c240041801c2001035030260040152100251100a465441d0540c1351006221521164050300d940304606110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 856624820 1250 856623570 856623583
    0xe0c3c090a03021009080607020c130c141605030708030a15051c0618051501090b010c030809100501030c090617190f060606020105011a0a0815240301080609 69
    0x810640406146a0030482a130f880c40d9000f50030094070b08400550700c03c0401c4918080d01d0701e034000d4601000000148015a204928000101c50400369503140c8a40c100c00360700052042080541d9941001c21410107803201d88800c001d001e1f1000044100910000380d020f540200e41d509414400070007a0f0b0321044104405008581e4041601d607000c40c00703603241d1444031718094821440400d102c01201d15400c11030400b0502a11503402c59007040d400c03c580e000841d4050641a4000c1102e90341c02000280307034442c2590000c0c00e00100c0b50200d86030307900410401e0441a0100300134400d80d0b84030b24262008aa20b031240d10081c0c0c1c2028030220746d006c80c2032419484c030f0002500410001c1070034841c00100400840c41070701c2d10045910203501052140c00340310302400c01500041415450111007400100e04125540035a060074000040d40542c414001500b01c1a07000514110862040000702e008000d9001b5031001d04005200641d07480d00c0c1c1d8003460407078046000740d40071030340c0b42c082c904e45601 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 856626070 1250 856624820 856624837
    0x1140712050d0f0e060901140c0f132304050601030917181c02310e01020f0a021b040608070605031905040f17040605040e0c3c 56
    0xc608046a41681c450750240200d010444800b0039440010403009003100c0082070312840c544c00074410044000003d0092400c1415804000081c520f400800411940a110040080e10078001607403a00b00b0010b19684010f403201c41c1c081ca5110006480014010010001303140c0168284400990303170358020301c56200001c1e0890300e400d1034030701607001c102c0c01c950190200c9001d441c034604035103020b5110a0088102c1505104040c403492442d801040030801c0c2c9141c06500d994622007814819142c000b11042401111401c04100004941c003102d002e40100200c50f1080003001c00d0001c4010750004481c40c90401e20004425225040701c140019141c66028921803a40110f4003040014030440095602c24905610741c3c40d284c0484840005441050302c040d107d8205044a40e01845100103201c00c04c40c840501c007910700380c581075015010b170269200c1c2c82d82c5d00c182d00002502840d440011180100180e8241c00a010b66850514446284521102c1d00089401c0144012250004210303802131 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 856627320 1250 856626070 856626083
    0x302040e030324060a0e06070501051003050c03011b030504030e091608090d0c0b0c040f260109230703020405040602120106020f0c0d030e030d0503011409040c05090c0f130302011407 80
    0x1185d01070090b204074a8000e401d540001d81001200301007007007807003800d000304203004d2848261895800e00a141c10a0400c840b440f903498111002d500620015142c84924086d09021038141c1d0b071424299004074a0950741c2e81c00450103810008072000100c8150700c00c004544a04469031034100c40e82e5542c0030400030082c04968901d0340840410021008a13134424182c9550610386901d4071070101c2c01103440c1e4014400006a411100204c0d041d0f020700c41451448003000300070b6807405480e02070081c1d134841c2d075104203c0c088002c80042030100717100c044061034024005015900f001c1c500400294010f818280d0404420000400d5107407001c80c808402c52034040040803164200002c200c103505c103800003242030107410f003445004c40e00c0034048028400160b4a0b01a00e13985081403c00e4151005001d6900c1903140d0300800c00043c0c92032074500103842c0251031050150b9603503641e0048078400e245003c00d04e01800300d528001003500302c4101d01528030030390f6011002c48c251824000076000b0900c0003004e9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 856628570 1250 856627320 856627327
    0x20f1b0d0807170c07090513030e12100207051c170c03131b080d0504030b0f15030601030b0405120f0306011101150b07060b1002060c090103060302040e03032406 71
    0x4580a0320140203150300404060514140c260041c190a0b84584d245030080c0d0072940e010031140c081841034952281542500e42041c46065400501e0600030700a0144940c000d420b1501b08550200480c2510b1315a4040456070740b0b61504110340e031840c1d90f8903147c0c00000012000c4070064442c1e030081d04400256060741c4c41580300c00c41e1440c1c2e41e0b04020549207440c04849103003404122004111000c0c00d106442c2801d106051184450424110001e01424400100170420005072005130040e8040f01e13030503004580d034446043c00c03d01d48640c0b101550745441010004824002d401010501951050b4122080d1031030181000394139008804d1803088040051000550650003410b24080c84802900000303000e4111400b1501b140200ba00a41d511903004640e21041240ca40304d42c141c1c10804661001804544401c004c0d91880b0050000035503000210b20710340c45034001e421107000707035034020418400c2d04101d5062944d00c0d0021201c0c007201804006c200c0766405540d540c0e0071b2201201400d880e28 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 856629820 1250 856628570 856628573
    0xc0b040809011701090507030f020406090b0f0409020f190c08090405090c040507091e03020f01231902011514120307050f010204030218100512010e0d020f1b0d 70
    0x10039800c941d80481c14400c40204440da10f00c102009680604609070000580e030070860401001c440c215808403011520421060290a13084982c010450341d1580c0003503654810801d540b40f10b4026070788500c52250011032809001b0a4050141c02468210060500f00c85a41d40c0d003126540b0500d1809403840004104110340e60a05401c41544014500d042384c1c0c0e910b076144007140c11a40c0441d00400083c0d5440300501c0701203605440c0c030f81c810f0306103030001c18010300315000131340d11000ba000c0c001d06000c0c091f020f005600306e038508050a081c0a10305201d07100c1c42c081000c0c241480c811042ca1006518203141c440c902e00340f62006034140d0b180302c0d0f000030070848070b4001d100d201c0314520608410740c80280300030b40000d2001c01c1200e40f01e1036210005a10346146106004600185c0c0482da190901120f08005071141c18604020480c0d0b812103030b0503407103c89183c041d401071090803000000c038014070344d40840084d0001041c00c51001c0100c21100c0100c43c4154441c0c40206500c00309038441128040b890 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 856631070 1250 856629820 856629833
    0x906180301020c060c031506031e06010c06020a02030a14340813030308180d120e03070b010509090a020102031e090a031b351606090f060c0b04 63
    0x1588548054001843c00c1020074549181500403185005080700010801c841c042da0342c031500e4075070401611014298100310144a41990003a0890041200e070b020020741543e2150614071001604400119654949104000e4581e4882c1901d24041400c40004441c0303070302e0309812074455101550b0840780b84407000a0100020921020104070241c1c0940c050004c500f07000c000b0a0b9107484030268808a500d10f1501402440c002045000d5504202c00c201144120201d1046010102c81c0740942c20401d42604680c0103080124035904c9500c4046000c9007004101600c082c1615000c403682425569903c54440e0343d0b601185000740140c0003031210032048071080d0074064494510050b118100f07600c10010442c02c6c90254426150300d0546a440b17291658107901c0390000e8415400060080052a1b060310301c040006c0750b581c1e40c1c0e03a80b1051540b40da64024030810307002500b030024080e0010b69a040003890407400c0c2c0200c00380400c03100000030385a8000c803140a8002c0c3d2101301112160780359140d20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 856632320 1250 856631070 856631107
    0x105030a0f0c0506301e0417030117061b071b03060c08150405060108060607020a0801020414011e0f14131203121406060a021f090b07050906 62
    0x31600d058010b4408210fa81d5602d01030003440300c0109202d050451031145a0a0501d2626403603c043c0600c042444510b008440700011241d0610540d88101d03262450706851180132841201240c00010002013801c0780391008206000c88410b0442d982c50b00d450220581601d014a034280d00d6030b000b085550f0008000615100d040b0070b0041d00581c1259803500c07100c0c244c0d000c640095002401c180704120968902070f101c441c6404003510b0030080e41c40d1a50000e408440c0203000c1034416100880c407201113580340011200504100d1000f507440359070750741482400f14421000c040c0800c41d901d20415050b10401701d880d40e414460356a1b00c1155110050a8940410024000c00122401c02001a00c1b40c2100030480c010424022605294515801c004007200125681811007034149507004032640d2075502074680044080703542640d201007010050b4541040d0030180510341d507000365030315414415030b40900102405020095400d03513486004a60b90721a5002c40f641c03000d018004480b00a0f80c40040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 856633570 1250 856632320 856632323
    0x50315161d060a02060609180a02090c160320030f160201020a1a070305090d020c0f011b0b181618060513061401090e0a0c020a080a0809150105030a0f 66
    0x341c40050555a001c0b6a02e035010303a0799900903070f1240c0244030540c00c0540460b036004002089941901106031050343e01c460441c500039101d0710240c2c0102d0700c1c0910072801c07921759880c00310501980305070300c1c58060400003801c6c01c2e0188200c2030901c0d45010b07140c00300485612111100e1043c2c58800c0483e40b00c0030700f5002c04001c0e03045100b410807940014840c0c01144a400c10109001d62141c509980020250390300201140c0250f04600c0440408640010b0000500101228600070b041c607054012500b400d880b808a03014180094540014450707404141e9000b0080a618500c07001c80709482d4541d50883d01c01c0c0850b0307041d0111000c001140d2091000c2c3c0c5000c8494402182c0d032699240010f061f00200545044001da07101e13000c0000f640c543c40308251102080c00c0c207012040c50502c000c114108014a0380f00300715190f00d40490014070922003484a6070740004403584940d101c4100928814003294400c10300d02c00c480b0120b1504841400c00781c101c9400500921161100350742d0f419041201440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 856634820 1250 856633570 856633607
    0x307081905040f0e1603060b0702011d040204090e01050c07020109171e0d120e0a03030f0b0d05030c0d2f0106210204060e0705220902031005031516 65
    0x401c0c944094201c010003030091300020b405605180d86100c2d503450803822034605251611908000500e031410569a003540c09080c0b00103004250390301d18210480d070b0280d00307600920000e000300380003417280d01010103000070b90000c00003035481d148518280c0c498500c000c5e000c58003010301041a00030b07401401003d00030b080155000038076546640302900c0c00340201406280c00c60240300240c50f60100581d40c0300b80c10030009000b580085940540c40300c540f180080c0400d40c80380400501c8180c103070010780c91294090403507070f02c101103801d089480750003480c0517011074001c01c0894041240309607486241a108452a100420421480d0b18101c070005d088041c4c0035501c4070700028010307410005d08000f40480c0c15009104205c1441000119190303030b0000390403101c148040c4900300394000c09031105440f082c001c00583d48100d400102e4101a69408000521300001c100301204800303170883c1080710010303000c56800c005107002084120782d0445240d03209000e90702b0a20310700d40c41110900d151460661 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 856636070 1250 856634820 856634827
    0x909062101020406030c1b0b0c090a080607052104020f0105180a0e0601090e09030703051612120f0c27050a290c03090d08120f0601020f0307081905 65
    0x80d40341c01e82e0402d0740706501080d074540001003150b40014140c5007403940c50910050324140e569920500d200040c10408103040c2c0031801000035104c00d503804010300040000c035401e602d89908000c2081c1d03c5241d8405801851312641128001080080341c001d030b500070b00c000c142c100c11100441e943d400819060342c0c50404a0704482498484146600141001c030015281618001002500700075507680a80c0316888000704010f00d0304400700582d03190981c5450440e64403140c80a40030054403410788054003c442c18005000e5464100c64020f0441e022420184407044814000303404881341c200101d004131360342a240d000c06c1600703004282091141007404400b01521500070954115140d007241262060049200d1455070030203060041e64205550850301d05070368860308507120300500e044140280314590600082041007420790b40340c1a0100c0318400c01d1700c0c0020444110541c1585c04501500400c0031026a01a0100c1140c400f6038011140740e00c0e040340d00085400005003511107100708607052 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 856637320 1250 856636070 856636129
    0xc1e0302130b03040b01060f110a1506170307061a0112050a0f1d0c040506010c0813150c210c020f1f0503041a0709030602180604080d020105010902090906 68
    0x48040c5001d030b40101c1c1c40c01d05c55810658050b100300c04540b007850500c164081d0040c0b1810f800101101500e9104000159a07003406c00613a0242455402c80c0d10f403000d0640654100380303c00800761031882d0286009204856a8400c04000b0040400c103a40c00511516100340e0703014115001a604410750040c00600c0104402e200c0040707902c0403403049040d4400d4246178280b00070400c4111141d8004840811050420000107058500003a00051400e08007160000706248031000b813500a00150038201d00c4e802610800070103910300108200d03000841c46c40d80e852121480880130191040c031340ca0700c107100d00c8070340c0070002014525400541e00541d4048040c042c40013003000c443c4003100c991141502d03810300f490032030039840312003600038040c048000c100070340c0b00d92041016007280c0d0016130040e500c01c00008a900c10840865859402c09030004001442082c0001d080701205401e41c0200705c01d1740c0300d014110580c450030742619488407030980481c0103480c0c9620361407200c0c4181ca00b65030b1b075038010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 856638570 1250 856637320 856637339
    0x270c050303180a050301020c1513050a0f150b01020c010c050a082a010e0c01110a05060903130509090c0f06070b010909210207030b090f0604050609010c1e030213 71
    0x20301c0d0140004241c2c600440b8280c205001c0c20030240c5021030007541482006101195600c1001d15100641c0305c051002c108001c0000340c603a540c494000054a44a000908101031081c24214088460180404800c1043c041c280315400102c0b50583c007070007000440d48011166a2800341c02038880740902190740700003c2003800281809103648402d00120b20004090301c8065410b00d814200c035904125030760700a1800071800c601202e400b42001c0511902c444515842c04a1400e030041c040d101e40c40501c0703410f1800201501d4000d801201250310700c0d88800c244809040300391490920741c4c0c040404c40f03510f446c00d0319599040300c00c054012800c107405500c1f4025288401c5c3d0101e0403481e9248002000c1c0014081c042088030381983c0140415050303a1380003541c13501d8510000e001c8807242c10225201e201709221a50300e010200d403c5940324107160400e20341390300d0b040d1501e05480d80781004880089000301c0c4807908108501640341d141800955054020f5441242c8003e4840c041c40703c085056080c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 856639820 1250 856638570 856638577
    0x12140f09240c0d020d1a0d03080c1317010b0f120c0d240209090f0103020f040905010b130510080a080a0e040f060612060b0310090902060708072004270c050303 70
    0x2c1001c01003148080707400071862007020008140d00406014101c58042a002000e07541c0220448100c5a9118048008425401c41c071350081d2540400032070400034900d0f41500401940ed008590002d06a0110010012500c444040300c850980080c6688945483d01c10b0035400054000c0141038801a000c2c00da150b030044500c81c004203404d5000c0740b4072010341803600d4207541c49a0366200d800059415600040c000c00c009203603080c412500c0390201c200300542034001c42d003000005450907445100074400c0f14007816085550600240300003800050150300003425007440e507081031500385080c810050484280030869155500107032a803c040301d2a030709600c900030040c4041d66800b6480c0f5036141d4031100769089a1f01c003041d502414404e21011041d482111011185e940c3c4000508141500c0070950b680940d0402910011021451034284040b980c810070703981700e4100912503241c0320801004115542280c0300070310780120141800d1800c034020f8480d2141400fa00c0480c0d81a50f540000a00d903a2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 856641070 1250 856639820 856639837
    0x1d130c03030c060e0c0105090d0f121d04050105010f08040c120b04061401030c092c030a020601090c09030609030e1005090102010b0103090b040f0312140f09240c0d02 73
    0xb10003a820600340491841900400504c0b88040c207a030002c0400005c005d80284805544600c0e00b00c0a038400708212200c80e0107000da807100c0002c019401049025100c00f03401c509688440c8240709600c0c0c640d15051003a40d058910507110b041d007542981e41c0468990703000a20440700c983c0c4990000c282c00c0b17420b07001000a00e119660b40d0f2030320301d040d00d85a41a40c1212003565002444c1c2c00050001a00204580080e503501e0040003608000101c0c0070030808880c54100160306440c1c0f440155400d00100c010320180d60300e50200d440c00d9a880d0390160441d041c1c0f040c0507000900c0e40070180001403085d0000418a070080c545540150300200000b0510b48000c0e8000b400315000060000c2207503028001c8050000782401d0410015005481e0100c2c0003000900089c500000b808074401013600031101d0503050200b06108010413004a480e2007900360081e28801e210291106c000b48132503d00041c00000545149c0d1080b4460001c8900d101c1846009000186101003d100c00e4800d188075101604001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 856642320 1250 856641070 856641077
    0x403050309040f0c0207050603070e090103050a1707210e060c07050f010926010204260105130f1104020c0109050726070b0f070602042d1d130c0303 65
    0x600c0c00074200011100c80350000d1a020f400c007148520026004240013049500549516a495403a04c03c210788030958070104d144d1040c600c00010042c8000015004a00c034403a101110320b07180c0a020200e010302402c000108040305403080040c0c91000d6000700000f050a5082c032011154401000074016041494060101c0d400800d00704014503101140c0400c1c1542030078091340c07281c100050204c44052100e02c80380a200b52041d05600c8100c254100c1c0c00412201d408182401c00da91820a20440d2000200301c007582040042104519020b40c880302c07080d031209101059034202e544918003088007001441e403140c0d080c840915483d4080c0102014940716001410f861410a000c0c021080f0701c503004040320079030002c0551640c07100010000300b17503180c044040d83c80d005580101401889403040042c0918004034000404021003c480d203018108140c0c112820f01410021800c0e00c3c0303480c032500003100c0b801c403507680480004c03c441d9900400030310880032680501d529500402c41e807550045000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 856643570 1250 856642320 856642327
    0xa03080c010507050307020d0e0f060a0809250306050702010f0614010809010c17090a0606030305030a050a110f07140706020f0d020106030b270d030b040b04110403110d05010204030503 81
    0x3082400c2c816964080018100070f070550030007000007550341d8410940441408407140c01c0414070360311107101d4200b004004155680c0c0b92a0700000400c0c040042d122200c00d0320401401545000051454182061000108210691540e210540030f4040134111800359561220703074951010a40c028503020f010200704204000c131000c8001000c85038004e001419603490a070fa41d5003010390240c0c440024540102c5900e810741c4485a40d64100410940700400240ca080d1001040540180c0610701c560001c000800044e55801048c5040e1009952660f010100800000650003110300c00f0b44a124040e1085003d4000601042403400c402c0da0040e1015170b101c0b52400c1120303001005000c0701d0302040d100900c102e600e10750b101158500301801c80541800d01d21400307960801c0c0c0503901e1090045507021511242c1e094007000d0f00411060141c180180d04090840f40c2d582414000e105002c01005289843c140c607544880303408500b40560294000c0c420000d0401180d824000f41000e140602c2c040e580e0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 856644820 1250 856643570 856643587
    0x9060703231f0b091e0a08060f0709060806030d11030f04030f06050705130522090b010f0b0715020a05070b0f15090103211b051006080f19020f0a0308 66
    0x32890b0b240d501c881d42c0200c040200103000e03160750a103020f040340e814041c0c00701d0112070400241c2c1d032807040e00f0004652003103904100501f0706081c0c48902174201602ea6904103920b544c01101d8400c5c085038850740507800080c0e0020854440c500c0d000e82e180c2c1040075a4107018461000501590155000340d850a40b00c6e0090743c14080b4502c150b5801ca0b03502d0402134a0420020304000020016104a910403040c9911003911909000c1e90000072401403a02040a040d062030614803440d001e004481c403141c001c01c00411100c1000040782c0d0307460380122a64944008807181c1d54007943c00440c09008000e1700b8440382c000541040220741c06214915034180c02490101d001c100011968050703107200b500907000401c0803800080f0320294800100100c008a0b0031915015503100c42e2890b00c04070070322000040e05044c007002241185424221030f6041c400f140d0754001d441c0d940e441031016a81c00c0d1f041515416a6070708500e5800d40302c98030250030301005002c00400222032904541c800e0b60300b00350001c2d0701e20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 856646070 1250 856644820 856644871
    0x20f090a0e0a0b092e05060a050405180f0f030d050417030108070806060102031207081e2a03060f1207091506020c010c030905041d01020708210906070323 68
    0x29040740301c805660a800d4104020105c80c0041c4070003442c80a41d20303c04144103480d03c0f40101d0240001500a1100b404e00801c0500b4032241440280c03036038082c3c0d2951805103100400c07a000c1c140c10900045040c4080c1c80b40c034000030100a082290750100784038454654404c220087c0d4002c001c108041c002d00c0c0d1510580f103040400081c9031074115002000002d0440100f000c086404c4181441c0a20ad02d6403203107008050008002d42c042c421a1410080080f05500812469600c000400e8094024482506110042d0205070341c107a6000c0d000142041381424460410011100e00e842241d000303079a10424070703003220202c680c0d00d05e400844400c00d010240e0100643c03518144286012220071125032801840d0801600401d0710440d10307485454940c0b501100c090001c1e44922008564900c030f545010080d40c2e00101010308010540320244046801a2a92a100b4030102c0c001d018980da03810030840091160381c2d00100401f04d00b104a600040003211454450000b5070000341c016480703040c952 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 856647320 1250 856646070 856646083
    0x6010b030408180112141b191b0b010914090a1502090102030d0f090201170f270118022409040e011b0525020f090a0e0a0b09 55
    0x100400081001804000b07801401203440c03000d00406806010f90398100101c8030401910700c9145c42c28103054004403d410140c10781405000a40511151a89601c95600c1c45000d520708041400c2c40004078070b40c03501e002d106100c507001c40118104c1c0c05410700d507484082d6500e080c2c000320807260b43c0d501c501c1080d1490034a096000941c2d1001480303443c440741c0d29080544440740c12040103d8022a00c5c0c04039900810940e8120344128005114940c2e441c42c28034000c2c800141d051340080c04c040016000c1000300c005a500808441c410295543c1d54583c0780e28a0071440307104110000c43c855110b09500340203210380011108100c40946a0009900400020b03117050a1070b8100594544000120181503038101d0768421029a004160001624409801070152005854000203e41c00c41404941d1140040c02c5108440b1684501c00d040440c17212444a117164009400443c0e101a021152074999002680054405070100d03d51254501d030300d05103401d500b0200c03011032000d8180111058184800b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 856648570 1250 856647320 856647329
    0x1305040e0d031d0708160504060503150c161101030509010c09032a060f0f0801060906051804020c030a09050d050604080703120207080a0813020f131b08090601 70
    0x18030681060810440d01c5440054900c000d0580ea400aa144080b441d10711082200e4003000f9100c004c0c2d42c40300d00300d8540300c405045281e0070312007500c0861240341074459070083c0c0d180500103119129210042948600300a8201224a14180302001a00c2c5101c80d80240b0140b08580c210b031801c04181c0090103942c005801c0c0300351641040780d854413650b880490501141d402c10100e2001003040328a4030305400d404481b402909100d81d03004901140c100c10500000c01c0304d0ba81d820003502c000541110304040c02e015400000b40740460070001036100d540600181c12206000c144600e00b1400090100d80c0991880803080d0400b28900344201d8110403010f0091030244c4803c00c0d49411030b0348250b00e50740001c1006210b000c002c0344100900d40f1400b60845204540742c42195501d105003808500c81d000070f00c22200040e405000654943c13060f0152031100c0e41c0c054043c02000c0c0c01d51040040e4520000901e14540c6d944241e410800d1210583c1d14200d00c2c01501e0380c05503410054203d03420240160030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 856649820 1250 856648570 856648579
    0x240a021f1b0c0506280f090215040e0f0c0903010c0918091106030705070b070804061b080a0e0102070f06050406050601020303150118080f0f0f12160f0b04081305 71
    0x40c0b08021840c0402c0c400d900142000311070948290b014408103101e1050100740a14a2401c11101060b10a5611200c4071900890b41c2c403035015680d00c48000548200d00481d8054440d00700800c4c0d000c00c060060940103903e08010908000b4410046070840d020030030760300c000400d08841001307402c6428480700710b400498807041c440c10f402902d0310120040003401d4031b40070310400800160501d126101782c0780d03d1540b0100010b068203088100601d542000e403811b603a0b0741e251030381d4180511120705601c2d542c104c0ea51140b0100b5075030900d6100051122042040041d5000c001e07480000d40000518911244070b91400250380c1000e081810807114020080781c1135510800c20302c101551000d201030ae2500007403903d000152219801000b025883da07100141c103100b4499110490707400402c46504c600745030b8044410b0122140d51a42e40d075281d20665400c404410041c010902540c04124107280340160034202e014282581c907030122031030480701520749080c003140561447d041d40c0d1200004080888 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 856651070 1250 856649820 856649837
    0x4080c0109050d0801151b0219080c010e09070804030c03020304080f030c0f01050103080d090501150311041a0105040612020f0a02150a11030a0f060302090a1406240a021f1b 76
    0x108082c1508005107020100c031482c41396400701b156295031484e9081701c901c2710043c828640e1241c680c1e40e00ca8280100e14040707007001a0241407800c2c178296072840380c1003581d01c8680035280d0b0785080e901c00d01e00c1d000a40840c00200000300d681c0c1d00400c0003200c1010064000d40d43d40440350762981c00d150303050703191031040c1c2d06040c0100f010800b90f00039181100c41c40304001500030110314100340102a610320707070490f07a46021300c00400c0c002e0725000f031520141c0a5030240810a402c5441c0503214103030000c100d000c80e10600040c040c00341f141c5400704164203d411b00500e002910301c007003c00c5420918004005038032800103091142081840150880000e03807040c0a840d0260007803450b6400002c0c03495200c07681c0c81d0720b0110101d00740d40008c2d0086030090454101d034141401071902602240302c518428082020104409042c0f0346481002683d0b201200101d0004000007908a9840380410300114400c0000d0000340c00400c03c1144048c0702b5050380010161b41110485810b00c1c0b40010840074005010b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 856652320 1250 856651070 856651109
    0x1215020a05032202370305060a020c0c030115031505070f030c210b0f090c030a0c11030d06090c0516020105090406090509060708130c05010804080c0109050d0801 71
    0x202603e40210614040036149800100c02c0300000c0e0b15528080c2d8880c0300e02120000c4c3d900d242c40e54102151410494507403022030079100902d00c0889110041203a88598005408140c195019000c15105002902e50305658000001c1c20348001c00079203091040620700800410403800148940104c411009000c0c0d890f2207040500800500d4444ca010316449024800c0e00c1c03071240480702800892016040c50544003036400b10700030500c04810b1030240007034803407945507032a10300d5611b44505e22281b000c07485c5030b03250560303280503007130903802d010a022100c0c2900c0c50204091004d401001c0c5c42260001e1090b103041c80750020b0f18604a41e020178000200141c3c0768000c030303100f80c508000e40c0a081c000c0ea10321030100881d000344000d40c00000c0041c904404d000303500c000400d6003400b03006c2c10703070f151032603034664032460f060612040348004c0003a209103404011950107492100c0d4450b0258000900b00034440803024252052228122195003091103650300550300b03d13401902415102c1c4a800c01342414 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 856653570 1250 856652320 856652327
    0x120a0818090108030d140405061504091a0a0c02030403051f0e0307050105060f0a0303050d1e1814150f040f0b15101e120b1503150906090103030e1203041215020a 71
    0x1821812b0101c1681360440c089442e903030031807140b0741d40c4186900c030141c07008075904c0b0003150191083d546103810a02040141c92000003601c1c2660340000140100900507650504000031104980c031110b03032101003e055180d800e101411010340110000710303081c40c1041c10040580d6118804c544600c458603420b1011903440401ea50241a41900004540e01503101d40149221440906d20049081421201480c159003588800f038912440422207801c0c800d4102545806208103c61541c91001c000541c1100d10040c00341c1d0007a00400c080c50501c51240c0b10408c410070120740d00d100c002c01503610318441d400e02c1501c4245132001031400d44207044500324150f83c61150401064200210060941c1c5802510b43c0850701e01303003000344901c4e0349080628044601d50403c48002806072000482080030741003081000d0f1044200400c00d0845070b095035800c2d07902024004046030094a0400a00640002000140090038210741024000c40d0302d4904803420b1b8250b21040c50809006002c0054526003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 856654676 1106 856653570 856653583
    0x50a052e02090904080f1c020705210307030905280b0703020304020a06050d02070221010c1704030e010203070c061706120a0818090108030d140405 65
    0x55000c00c103040b8050528401e4001489100150000314410002c10440e0515541c3c942000002e590a20104c1290800d4078901580003c4403004d1120400030540440f00b42c40d082074610b000ca40c0d0030589408090b0400d414540c86101d04400c120313051111220310b0351f440340004e0116007203001d030440884c0400c009560000c01c1c0740200c2c0b82c0c03911034000c49100755000b038400d04003903240403012201a40403021a483d00c80d42804900f00594814401410003c01c0501280d01a035803100c2003402c480000c205281400251a6540222200241410380c01a01030805521420701c1c1c50050f0308610892500428007003011002003140c58101c3c2c0c6043c5048c80d0905075407910790711001840310068000491071041c0d480b04288500040c0c00b031000301459481404074401c00c003003034030109111880a81040303000381c201003081074070030b4807512411101d01d054918680b6242815112140c4610303 = true := by decide +kernel

theorem cover : BRFrame.Cov 856474820 856654676 := by
  have h0 := BRFrame.cov_init 856474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 856474820 ≤ n) (h2 : n < 856654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
