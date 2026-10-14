-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2869
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:59:01.010842+00:00
-- url     : https://prove2.me/submissions/dbd5d810-5180-47a7-b4ec-09fba88bd39d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 515827338 ≤ n < 516007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 515828588 1250 515827338 515827363
    0x803040506031b0d1a01030605040e10090503130f031403040b0f16210e030d1b060209191e08060711120d060312020705182526040203 59
    0x3d82542d0018982c1c2d0822942c502e03a2810301008001c07120350340c81c0600700c4401003d1b400f280c0b500b80009814101800341541c1d0f03003980b03009802c00e2105003030044028007058070169014442407040b004403201c010071400143c2080c820034030000303266144c00f030b0b005510b09031140c1103900140010050101510255200c541c04401d1054603031850300c8c00803042518685018264000446501e00d044a82280303038003800e401c9aa907500039410070018140e80d070b24242c4c0c1440c0061002001403012008031520b0504c458032071180545051800030004501c41000e030132040c9038005250003005481c20000910071542c24002c2c0d8405000d02d009201902c3c4c80008200e03a05000080c1812034000e8414403252a0300001c24080c01d84030b50004203180d004115901049507030b40901d420403000d880c00000c66108551000b4004401d42c0f40c004015003400e640941100b0080446500e400c001c4c01b5030f40e5601c5a017030990341d1014060a043c158a1080403840f0000500b849020790512015031404a04403a4105 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 515829838 1250 515828588 515828611
    0x209030c0d0809040501180f11090f0d0605040c151e080c12091c090f05010302070212060f0702062a0c0708030a02010b0108060f0603040f080c0109110a080304050603 73
    0x10040c103182c41c09220741c03400181e1291a2400119032282640c0031445031004965003008010070421301902101c640300d485068a85d428801c0c1000c528000d803c4040d00c0e1707006002c41c2c1c40041e00d40c2c1c0c1c5205455003614101c40001200009020200d400100d07882000054074040c01c071045e0090104914550142110042010b05030006441d1437071001100c07540400c0e0305c800e02591400190190b240c0c05030501c03801c0b1410554090101651040c5031172320946078661380c280692460480158001e500402c01249c02107921420450a03190500c00180304403c40a9411f0581c0340c207070b900901300040203001003007242c1404440980710340040e0084040c08902407000d50ba40900200c010314141d20b6a0010740c46200016240c0c0c4103513419000010504400e8980301e00d280c450404118580302c0d0ac646ca42d410100a100082c00300c2c030301b4803280c03141e9809007100340d16000c20420041d00303580007581c0555203040320400d00106800c003c074440c40100050030103107089c0350410300007030407620000d00f02c021405d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 515831088 1250 515829838 515829859
    0x1b060905010b13202104030e0928020313240905100c080f0c07110a0f0515030103120513050a060f020607090b22050d081c0209030c 58
    0x44250700010007440010303c03800c08030151449001c06810880c0251080d0f00500f41004d18026082090710400c400805685c040d00c601d04062105015006006070b040014608d6155956191442514090072210304551200e10840c200d030518800d05080021049104204101c00b410410003c205000c1e4014518400e856070042840c40904c140000e4024071440c018500c1c040005c0050400c075000d401810a02000900c82c10544000100312103603501860b0140019104511090013024030511800f144000c000c01c6c0d00c0842c02c01c06a940004000c400c000000f4090761070819004000328482240301da18642c155a07d4402c00f034501e00c0c48405129010500c00401d142c4224000054603001e042020391554881d801070010320300c00a500d015006050200ea40d1910410000065070361012095103030007000540e603021046515a03403806548c260501044960300c10b42507000841c005c00c5c84a0310703211607a10880d94a044025541d0210f8410031180044d6100800c58100c1c0c084102c5261900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 515832338 1250 515831088 515831093
    0x8060a090c0503070b0301051207031101080415050f0601030e010905030901080402060f070510060e07090b0c01020c120d050705030106170a140403020d030b1c060209060405060703110d1b0609 84
    0x141c8550b500141d6043c050f1103c04905d680c1c200b030145040b04c4045030510790425440c44441d81700e191030301000c3c009a540d2044070046500030f8610603001481000100c0c0303c0100301c00302104a940a80725486010704940920441c0d6900d0b0103001c299018030002002008065541c0303035528810380015a040c098000000340c195034450050b904180c4503c010719648144a1410302d46072041b000ca01103103a4582034000ca1614549945240b10740c403d506c03005000c0d81410f0300e040554100c0c00d000710b101d640822075405414418408080c608040d81281600d464440e200d0400307840004284000304607040c0010010141c1c40510405002071132100404180c40d850603c00241c051a02da07440c3e2007590405210806070300040c00c0e118103103569010485446000c080015002400c12a20603040d441d2041c2d1001c1b4010358020a8402c00082019240c50364880208580390021441038001c074200c2059800e41c40381c14011045180403074030340211803088403070300c0c500e612440c85405071902d0f0742c40254104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 515833588 1250 515832338 515832353
    0x40509070516081c020a050a03270b040b070e0a2706031406010e010b1b011805030c0d0c0305071b0e1611010506010c12260a1508060a09 60
    0x41201600c2c842c00c80e402c41c1040005940a02080c41540c94600c03c640402c02c0c91741300303031880ba00032556030510b48220700720110050444a01204c4181d0401da1584a04071581504514818481c1c00c0181145c91305090091414100500720414414500c90014059640c158440d09880c03900301441c0307105090311802d0741304030019540c0e01c42c844c0c54108003000340850720891410b80441141140c0c0305a0720340c04d17203140b2111b00f0f1240300e10300001402040d182601240d900b500c0c00e100c05000286464041103640124012a0300540b000d40001030300007034110050083e8105146d4500f4030021078207107a42d00800c0340c440c01138054115452100c0100168218218104c020007815441c1261800c281c420a41040c070340c840c801c00402d04580618160b000103000304d5100303400507100c7c201d40c610f0a4554041c8041c039a034407a010412500c0301c101c0d540f00c6803000f510bc1c401001c00004202c0c90310307091140840b00c241a03417035030300000740d54100034843c000124981d218400c1d600201d03034640d03103180101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 515834838 1250 515833588 515833597
    0x60907050111150c21070306080c01170c1b06040317070e01050904050a0e0a03090501030e07140907021c030204030317060310020a0c05071805011a04050f120a030c0201080109110405090705 83
    0x4171030030104000d001c01c4e10b41c980c02100503182500250303841c0c0d505100040d905241a1040d21900f00e00c09000651082c9000d009003c58419103180030300307404034903008942031100032502200421003a580c82540441c1d07000038140c0c0940c0c503041080503141000f0000e0b240d4043d03807018a220350b44500004103800358507009215000d484104603070745080c2c540f901601c1c03d8424090580000c0c6050610426510001400c000702c030f400c08014042c182c004001e02290940c010400c00540c402c2c890a020710050044508a810a181c4d50042c1c860b0309600e80100640200b5048401d080001410300459a5020809422a007455400160789803c11081034401c0c51801401426a0107400000038080040760385c041d11800001e40d040010340e88541a506000720904008911030106200900c03950038031840828504000410b5280e000001d1541c481ca861410001140014054415001156000600f01c3d0141101c60414002d10b07800c080c03c03894500461044502c00c1180304085409a0700680489 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 515836088 1250 515834838 515834887
    0x101d1b0313050d110d090612020d090b040b090106060f1b0c050a030317010609031203050702011104090b041d0a0321021b190206070320060907050111150c 68
    0x640c904400e45a0180c607250321421500d44c60f0180300ca50440c500d01c905201002d541701d54a60000e05190000c0d030720001d401c018040780b10316a82d0303050384000c1a00d145c0e078203116503c40c0c0500b40fa01c1c40c2070300300d09082d500345030b010f0003d011440c00c0d42072009400c4141a12605028400740071320301694240300b40801d1142c1e110a0300006041000300601d94080d002009000e04030880101d0359a07680700403613506096100150500e00b0390071100101c18842d801480e0050751138400480c404400e510600b085601a034445407806a5558100d26541454001c86040c01c0c5010f2100c1c60841030800400d4454001c2d00e4001e041262506610704400f8005110304c0d1210210760b4119103e031501c05406010201e1494a280b0070b104040342d002d408080001e45982069001d0110342c2802e030550350580e030860180038006010020710301a5406510100110380c40f4100030b2004217801ca14000024081381c0290400d03802a0304a40501701940b40c007048426048241c1110040d40d0344107041d800750122540703a041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 515837338 1250 515836088 515836093
    0x1090804080102280203040506032a07021c11040e01180503040e100f0e090a1515050411090108060117070e210619060e101d1b031305 59
    0x2155011056000e400c0e2011400d550b06000342d03034192a81e194090a0031340f4001070f4010802401142800c2000d941c00c44524484118a50342d01d145000d03180850408040c10700c0c801003921402c5d4607100800410066090051864000c004d8841d02c001c902001220750082c0d07100d115940e02d030542540079801152002c407024194041503e841522940680314040d48107081c40d0210b1451201311354840d0803107140d495628070f15850190000300c460740080c90400e5030702449950001007139031008918102c1c40d20440014000700c2100940c000250740703801460080c0c1ca0074404e171800030000002c450381f8540900701110b242d910003004036000c0b0621f1500940c0243c00d40300740643c3d16045180b204080e28102d542d034401442e102c00418040e264000a01100c0d40b0000204881c9951a0301040d185036083c1008141241c031041075441c1c00109403083c80c038a2100c2d42081100320f8001d00c40002c020499101c8136014101328400c1d031980200c400d02d2170810940040803d00c00704298902610f1254404103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 515838588 1250 515837338 515837347
    0x90615010c0b1317030928140129010914030c0607060f1b020303240301021201090501080304060207060e060d180302120a0c15091e0611120612010908 66
    0xd110f1580c25040e001c840490b4810030816101807200c01340d92107440d01c10000d1101e16517190f005031406034002c01d400b1003c00c10700504400304042500c044103c1c802c04001140392142140044082941403c22994410359030003131031101eaa0010004044480741400341060a26403400203040036800c162540d400440022080108605074001c0304800803c1e8408000f80f41c0ea086550054040c05a40880141c00800c0029446546580d4400401080316100b0110344602d4001c2030072a4495155041c8001c401070042210300020b000385405001020007035803c0924002010795210707114040c2906024440c5074000031912001e0541c0e80911044d401803005100706046200ca8035000b50080e40140a030940603000311035442c046800c0006560344216060314640c50b03441c201515030100340d88868030307801020041404e50401c2d020f001e248507901b40000405280540864010304480c1a00c00020700450f030900078040a010361004094032003d42569010f40854010800030000030300400300480d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 515839838 1250 515838588 515838601
    0x301061101050a020a05031801060302060f07020406050f0102210d1b0e010804170d0b1216171f021b01061706093a0f080f090615010c0b 60
    0x60309000c40200503000b002151903001603c02a40702d8071985034081402000410501001108211021800c02000040e07543e01e035400612a41d100c601207170507600e004100102946814442c00004200441c2c90030120700818002070b464810760b805e0391085201e215448080c10380800200c60a15441303107c1000b43d278900c1c6c5506103000010392004000107621544448565001d046114003642e00b0803c554601c91101c2231500c0721340c0c0300e202a10038080d12411038602d5500c03100c2e22015500c0003180684004070b0340d645d421940600355405090840181910b000030203001140d036161420744048804000001c11080398080e1080144941c049045920b414050910662001302035482a13280c2e01008280507189540e42c500944205000b03800c038603c0400c4035580000850703452480070b01c0315010340c8011803441d2004c0c01c1202c204000b00f0b00c400f00715100241e200c0e0602c0e91044030355a0040300d80c00d0200045a6910000b0884402c41d520108040e100c3d0780624000300d40320340d020b102007001e440c101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 515841088 1250 515839838 515839847
    0x70309030c0c0e071e0e0f011404030b01061b0f020d0816110f06120a05041a10030201030b0109060e011101020c030a091805010302090f04060212070c1b060e04021e030106 75
    0x48600d0740c0000d91842481d619100c170642c619440c0d403e140c0e650100340c000801080700943ea104065418030940031500501c1c0c11050700a80004d6016041c42001980f42040103084221000000c0c030f051402c545100c00000c248840908810b601900c10308000d071850302c1d09031520b01c81d00b040080c003e40661000400c11103561804000c101040c1c402c1d00c105902981800801d001d803001d40c11050112000090b0300f589203503c40e80d4011301a541a10003801d040240e00781c03c1341e0070f0300d6001580b003140205100b03558041c05101c030800ca00303280042c809490420b004002d40c2d0010038042c10405019a6451304401c01d4044c0e65a054015081c1c07503035840007231000b41524101e8070400e4001220189010719413840c6101d0300f81220380103052901c0d1651120481011900c004000322007269080c40084101d001174007a441c4a50015110070032206105d0401c4440d0404009074100080281d02e0144a141d42c000c4954218410560740907854141c0828000954030706640000b81151021000040c2154003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 515842338 1250 515841088 515841091
    0xe06060901182a030e0706020a0632100e0103020d03030b010c0506070309030908010c14250605010501030e01110d020f04030f0f020a0602071202060906090306150f1206070309030c0c0e 81
    0x1c54504204405c10107a040391101c02c01e100ba0b90141e00101204000b291164201c440c00d60b010341c00030880340c03001381e581ea01081c006044010021504108101420803034010b00d2026100c0c0c0f5440048540c51a030008502c0011604d0090070117840303005404059020b4030400c00b071380d44d00005076295032038000b60007002005c20810507400142e03081e10000b9a00418031803c40d0f062842d955881c80b0428110308800b840d4007000140242440f40f207030583c4030150001125007481c0c4943d402094951500c8001000d0700e10f9100300841591508036079102602402e0304813a05170540d400d0268542c50701802440e02c034003e691028001c1040e0f8250201008062040744a60340d20895080c440d6075120035040343c0c1c034021030282540a107000c40040d0301600e0007002a18201d0ba00407c682d18180c2e0b4100824200041075503030840f0307074100c480c00e80494942000040203a0034107840441c01854455107403a900c0c81c0c0609440c0515507505131080038148100b010400c1d05400485c04050b055482441070000c040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 515843588 1250 515842338 515842421
    0x30f1118010503091e0f0f151e07081504140405010e0730120905031b090604051005090c0c0606040908070b07180f0302040e0606090118 60
    0x50500315440558001c100750b84c0240d0048008040c11079140d010b001c01003002c00241581031068803000c2070720384c00410030520042c0e4050054007101d600a8039505444001401c0010340d80581015081e0b202001c0c1140c60344031020740741c10001038903040002000044188607540c1c1060915480103000c0f03941006941c0183e1054008002c3c09442c00001034446240740a00740d82c9001810703003000003900c80c044180c0d0710550400c40790b0383c0d000e031070f40c1b0030115410b111078003400700348204810005072509112224840b0040040e918110608c1070001d250741200502c49882039031340e0408138031340d8002e0316600c1c1c0141402400f01c1002d1309040c2000d144c15000030010100301c0c41040d00044140c10903000380c0c1c494903404035104c5d050241c0342d5111142ca5400420031410086980752580450100c0701c8072100030280c3c07024102c1a1421401404140d0b00400004003460340900103022a0780c58a80c6120304441020780400359031124422804081d218200c0512070011090700d480f01080c0b90701060700c0305c40384c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 515844838 1250 515843588 515843617
    0xa0804031101050c0d0525060b0102062404181208010314120301050603090a0b280608190602091504140f010e13110c0105070207080609030a0f030f11 66
    0xa10788001141c007031140d2001002c030b5401509044488074050000380000c02c80017040422452035164140e44515000f04040d40d5164a4094421441d40c05210307894108152103521074180d204841c0d070307800d420a9001041d0086950700b0301f00d014420000c034010082c070380c004c00d403485080c040b102c0142104000e020540d00340c034100c2406000c0d1903001400807443c0300c480b0b030481d045a1801c0c082100c29080181405c0d031b117000e0701000100246e40650580d200e884400124408508154444108000004580c0d140f051400358184031124001820603d00e0400b030f88860041d240c0c600e4810044e01481c002650008085025804800002800380054a00694186048000010800c440600c401e20a280130851020004545003090000075110710000c2001042c0802d4220080b0141c2e405845110800d075035070740c24854201e81c1404a1001080500d000380880c2c203117088501e23101c3c0b04001002040c42079040c0240b0081d07010360810281003400410801a40040704c44032182d5600038012840240c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 515846088 1250 515844838 515844863
    0x120a061409030406080109092604090f091e020102030408100c0e0f0a14150d09051509121308030c0715030903200316080c06010e040f0b0601110a080403 67
    0x141e00081030390200c071500d0742c404c600c0341d00c0c1000d024000c1081480070f03100b80307038180e09503480f080079003080301d00704001548001d90340c44c03601c80d00c0b00c1154854140080c5560400f8040004503c0c0021b404800911400c4410a403041a20050303185225941c00180c45020f1411284c1014945a104c3c0c001c03019241c85044c10310258004020300710b00341c04582c80e88205036040900003a450080b4000e84404098902c0c205010610880c070318a410810062905a03290600c1d101003144c01c1c001c11011419803030201a180c01c012220a8550341455844030320034030041040103c0c201c003a61410700030158041036a6441c02403100c0a0b89400f0180904200010440c510140b032a100c1d00c04d580074290907030b03204000f8071a000c0e10140459942203d6814a1106100b208070113040101400b981902c10400395544205d010b82590401c0d005038007014601c01c9210400000c1640ba42c03240d0b8445e50710000556061781c40d400141ea45c0103000210040e43d1003999905c0c402c00140900800580b030080312400c100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 515847338 1250 515846088 515846101
    0xb0f040c0206181e0106030c0e040f0609031704030e0109140105180a150507110a06050909040201090b0a120e0109050705060c07031b0501030b2d120a0614 68
    0x6035200c005510005078800000907103c030b60f282441441509a03d42903800410300210741072840050030780780c500e059545d90320820400c480e00f40050010a03890000c0d144928040e04d9009050401c0390000d0074807130f00ca003000f00801d0720818a0544514002d41d40f082181403a08009010710b402344412030214104a00108480d503ea2640d40c2c00024141c1d074641c60441c05148440240c050109000d8000500940201d030301050a110249081d01c2c9588003030b240c080f241098441100c00d404001d0040c441c14a0501505920000300e401c103103010360714000107858620048480002c00d40c4176900150011618003178483c1c2c00218401c070200c2002e0140840b5400f040001e00b00c90a62800901950003000c042099051250240c100b030030f121825550321035a45c1e01c500e01c0400944010360580301c85842d040c4050760b0580310380800d61390103881025103034440c80d00e0603000510075030960f0084800000591642c0e44c0c0c080c005070307021082405544944100d460b1030800f03448048101c40e12800c80701c00243c031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 515848588 1250 515847338 515847341
    0x1e070609050f1614060c071517010602060106030207080c061603060906050a0303030c11010204090c080109051b0309030403020409080d0b0619050f0706020a020a0b070e0303040302040507210b0f04 86
    0x20000540d82d00d441c840e240c1103130f80300b09034640d43c0007a4000d003041c05038000d01c07001400720380000d06126254110301022044010048100e40001020700720040005000441c1c0c00030740581581c001e4140141d98403a10b0811035414002c90031194814403038072041000c000c60107010895a0202138900344102d9403200181d0f03086e1481c0d03004d00c0e40c2101c001a010000f0030b20130340180a40010509100c0071041280300b0f1142039a00c5604141200c0761035201000e8800d501480060050510000402a03404c083d51228103250002040e9980c01401002040103208180101e60007907900400801c5003009500e8a22003940101c0c2054403154600003154409041c440e040301c20b41801040308a5080d000d0b140d05803142d0300440c02512000506020f0000019602c1c402440301282c04c1d00140000e40051070220200300e40200a80100902c45001004640b400029203041da941282d0204803076031101d4007100c22030358502d1400d480340c1c60811074018114890b804810442415540b41d0b840328503035400d120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 515849838 1250 515848588 515848603
    0xc0306050114031b0a051810230f04020d020409050a06060c0308070f0e13091b0f2d120b0f0705041211091503190f02061e070609050f 59
    0x20f405412209590b01041d1800f01c006020290080c00f00014030f032200045105510baa00b200f000740007400041c06203924078409164002d0040e00840d0b190841ca440700c1c6507216400c2030700d450103250b28003200410740c1d4440c0c06035041c0440d040d404540b00c540d00ca0300032001c0d15080d1021400145046004504c1c81e02c0341402040541c1c05444d400c4554807401411201c510403040d1400c100034036545c0c080340607a6660f20002c1e03681820440450056001d0030860714031040905145280111074071b080001640e4120b0400480d400649022030300d10b5910540d9410f440107450340501e40591190104040d0482d94022400324019003a01c6d0496541288081c04480700385e4126000c280144003c10055101701c032460069845480e0007007511450101081548034281c1c0c1c51600b0350100d80c1d24480508003008400c400000e00002d544182d6069103070007241e210548000b0380103080000d0407000b140104104000706100303139103140b80e46010341d042600081c180c2130002c84141c0900c00404244184c00104017 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 515851088 1250 515849838 515849879
    0x3040609030803090304152106060e2e0c0b010902030103020a091e09030e1206040b041209032a2c1503010f06050a05180a150803070c03060501 63
    0xc112940c01d64444402c95040208003040c1e82c40208008207560002c80300c410300302034058440c21490a4048490304030003c0345402c01c0d031228039088040155035802500085a0311095848807900340d108030360040c01412805880303c40c116105441000154030488194015004144229041e43c903803e4207402c0e40702c2840042d600c0094140d050081a02d01e40c071a10b03004600650704404002019034440985242c48000e502059040d50707811580d05210010040301c030417640141007980b0741603030303001542c40303016101a01580c1a888028842402842070401541d008403100200d02080810360360b03180c1d1840315945d480c145034a0006802e190050341180c450400101d803280011031000ca20f84085402440300b10981c102403001c29244d1428854000c0d2401601000f14600f818402400084241980601d008499125070144c44191071070130780d500503111404c0410004480b1200e983c02c2207a541041286010020700b1008000c1070b0316102d002c8a10400c0c050115030783e11003a40c25507401d40140c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 515852338 1250 515851088 515851097
    0x1030e061024050901030f02121e0106030b210708120301080d0908100902011206080f060108030322050c041418030a02070303081905010303170a020307200a08030a1d030406 76
    0x703031141076004c1e4005650050b40c4080050800070103589c040c0031700c0c10944036401e640c000f106074140c0d51812000602d001d0561401e00703021981101d03004c642c0f84c040d165030721102d1aa00d401d0f204040c2e80d041c80200c0062801e44100c1e00f10074032421010090782d000784190a02c074490a500c0d07a034214054070030300d02184c085d00043c01c10000c0710940c120140028080c02ca040000e110606101c0c154a841071034090495003000748481d01c10440000e00e4200c0603003082400780e10500400402d80c644a005225602c9000f01080750700c1c3d502e103001850b1549000c41c4542c01030400c4402001a0300c1c11804520450a01c40703414070354221580099201e20481840c10300507081160248003103802080b03019003108882d642ca0b065500d41525000c1100c0303007078008400141008411703074041d401c0b0311070b056003101c08000110318600780300300003038030071841c0217056000e01e40700d160303142c500050511100420980000c09981d60f4508100e0714001800c6044407038080d900094040c40f64540c0c0081038400b981c140307454 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 515853588 1250 515852338 515852347
    0x806010507170a17010b0f0f1c18110f0901090b01120f0207050607090f09090f050109050106060f031109010c080f070501020d0e03160b0601030e06102405 68
    0x115510780c4406401e49030b60024662084084040c0001000710603403903990b01588105a48a0b1100258180e2104c0301c920300a1101034441032120003243d2000700a212001e640307060200c800000c500760a50b0f2030b506685005e250000310360700701c0340e10031107141b140c150300002c0f41d400740c200b103501c000721000c0e0780e0414401c1c40184825229a0b1109003c02c0050400308040c88020b4074a80a507240d000d4880031072500400da60b02000b50800072250088510700380794420703d08082195402000c1d0b882105000340d2904404000d00003642a0302d2803c5802030b00a203c02c1140e81411800b8154501c41e540000b02a100f403260f01520901c65120407030000951103203440c44440044548950020041d10852410800181552113160040548030311500c00503848001e840c580d00c0c212112900d411015400c03c000368120904074803007004500c0c0d84280011029101c0000407001000c409440140900c901010b005003080f04001180c102c40c204104541035148000e81008501c2c10300c846000441c40030710 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 515854838 1250 515853588 515853601
    0xa0b064f0b042d441015030b041b0f060c060203060a0b03040515011d04060b011407030801092702090c0f070309090e0705092a190e1c020d1104060303081806060108 72
    0x700702460300003000200f940d46e1601d82d01c41c480c1019081c0c804454402284440350118104010114014041031442034005451300002502031401104002c01041c1e0001c000740e20343d6a040302440103070500b0090b1581341d1810f4603106643c1c0810720725142c15148003100000303444101d500e0500f000b048420031586181c0f181ea40d0400a03110640c81c1c103041c40b040c612140314a20b2408040c0000d5802079030741001d6940740c46c1d2040b007190804501d000d0708880c030240700c184100c00d80c015850407590643d8000620395900312603241d64000c07808a2404e00200040c05024503501400d83d4040e14407011040001c0c42c6032443d25944ea4000784900b64104d00e901001170051141420300f01700940d2108000c14241c8000226801c10360302c8040410703905c0041901c410b00340785d8031110b8588402c00503a0754400490404074049100c4a105c07000070702c1048149100d00400c095160b444190f50000f9205109070380e164507000d4021003085401d162500c0900844610070100080c4450082034180c4480505450302d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 515856088 1250 515854838 515854841
    0x706112505070314060f07080402061801021f060e2d04030e0a120b06010206100513021902010b090a0b064f0b042d4410 53
    0x8641070350907010342500000810f0200407210786440640000d08110320f8582040203c43e50050900360400490b0300c10003005841d03020848074510000d108401c881360250300105d1500c1300b007520f07108040448985080175441940c00403425149460804e44036507a13a030703940028640300081c40d500c04501c1110032090254514504607007082c020b241c1802c2003802070012a14600712a0702000041c201600b2501c240300346254856000394007440640300390706200030031050300d500e40d016040c85101443d01c1d80c14082c10f950304403615207901d80c1c0c02c03120310060200042e0081c00a90985802854100000752400115100310590880300400300ea0800c3d01a8100368440c3c0600c00980c41599006540c0d0301100e55401074900ca20040c55a11040f03c04940559a0002d4020380c00188003400910050005030300203815080070b501c81005d43e9207180d140201b058441c02c000d0740400d010707440c256542c03900741640c541a0b0400c00f091080c00c00d610b54400e036020f480401c1402c6085030b107801c006150400325515 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 515857338 1250 515856088 515856157
    0xc0a0f0305071b0f140a05040c0e180a18080f0f04050613141801031b0b0f0c07060507030804030e030f030c0102121f03080c0102120408070611 63
    0x41d10306941004880d5031608103903001c140921120480c1c8a008021411414002c00064407002070240c1815000001149910f50540185481103884104080701c09105104407500803000508a038425480b04e80000206007080c0c890042003402c00c00d001c200c41c2607c0390446012641b00c00316a1512065103004866900180801400071074100800226070759920017421421315109000c2078410b00e880004c1c440c11132013402160050310003041e00760700f003464801040e04498009030310040104100e5080b80c110905600000824103001c00c0900500f034169000d000c44080031421906101e03210502506c590148030002400605200002000a4441c150542c01c2d0000507048a00310741c086100030703041d50041403888580340c3d070104014240b45010031505400c5070714a001b08802d01d000c0c0c0c4003414181c0240c08085c0600e4800204045000c200354116480081c3e0b4100d949028100b918091300f0950040c68161651803c1004504407071040c0001c494401d11815940d0030f5080340c22581401e503041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 515858588 1250 515857338 515857343
    0x90f0106051e04090603030806040b1c02040b06090d2102010227030a061a0f100f1d090f01051806130e0102120c1c05070c02060304020d0507080d140c0a0f 68
    0x8060000040c0e02d9001e005d1080a140700c2e4580150624045092104035890300004500c50781c13130304000c043c159004c054403400c0c3c00d4055a000c0348102154010030910701c01d10b500d5980001340f010003c1c0501695010403440031100356203211071290f01c445e00b02d00303034000c078154482c0a603520300101d0031400082e060140804000f40a56201c003000c0c0d182c83d012a07142c00591107041d0301e0445101040e260034209422801004c0b2481840403141860007014100386031600030074040c04580b400591020b445451101d06002004a80e0a141c070408d500d5115100388074144c042c6c0441c402c1c3c0180d0254809a5610445024010040d00002c40d86440050401c404505000d0f5500b0800b404400b600d1500b9188900c141d240391030344c9c6280140300320441d40d0030070aa0001f1a4600014041c0aa60048030031241e071783c04032021604d9443c2c80c000501d4031410700750000c1035803260b0940043c030040086080c05011004d0f44032038042c40d40c2c2c1415842c0522449041c8901c60b0008292180050382c0d06824420321030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 515859838 1250 515858588 515858647
    0x601120803073b040b12122115040e01090f02060d0e19111203090105031b031603061203140309160909150c080f0a180f02090f010605 59
    0x84104112840401c10b00b28042c0c6954000640c0f4260342440d0007407558007041640d0a40c40e001c1d007803251a0700c0e04013920034069401350015080a000d0000b030300e0080c0030a010030280040303042250180c484001c071202c0f01d42c080c0703080841c00f070a50350040c8030b500d402c40e800218030101d0b608207a081200075446a807800d0241a6600f100c202c0c80402003010080f02d110640489861150740d003006210540c0b119000c0c2c0c030405401c5092400ca100100945061200c20b08003203840781c40c1c401030064188400b800c9400300d0b00300030040000642144519040f82512038804203c280e4070380843c050b03005407200c03002e07002c030300b06038181104071940800555100c0c200381c0c103480744007a0001c01d40c100081181e21940040380c40da8600428002c0c0030380441002d00341c0d5081000b1030185020040c080240c001c040c45d22030000f8000266031009260807481e03645144d03050100a0280c44c2c42c1c000d074050f00e0040140d0240000c00b0004201401130a01181601c800307840c0e0702e04008100071116008201300e02c0382c01508 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 515861088 1250 515859838 515859887
    0xb040509130201020f10140109061a07020a09020c0a11030f120c0114090304081002120402010e0d0213020418020903060402102a11040b060a12110c0a020102060112080307 75
    0x44001e010316440c1c6c0340080350204070201c0c04240441d02000603000b090400d031404030308000042030a41c280c00740c1604684c49980718895400024000c02c8076600c00300b1494000180d85940c1500807c0700051144110180f0120303c480400303160b61294428000c1140303034032400740360b1301212202c0013030a00106420004140b43d1205101e0030007140e801e82c2c00f60640da0000c6018412920306204e18903a980c41401c04500301020100350b0a840c20000c1c201a06200104207a001651159842c0c2080c00d42c024081014a800c0c035026a0001c0d80244190600d2100f04410310264132808c1c001c0350410500200201002d445503020496141e5040c10070805115a6500305d00b185549010300c8070b03140d10042e5103403c0a4059090516003800c1e5044428440e41c5801c98404442e43d030203050b2140d1810b21700d02009607203119015000204202c80581307201100119903842d40002c0012a911501c0c400e07820b480d4680d90341c08000010701c2c0601001086d0100c107100042da000e20801c07100c082c1420541104801 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 515862338 1250 515861088 515861113
    0x902040204080f030c0d08090703110102030705011a040b01020303040c0e100f081005090f06190204330f140703050702090702010501050405010605041a09150f0c070b04050913020102 80
    0x4000c410b82903030b0f18603000410380c200420300a1000301c00000c01814008458540141c005880341114080240419000b0a0714000c0741d200308103582174540d000008026640404140c066030b0360b0504c0c5441d203c3c034102000c06026501c00b0099900465101560040c86170401d1422000e00200070314001240c901e00d2800140c02c002070001d24000d0030802c01030a0540d8180c0015000d0301c00081c41c1500603880700507c00d14600780018403542c40848036041003c00780060720b000e4041d1150364804080000d61a10032010141800011510b006c22403081e00c1290b10514030550303045d99011120340114090350403609021700300c0401010340030311a01e4540d01d001c60310b40c001460b1050503214880140e54990040c0114101841080c2c05440b00e428010f08151600d8281c44442080405840c0003000c0403e9400b00c0d5120b03c2c030300109000180c0a150f0311400d003c5c2d82c00156420001e41050305115810000983c1c000c0ea008a50680d0005001d50020b5510001c0109200140080490451003510300f031000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 515863588 1250 515862338 515862343
    0x3090e070c05030a051c0b060a030b04020408010c21060501020a1712131a0c1b0705030d050309010f06140f13020310030203071d01061124010806090d12090204020408 73
    0x1350b05141d445042d00d803915039819950701e00ca20058105a94030780140144645d80301c1c020f40f540300300d4501d008103c604900700403d02178069036000b03900540c02d01c2c2071903034006d0304080c150079204c43c4590500c40101e411802c00301035688901c00c1da0f01603009001da91001c1060500140900d1401d40301c40c51511840c1c0c9410201c426040b2020380e074448014081e541040340040480c01110398038144081d590400060303d02003486042c840b00406502002e620500d01e00600011000300703070050585260200106024010f98030450318118036501c1c1101050f883d0f031080c07040b078041d0750079107003c400108071010610030015120101180d1142a1401d070440d40c2c0716500003148507180700c5086042c014510f205043c9022903541101c401810607500103060358040b04182070440d0054a04080c02002d1030961508060b00e5090070340c0c500c00c1004520840c131904010083c103c50150307080710010ba035409001521a003140c940300c4000341c201c494151820026402200c10f01e80011300051406994045861 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 515864838 1250 515863588 515863597
    0xc010f1406150408071715090d0e03010b04050108150f040515040809090703060501090602060f1b190906090b0903250803130920031b07060509011401050d03090e070c0503 75
    0xb00d080501c01c5540034080014045481081c0000003c8016424144c02311512040700071010070400110b20903404003a43c003504100508100a8070030045541c513020790940f80e080c04180311003020a0400490421002e002440c0c0c820703600308014200007184480189503804024001f9107600009000d051580e0740c0e441143e500403c4162400250791780703410000b6141100540c0aa02590000310420202c00042c8640c5540300440180c0d03d100d01303060a16000d800d0041102242010340b1400350881d8054214400e003058403a07079180c1d82c92444d030380c40444046104260406030550456242c850b900d10300284903800c00440b444c446152182c43d11701003840c2d50080038141c02c038650035100030071000c80d03a889085038840f0540c2c250580042c46090502c00c0380700103800f541c0c41d42480001e10184041d583e0544509950164003030050382082030410740030b08141103501049400708000000d4500c0e001c069030900036070640301c0242d203502e0209100c3c94070030002d04500c2888084030f088000210b0034002403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 515866088 1250 515864838 515864849
    0x140a1e050103060e0f01030b0a14070c02090c040b0f2808010e1803090d020a05030a0506040605060303130b070602070f0602070209070318140f07030b090709060315020a090e070201020c010f140615040807 89
    0x100333051101b50040000340d540150a010228104100038005001002c0807500307011803480070ba903640c0c1100440c40301042e039801e48445103004644221040140c1c8440d030141240e859100c80e00751a125207082d480421002c0f000307406180d000300f06040700d0b41400300e040741c40307107000502c01c24510356a40c0204c1d081102944040300d49400c503004000811078144602d03600b00c44150025070600e224040b0000d180846070103840319010740400c0e401c00b0000705404880d00540e21954480d0300840d24903051010f034100340310491060900c4400a51240c0c0329200740b181c603d1220181c4615049152a03996401e40402c1350094180503402c1200b109407070400c500c000070351050b003460301c15240410780d00c2c1c10030546d078000c0710340d840c1000b001b04081090224001504c00b40c46600603524000b03031406072008515940440d40c2c203a040801c0200080d010340c00707002046021002405119081c0c080c660884006c0c16000a02c185404089100c2d810040d01341d00078a40c12203c0b1503d41501c42c1c420070710b419090342c0f01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 515867338 1250 515866088 515866097
    0x20d0905010f090803062209031205060f0901180603050307050f070b04050102060a0b0418030306080d0c0b010311130203042316140a1e050103060e0f01030b0a1407 72
    0x160420054244200c20464000e50010005809107035940c0040c0c3c48007030301151245001411082402040060203252072034411020005410750b4075010b0300302c8011580c0a0b642a1a11000919600b06100c85402511000f00510800ea00342a802d20b00d50702c5100000c1c0c55655185004030010344104001c0c03c002e40514000d24102e814803101d2440c00a058001481c400018401004680d800007030490b00800001400f150079523140d000b203070080440764070f6904000c2c2c458140d90306240d003503849102680c40300d0065814110a03030700b09450000c96004010a4410b40100402c0030071102c110702c2001e500c0052800164060a142c01c40a0ba04255401c1e540b8410100480c3d00f180c1c10034900b90491040e900140550740911324130b00b09418440e1003903c0b124045500d040900b50759642c40c02000d01140703c640c0d10141108002401a40000c2c0640390204e1720b03089010500b000d2041245218443c0c1d100301c00c490323a08555035400441009000800400c0e01d030a0003e40d00d40000342014800d02c4956507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 515868588 1250 515867338 515867351
    0x3051e03010b070b0c1908041113060e07020d1b030309020619090501030509060f18010204060203092103031605160803160516030503181f061a0405010e040f020d 71
    0x415084e41400502003854001c820400c00c0c1010020b46040010000d050800c50130a5aa905258840040d0040c00651011003002084239920301940f041d42500c044c00c2100115070340e41e81c016a520741114940b100440c0d042140c40501084ae45a201103661007440c001c5480070b01030b4081541508424101c59001441c0b554104445501200c3e04000782024030342072046090010500307807070f039030043d001041c10039143e00014007095004030400d820400750002150f485030b039610f0003034898020300151482510348800b690f0514401d450041c0c010703281d84020b58650745800f200389481c2d610000984080c440e042c00b141107180035400405419501444ca21542c0c1e1030301e003440b0281c107041d8000c10070a12405001001c1c2200c51600794500d039030b86c14201250340361503500042840f408104010301c070510034078080040d41048101031100440c18075a05000f403988038640080030142002c0442c035990302c1408100941d620070111041c0412000d040001c0c203500c00034003003003664400c1405041d900d40340c54 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 515869838 1250 515868588 515868593
    0x61608040b270d1104091a130303050606090622030503161221020a0e040e01140a09030509060304021c05060712060506030708100806090703030f0e0d03051e03010b07 73
    0x5103188102c10122031542e100030b800c4d42c0d101e0140001407202d502030759544510004000d400884280580c1500700a601c1c0c0d40b4100132080c00c0c41030011003c03000030782454085105420483c003501c903142d40003040d4505100c1040c600e0700e1502c0341500d2050b80740c940411f0020100e0801d00060035511020311542450070350a05040d02e00b40300304507460040180b02526501e50540e0480c048190040780c84001da943c1d03030340c01d05c100d4075000400c542d15482843c210103520883c40550003580315a41c28404180c0390740e5001502e01c12103480d81c3c4e025011641c10010b5507090720b813180044d0340c402c1c40200340c80d1101230800c400300f401701c0e007100701228640d1010080c4501e55411041900d079103450744400b0300c01c943c01c0a010510b14000688034038140015031000c50038500b032254810707001e1324120044407100c0c6400124248c0c0c0340494802070300481c0300410141441071080000580c0c030100a0322055001106507422515607001c090801402400028919030032407400c00118000c03c0d00c2d170f12041c0c4541c46070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 515871088 1250 515869838 515869897
    0x110d0c0f15020309010f03020f07020612160f022806021b0105150604050d0c150f0f0f0206040b040c15030509120a120f0912031b020c061608040b 64
    0x4040701554800d00408000f070b039015030400d00c55041c5140150f1118030341a0203407010b000f400e01c020752108020884044104150039260b01c102058030380202003550080e07050362488820303030000700142c20181500719500c000101415492307d80c1114180030703401c25140c403c22a040440404511074a034030080030005e5090040581101e0b460307220209811001c000141507200c0c901c038075805500350008203420b0180c10160a4010898150302c09407000001c81c004000c154003c0211010540500014601030b20031448480d24030b980b07400500701525691208115000001e00803240303111545808141d140002444010440c91500c001c103803403d102405904040014058180c00300044c04507180d0654060032000807d1604400016140201c0e0485009410344041c0544815080d11081e106c4c1503141d4040c21b41d46040e100144a19110b55500f240c540903c84c05245d0b000e4400e01803401240d103a110200c000700e20441c40705107025602d030002c406540148005c442e5001c61022003040b4500c03003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 515872338 1250 515871088 515871119
    0x903120702150f01260309060a0c0611070807080345010903050f1e07080702120a0b0c0a0318030e100207050102100c0c062c010501050904110d0c0f 65
    0xd20411540f07039810107175402900003501881083c00405201d6444035968180100c9400e55030107005c0f640c2d1000452409400983c5040c022a4807500c1d2000f400c407507904100a54a220ba8041785607440d040003900e0785049608050190654030030301089118010340740c8a0052807003640440c0990030280050f0150b81c03e003c1030001c1415603410414040c1c0003a50050444201d10001c4c507010340c403041a5914101d4045c001c1c130f610468802e0000d1501e0078000954060214103100302c8070b4850708440007000d1a03c802083ca00100700d000300d1000b00f02c0781e43c062006800340c1030300362034000342d824041440c0c0c66100b106400141e001c00e0048884589174101030702c400b20814064001400210b1500f40000d5403117505442d83e0003050340d1201c05040b11880380b15030707040c0d958002900380110345001c1076080c1c0302003c40c0d0001c0a07482c00484c0c00280c089060040038100e59004207942d4181c1e64030340307600400d07402446816030700821813201207000401943d0114040c000360a4040665402c4c030080c4c0e90b000e502c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 515873588 1250 515872338 515872351
    0x602010509071203050c060403120e0c03070e0601170114010809071409040c08010e06090709060f090207050708101b0806090402010c050106180906062c090312070215 73
    0x500081002000000440d10100c640610340b120301c0ca030f45070404980e00c0c085c080c035007601802144240414158400203e042c0840340305403c100124012080aa8502e80c1d41c18050b0141c0120404001d150204d840b07040d4424410304001c089058100c84805c8060303401d030880030100040700c03565100b55a2200004d03902c240d00741e0040080b18104148482c118080f01002e07881070849400040800c421323031102c1c400401d180c41c02030003040c48070390140761254411180c489451190040c005483c4290380140000c035400303e117155403001e0500044102135071003158291002d2181c1c9800284200b010000d03001e8444003410001100f030800a07141c01d44070001d41a5004000142e001c1c000c4950303490f4145c1d5000742d030908102c0607402482c035010f40586a241d01400714582c6020808c02c00149a805c01075406215100c100001500c82c100b1041c004028019118000d014681020b180c210840042e17400841c050101d070b041c61a01860301c000c10350f0844240c40180c02220b1052101c0318070501d4130b9041368 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 515874838 1250 515873588 515873591
    0x3021606080f15032a090c1c3e4605040f0503010606090905040507150f2703020105160206040303110c0f060a03090f0804060201090c150f030207021815010306060201 73
    0x2400c07212501907000f5034a404c1c1c01c900c023440154041008590018045d2002c051510158490340900808490291028088601c006400c0008218038007012512024405442c050820803420210380320a0042c010060f80d02d039010800c00441132004901501c8111036070b4410b5611401d02c501100c041140b030744942d0003607041c5401400078a0704000a13500741d42000c04001030030740e82d41c200340d4500101c5034458904031143d04901c03026194401d84048902e03203107440c0c10150000311445110750b641d1412402c42c103001c040b0010b10040d0311901c001e24081d240c1810f458624145500010003590144d072045000c0350710611080381821042c0600100000300700c4000e00d40300041800f1401c54030480200108250f03560f582007040151080740e80c20101c0c0c01c03200390b6441d16101d1030007900a0141c443c1c02e840310080b103040000d030100e4121801c14080441c0d03407009405803c80d80250040e421030082240c2c001400c40e80325115000b030f010700a1040401080b01851040e281001408a50310341d0015030459 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 515876088 1250 515874838 515874841
    0x130207112e0509010e010221031b0301060806040605120a02010810080304090e0601241d04020c0109140109080708070201091a0703021606080f15032a09 67
    0x2804804003600324039090701c1c25040324100d2084454401c05070a101e0210700032a40018480707a80c04000307840c1d00182a01c4488a02801a005980c0c403120405141c00390030356074200c0c204540041d40990340100e822a01c00d404208880e6000d00290403d030000000200d5140c2001180c3c0f400b07001e03000081000b40c440e123001e031007103900454486120701e402a06102e810700202d072140a0350b03040100180440003c0d240c9980c0c40305e1701e170740c05011002042c6585105035000821201e03a40010495030b1940050040c490380d54540d425510345031500780106a500503500386101da074650b0700003803032043d080400000710814245010010716509a8200c565a0703d07200300000001c000d0821201000c0d00a44526200c880300c4c070040b50101800d8108000480c4800043c11403070070400c01400c841c0d4072036001d640194506035070202500c00e10b44111030000d124140030611400701c3c1e50340c0940000f40244800e102c0d1100b0b0b000b0074038000718031908074014080400d89400041c2c811020441c0d1420494a8208030b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 515877338 1250 515876088 515876093
    0x10b03040515061207090609050903090303040e060a09090506160203090a050f030a0f0f0c080105152e02030409150b09120c0d11040e010b06030106030905070509090606130207 77
    0x462002400c040c0b4800c482101041895682a400040301030440b8215202540c40f1405440640b65502c5007000550800001c40d1030954048143d40000310060004d40c1804e00d4501c2c8218001e40140440c6e030007266000001c2030684940c0540403a05000768014292820720320f507000c290800c2c035040303038045400c01c0c0031440c80f6517070781c034800c80032140200c62185007001c0c000c00280c20011409402010b5055002260080060a00c52114002e01030740324450301c1584c0c0c2d1503c07400d0b110b0480768406108043d0301d4041f5140b400c00307900780e100506020b106a42c80c914003141c20001d00308000590160780301181c104043c801c140241c180010419042a215520f024002501401400100b07441072041d44442a8503002c1000b030340910500040440104c0402d074200245203445c1c40d20598007880c1800c8242002650500907003200020241031185140c0c0b81050440040c130704144c0c01c0340c980c042d411001a588d554a020b4900030b400004c00340842e410485c00708250707000c140014a41c8113005100d42e102 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 515878588 1250 515877338 515877343
    0x307081e031302010e12062d09071503050609060d1b080c270109090323190302130306050c09040509030a09050d050a0314090d030c0b0c0f0d02180a031406010b030405 73
    0x40040c81c1ca81e00c0c4228100800c010070618480e08c00300c40180400d101040200340b00000d00d00b00706c2e0340310710a03500344c000004002c03403d4440c202c419036080220400441d0441c140002c0102c0d400b40200c00307034000400c90420344500484c440e4405101a4000c0c1a0a02c00e031905034225a2007007218807100610143c0c3c0c0d10f40c95030030881413140b981050341d03400d60300e001d06000340c03146070343c0ca842202d810f0481e209a900310b8076030342c0081800c080f11501300300c209120303a4060f1085801d000102102842031034596620172018000081481c20448000e0203240050303142ca0095034050f01704800555210910140e0040c4070b4001c0f607000310310804640f013401c80481d50202d0381500850301403800a235550030a00d40b0400a00ca00c07a812504100004080b406050b446040e2407025841f0b0610031540d61103c405e0400c4034050103481d8940d180d400c02c83d800030008294000c00400c2c00400d414000c89c034a0100103003003100c180d40291401484843c00314400c030f500b804620301400f681070b060350450030301e1303104e281d03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 515879838 1250 515878588 515878591
    0x7020a060510121401021308031236010e010f0b09070906050d0c0c0b07030f0c0801060e0409060b06040b04080105090a1e020d0204060b09010909020901020307081e031302010e1206 79
    0x1c04560010409003501c4d1002e40403076002c00c03411000da0641513a12004190b0304d80c01030081d40100c94622001c100c003106000004042141c007030b180100d5078142c0f00c407103043c0c040301864090306566840d0301d8004030b0f810a00031698170401c180710001d20604890107202c50a00000c000d50200303c9814002c2c08016002000c0c6c0e1401003050400085065880b241039a040d001102c02400d81d05012040010444c1d03da00300c4442d0203010b0800348105110301400f031364510003e00800c40070075031011a440c9036081aa01c0b02841900a090224040e40c03154089085980141c1120004401c002000d00c400300d001d00665400800c00c400800c4c5140c0e5030384500c2c0e081c105001000c0b040c002210385003011365a40180c28012150028010000281d8400c00c802207980b1180c005800300e8214000005e0b6a4014800e4699050f4180c001d18500561580e6204141e403103122247e441003e4201415044c4142d030014510072410a022041032504d1800054220714a0154103481a20140c003400358000c808180c0c0c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 515881088 1250 515879838 515879843
    0xe010b03071e180b0f01030504120f0314010326070c03020906031c020c031b0a0603050912070b100e040f03120e1b01111615050c0607020a06051012 65
    0x208464003000550301494402c2d0ba000440154980100120b0f43c1c5181d4001a2004030441c0c409800301a00b070700550948400b01c070080e240d40e402010281c0ca841c01045c000c0c0c004150703450005a0307042c000361903180c2c030340c1c003030300280c50b125000c513184032140f5039052403180f602d020f1141c000c2c14040e0a40d10746a0039110342c00002d00a20803400401c00c0d41e02c00f08102c1d40b6003604c2d03e02104c280c1d445081d00030350f66010020079510038411540740006000e0f150f41000c00d5010003400e150025820b10605a001c0e00000d080021141b0841c00c00340080400140904111480745001c82e0703c0341401100c140384580207400042c5003105503420301002511290031a850241d05082241d44404c12403060f800800421500c504540a0f40aa9038241550b01c0c00468188100341c940b1500d400b013206c496540c507107103031401200141c0100000d010b0504c04400701904c42d0101e1901514205240c1d40c00d5041820590b4510f025901c100741c201c0c1000841d00845510144030a0455241e526010781c8400d42206000701 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 515882338 1250 515881088 515881109
    0x90303180f0714010302070f060b13021804320718051003050702070b0f03340e060d061d0603030a02070302090a0b12060a0c03050f280509030703030e010b0307 70
    0x589804c0c2d02035016501c0c555040140103015034a1801c1c4030707002d0301c10714880500c07429000b0441d89141e03110b88246c40421003005a200034034400c1c8400e00009101c03008100f42c42d00c945501450a4052070180d040003450107128203c214244940081c006e4031851645984035410342d0410320035070303c072a0740540480b01e4600c1c0108803130300e5080081c2e09040982d040612015400100000000300182c002c60003207034104560300c0c8039004d000180c0701e12103401d5400291080d800038080301a600c14251101c40c104010240343c51b03d400203421000703c0b0030503032250500540c1c035a442c0101110700700c940d40e8001002d4019524145501c82c009440c9c44e402c0c00020b06c1030412801041045d602a0300040d080040134229400000034200ca16039a1442203492031507c40c1480c12014425129005036401048600c0c1c540c19070f07854000601200d405942c880e58a01c000360300300c403078042d0302074000c1d180140d520380091580e400a605009007038454074030009010780c0c1820110b02942e200090140200c4228a01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 515883588 1250 515882338 515882369
    0x9030c0209072c0f0a060c3f110c030303010b0a020703050a050f210d02070f02030a140c0108010b040504020a0c08030405030307120c09031b0e090303180f07 69
    0x1c00d4801c074986100c0782e200920420810301441c2400303d405401d1a40889800824482075010815443d20a0003030100140504544034000740425141e115810110b10b40d0141c3c580011810a81502241030144511061f54004c00e0680d81c0140065680c032918101500725007842001103581c7c0e210601c118180d2150000f40710260324801c0c0502c5014692000985949504600709140c1c0c034458103055911700d0068488208a10544d080c3e651700f04405400501d040ca00c2c0010510000c0d040400c094a2658001c445940160703018001d48081d00d1245021038207074144003254a103422142441d06052010110040c4080c80507001075604a4908071170240e80c5140038001200c2c02014607000400d0f042d4003000b800208000807002d103101c0e0030180daa006051460b00a4801682d114218490115040200c01e2001c0f400c044201b1034002d021401c40741c2d1031940e61202e505403110031a403007409904080305004224170f0440014401c02181ca00524229082681e440d0f02c4007500c0c441c50243c11031a18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 515884838 1250 515883588 515883601
    0xd0b0907050306090109110102060129042d060302090102070e0c28030506010507150908040f0305010207052b0809210a0306051f11010b060f19020109030c0209 70
    0x300c06405003001070240c6801d030078440d25882c080d0054490444406903a4251801b0725403000485904940b070151040a0040d13074850b1050302013000414580c0510700800001c1074014282044550f00303000601c00b6106c00a407071043c40c0d00c0803801d0f0052020035004000e162210380c0d000429405a441000782032000752201e1000d00b4551240300c0d00c03254400f0b0b0340500c2000c4004070041d1101000303501c0c2c0341031005541703080044a261145000040034801b00c0d800341c02d081ea00590000e0001842089064501078403060741a9260340a07600483da10b03900040c411f07040200c2403046890307000205004208000c48140b031103100c0c01d4004404030030400c000700045e224100400c000d441d150354180070141c140710720044540c030070391004500c400440d080c92800a002d080040d00d060504448122800c03010100c22170444020710a203241c0c0e400340d92503000021455031440028102844104202e9988a0b00300410054080d03145211000350b914200403003001c02d4201e0078010049074100c40d0301c05660b0b43d00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 515886088 1250 515884838 515884843
    0xc12180909012309010b010203130b09010c0212010c021203010e07050d11041d06180a0f0608070b0a230f0703052802010f022a0a0605071e08060d0b09 66
    0x3228660a5144005014410340d0f40720342090301070740b80c90009200008a0b00010390303403403180718009000440602d40800c200c9002102030042000b05240641a03054070760001480b00c1081650540d03242d54415085155a8041050700750892610041c0b6065616000e1003030002000207000e0b00034131800280c1188a44015072000031000340d10b41ca030315203c944401d0207038080007030340c41c84208032000710001c00c480b407400c000c5101c090304618401c2103166641070601c0b8091710040421074415515a40701080c201000d0282101803c1c034610020b86031a145070303008054a0311041c0310031031400e0002c0c000302221111000c0b500103484144281e540e0710f0345440c1c202e9051041c05200402c140c0c80c021100c1000d02401005d04880d01a80d0082c0a410804240070003284100485000c0d03804144a0305d00356500254401c8200084180a0b9608402107441d1001580d00440380b00002034406c03450079045981c000c001c0c860f01207039450072150510b05940407035901290700304058080010040000c0d0000403c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 515887338 1250 515886088 515886101
    0x408010f2a12150306142403032830150506120601110c031e0106080f160905010501080403081807080a020901050f01050d020322080c1218090901 64
    0x450200501c0a1407110004210f0560001701c44e00d42c100060741024406900005010310750f55180c0503049080810b40e101d000d00044082d9401d400148122003240303005c2c01d200080c82e104031003040d40301140820018180300c103025129003d5101c986003420400140c04130500740c04600300d40091003803910403c1c60b40004442e408141e00010004e285c102d407840400c89617010320401e8a4080040010211041e241c0d048841c0440c1c15910110121030082004198040300050102c000580305445a003c03504040c1c02d846135010f82d500004442c4140c2c0c1d800d9190000400c01c07500308104079410200000c00c40c2c0300c00390005d4100301c0030f0004243d1850707402800e103800102420131a4200355072030a04548039000100140c9c4621500400010507080105402c542c00030141e544034501140881ca440003500060145d0070310070044d07002090302816841410b00c00c640919500ca40b190242c40c660351501340b07010f140c0d0b0030300081800010104144c0b4094094454421580103084c3d580d08500940145003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 515888588 1250 515887338 515887367
    0x415090f08090102010b0906030c04180503031003030809120a0302130806070c0b0105030a0c030b090307020a14190b0d0c020c060f0c071d07080a1d030408010f2a 71
    0x40c900810800041c1001002519401c0e0000d0154242540412440040894840e501034102d01400301c014500350f03214036859090703a50441c01e000c1a42d16100d20b150000c80d50903400322a400e400380241070300704200c160b01001500052610190115060515005500600301031580104840c44000540303200400a00780340402c0b2480c628000500400f0380740f80090a42d283c00700c940010035181008141407403880d801580406001e40745648485101d10001d01503825800b062102d41c0060713450105100043c071401c5100080704411030700b001807400301030610800e080a0220b0800a905059099039441d001140e000904155900c0c03050f401e00c0b11009680c1d038021000605181c58091850107816045040d01c101c585241d190403088245d0344801e016810704e01c100fa0002154a88500c050aa016294240206e081442014038800b80712000c5100003158201080900600354244102514400d1000042c02011502e565034156182c41c0e4041418248583c1800100c5a0045203041688503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 515889838 1250 515888588 515888603
    0x7060e18040302060601200a111201020406050306040f020307020a020f0406031407061e0905091305010203040b09010507020c13020d0213080a060605101d04060b160c05030f06041509 80
    0x40e0500e8000e44411080b145d190208080b91545285002c81001c80d05207515800018004400503455141c0030b0a03500300c0e000d9009403c24005041e0845c01e00203040104100c0d04c400c1c1c1c403424034008103c25541e10b0004211041e10500c100120640e0004600380e0458066403845e00218403040442c0c0548101d03000036000104261100c41031400010f00c0300102d5400707031b03241510000805207c81c101d48803150004000f0318010000c1c03104d480c01d01280d640010780821f007000c039003001ea0b07903650aa070412207095030400305081c104500701d8000c0c000d29500007040e10241100c8802403000030000038030f141b0b00310040c590118882ca900e41240e811520301a00d0903614a6201d652a00c47c4c41c0e5401040b04101c8260b42800400500c5007000564031440da00c00c1d841d44880c0c00070703282880b0642030b0300e50100b590081d1516000110b11440b0401030000000c440325000340240c0c58202008401400d6009a0281c0d00480168101c5800404c0280d0800d511850560401d01c6600d00742c0c000d0940e2040262111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 515891088 1250 515889838 515889841
    0x31109180402210610080601061403070912030e040e01020c07170c0405090a1209050a1809080a0507050c06071703100f06030c021507090b09030106031713090207020307060e18 77
    0x641d40020b02c1403054003941c024a8505d9115010701c1c0d1113035000c0c0300e080c010401204064400c00306000c05150301c10340314a4016101e50390394102c480310005180d400c3e004101c06100c4400390741010f018900082400030003c0d0314000103a468103690706c0351480b6051081021030313086401030009000034900403100405c1403000341001c500240e11200030400490315090008100c551382401810282c0440c2d40003401020500c0c500f8140100848201614022195070780c1c004c00001961040942040340d0f655440039201c0b1506d140480ca865040e822483c4074000500c4800000340d041102905025209011140c69468005040c1c00540d4170390018141d007402c00b6004512035038150b009102a00c00d6a0842d5110a61900b03000981c02e0180c405034000381e100c0f402484400310880003000c0c08000a4000241644e8945900300d06099944070604c00340c5d0001018000c20141060700005000075140451501d070107a40041e40e036007401c0c4104014002c44000ca65025914211200c106092407051002309 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 515892338 1250 515891088 515891149
    0x31d0f0603090601150804020307033504140a0806010909020a03080a024b033c030f040b06180a0905010501120f0b0619030302070501031109180402 65
    0xb83c140901a060380100207503400e004140c800e600b064052078020300500441811919002c00e075481c40480300b0f80080c900c41000c26008200d26880c3c1c85611107000568580e070920300310071041c0307405003031132442001101d1084c4020b84000c60b00a0466042070030010b481401d610200f2460f582c6644081d00c2d007000031811000c40c0e42c020415403944123a40309540ca5060640302614240180c5112101095040c3c40c180c91000000e10139035082046403900b01c1e07082003c4000440c80350350303c003051201200c0a040641040f10001688444030000d0300215a046203007480c042108080300500140008020001144460300e40302d1201c4000c01c2c00d0036080040b46002941c500180c011a04212401d40c80c00d0000201a0030351001c850700315070b100e40000410b40c0c09491f1981012406054554880d51020b641400d1203617024105000b036203e41c000d4a0114070b00400501200e81c0604542e007421020080c0c80d003140e603036590016580040c0e04805c5e040b0707111400441e110040d001c84402203030840d6040c0844 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 515893588 1250 515892338 515892343
    0x305040902130f03030305190e0d030515040c09080f0d050a0c0201350601020d210e1c1101230916081e15241e09070309031d0f060309 59
    0x40b03410003c6d0844d0700350040300308d10340071070b8401c060301c1c04035400c640003410b4203600c01d420694010034020700c0010404130280c0007408031241003544101040c07031302504100a0a05116191000307503000040c1078145040300014106100b6010000d0410801180380001c6a025003580440e200748502c2200e02580d03902c031030300440001050070a0808408400099030f940c4001002620000c196407040004520014030443e029107183d0b9548025480b0300100035580000c101c1802d140c0c0c4041c0b00a0580c002800d8050005030590840710026418008a2002c446a0325141c160441004160f40c1150352a81c000302c0c1484816200010428040c44001801400008110001145058030b00106403e14110540e65004540040e10b40c4811440015240411550029151414184503252141404000500d20150b4918881c2120214030070b811183c01c003844100d50018003400c0410800e00240c50141c86629051041c5d002c80003844c200c02c0913a2907221500825003801b91500d0340fa0305004000030b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 515894838 1250 515893588 515893591
    0x30a0801090b031b040b0f040c030c080f010f0501200f0304080f0318060f07060c050d1802010c06110403020a0e010e1b0a030b060c03070f0b130305040902130f03030305 74
    0x2030041d03040240e480722034038002c600384c2c11544a000010001505500511029007003440502d644010302c0c800c1106251594010081d0041302c5980000d4503009040c0d01070030340030001c0c4c045400c0400040042c40780827a2405d019060301e00c2400d0504240045e0f2401c801495512655200b8a001d1440b80300081c0384000050000d44181405980d01417100508190345e9005043c084c0303050190700d41100010f414080000e10b2440d242044092910701c1686841c02992503030403020001504c00103d42c0e25011843c810b010710248400c008039401c00041e00000c011540b00c03800505003d81e1040b0508545411600b2a402275901900c048420303075848140c42072682c42445070040307845211001404080034045070341e8841550141c2c207800d001c40c0341c0049004059810255410040030018042118020405881001e20075090340116168601c1e2006881601401c04445803070140329503400240c002c0c05460949101180050721042c2480300703c001c02c0c010350b01c01049080071400100a1503410740095 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 515896088 1250 515894838 515894849
    0x10030f0515181b0307030203150f0703060b0a0f0e1302040305010b09041a10030c03050a06060602030a2003070c0e0f1b1204030314160806240703050c030a0801 70
    0x81d041a5108110303109070305841d012203550380d0490742c41141c0401190124907843c28016044a800720784079804649405802082d04018004c82e404000e00c407601c0401c000d912032940d1030103110203450002c2c2a0341d103004603052041072014000142c901c0901c51020380c1d440000c018032101305229030301c10a600a5101740020340e455402d060402405080480354903006591050f080c1d28600042d10522005070800340c0b111900e14400e40300040810044514580514003901c064101130704980303002d0303040710169440181903402c240840004103400407440351b074071041c018003023402c1c1d41261039003030940c40792410041c8840381900740420522001161144100340c1c01c0703424032280d159502c071120319000001c018106244204aa290401112501240c000340300e0300340444e0380c0720b40318100351080134100c4d0014088030381244224000c0340e114000a41011050318404000d179600100c0300205407000c0900c0c21500c80c005001000c05100300d0490340031401000550351110401a002801c101e42840340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 515897338 1250 515896088 515896123
    0xf040f1512140d0206010612020903100605030105151e0301020c060702010e070602071203120e0a061b0302090913150501060e210d080703090c1e230910030f05 70
    0x21400b030301a0001e0120210f07110794000700142c2c5e01c1e0034001c40724500c004504d510a66020702000b80e9648041020500400010740b012a2240c1000d05040c01c6070001441070a541c600e100c600100c64550b560030046a41081c0c1220100d03c00e402d021901920070802c4000307451041104001d24a136040d880440101c8a100c1035825081c0c0d2403804a94074140b0b805800604440b05444d040068003a1a518080316185100403c12400d030340c85081c14142c0205041e02ca054449404402507042c1c518454001c0f4000e050840c280299030b170200fa00604001c210000c0840c41e102c1d9801800740c0c0348000380c00000f00150134131240d030319000000c1540b200491014058038160200000402249001008102d0590002e1040002d1201d08443e12034028050340d00b0f0603560940c00c008a80707440708a40180040034002c1c0118075036400e1144505040d0346c8041540440068040020140e25606c400f07020000c494000d0280c540d10b20802d100100342c7e100a081c040502075260400c503000c43c2c0c004101202419 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 515898588 1250 515897338 515897363
    0x506090105060c1015080a140d0c0c0312050f0706020408190f0201030c090906060e030709110415120c0c0201021e0a0201120609060b0c0d020c0f040f1512 68
    0x20300400f802901c20b0550f0315081540c01c030300c2011440e882107545d600c0010300040300e41d50f54500c150078500c2c003680c246d03034149101c8100d24040e5400c00515040d200d00740707000680d043c0d0903101c8103601682400001d003901008000428501d1041d0709480244014600060b5a40e400f40341800082d4024490002113025500e00c0911040100e02c0e000e08043c2c000700b0404004030707258011001000d240181c10140703d4002c10101d05440c0d203100f6400038105d60344941c0080901e5400b05031922804e0340c407903e0350b14240000040180c401d40203a80407500140c4d05856990140d002c08e0300d0381d50a01514190701440c142e80c00d14010741c42407400038414002e07000e031290040b00040c0c20440001080140b44d0581c40300882c1c4006503c1080a420301e1116170304001401c5440702040000e0710040d901c1200c50325800700780343d00e5008050000b9451b039102030004000d8044001d000c101807500ea031006600c80e9907078941e607400400b10f941141c8400302c2042c08031a90580c40c1c62030001409418042902d00b840c0100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 515899838 1250 515898588 515898599
    0xc050108040f0b0618090c0a051f11070302041401090b09010f0501111504120206070c0c2312031b060c07230a0c170303060f040c0e060d05060901 64
    0xd1001c0c015500010b1200604940d62200c11041c04042c28150300454148280100300703041c4030398a40a03910703003809880b1015540d010024000320030b400047c455038101803c0b554203d203904400301070a20038204000c2400900310348906000e01580061340050074a001d42d0307120300f0b002103814140c1d07081c0703401040110515428801d10342c0090107440305061115806100542c0129080d4802c5000c00c0304807095000a405041400102135a04403841c0790402e940320708182d0140b106a13448019850820300c0810b50351242135030f0183c14403c0b80a150300740d41d00c00c0740e442d41d550010450240e0141100400c0446204c00c607a596020fa8940d070240d22400c50403640401000c51031078016410941d419007091065281d490002c612a0340c1c02808091001200700354800034420300c1c141d030380101444080a07281944000c0c205440d0078507542d96400c10020020695507002121010f441c0954000440040c031020a80c0d1002d050741c2142d9010802003600e815070f85527a045944aa4810b661400d5244d0380c44 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 515901088 1250 515899838 515899847
    0x80307030513031d0402130311010e101d0a030b041a06040204182c0708010c030203040201023f1305010c020108010e0c090d0b07030c1107050d052104030c0501 70
    0x1a0000c00140b41039420034a40408666440e5108000901c010f14060004400c2e40307500c7c0c0568021074441201c5110300c0c044d982c10800707008841c0c10a941407103042d5080907009001e03040d0803000089003c0c00076298101a169a003c18001e182d0000b040551400c050511200d80c046442e005103612071003d00203050707403c1c607009507800c89202040c40f00b2a24141f62100c0301400090a502c807800039021000c11240c100d1202920045421a018101603403c1c615190b085d680b90340e08007020f040c01002400f0050340d000921044981c076121105540088404120480041c95464505540300001d410a40c0407000e800400300c0002d51400090011369420054070021411800a4003040f940e00c010030034170560120380b82d0b029041e080c0d45c1e4540198440000c0480444001c1079880190f0842005112905446030000002d03c5060800212041522241c5e4500c01070140714018600303104140b040140401a080c5141c6441300c80700f44c0c030f6a44100d1841e49030800e100586201d00d0710070307000030b255016 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 515902338 1250 515901088 515901121
    0x605030c0102030d020f130e09061f060309061b0f1b0b010e040305090301020a0305060f0d021509040f0c080912030f0106050714060a05090114060d0b130b01030803070305 75
    0x180c003d10300704038584894030001d40040444480000301081000314001c22200010041c1054601d0301300319060003c2c0716458103034014400707541c0880003240240c40c0ca04541065085440714a8040b903000201d142030740182c03c18251038015403030b21500b243c980343e801500d010903101d1142d84210306240003051201e11a030318200007600452410700148035290403016982d40c86070080c18043c0c60700f00f4480c042422a4030080e034802c006a580d00031700c2102d1400034041d55038900c00300d82c0c000b030551098001904000b0303801003652000b000058042e055455036084004500703500ca00400c200090588003130a014822121140c16001e20303500c1e0300c018150001130324000d10b010855003a150703003400f0303090ba89035019600646d40d40340c1c14071440422210802c4aa0b1281440e018007059038140040d00300d0a5074000032003202400400400c00c5580d4441150ba944082d4008000c0e10b0f1a031103649502410403450207011380070154079400441032085400081d40101410b607000c21a640d9007400541140c5003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 515903588 1250 515902338 515902363
    0x150e0c03101a2403010b0306041107050d0503060a050a080d031b0c11150310060e030706050d180b07030e070501170403081005060705151b040905041a0708060301060503 74
    0x640004204950818407403c9a0280000020b14103640c07080400711801d400c264050121118000f0400025080c6405076400c80d2440e400740ca82071200554415442e24132221a140400002000003600c3d0340d5041e542c07400410b4040d00b455075803600c1d000116240c0310030080036800b003400d110301540190080724049689441036a40d84209103644c0d91000c0549a42040c3c46500c45880c41848040302d00385c000a40c055540c0c90341613052a4640100600840020000d89109402000f070401c645900101201d03400c600c1c6075030011b078031074031a5600034a80e045600003405881c541010002680d4040c0d1102c0321100090b0300322a050b036611030045842c17603401041010810002c1300424006401a0040d9820020502d001480c080d241c0001c501c0540200d4400d0300c0c10781c001c40e070444101c28031a100316000a110050070a130060720821401403482240b042d41d00310f48e560380c005010f0040038103129490750410700c510b10060411820040c80281d0540300c0c94801d51078800d0010351481c0001d200c0d80c86c0340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 515904838 1250 515903588 515903621
    0x60b091c02060f03090a06060e060a0f080c040f0e030301032009190b010201200d0f0e030304030f020102040b0f091239030609031207020109150504150e0c0310 70
    0x4680ca03180c00f00d40c0000e0b09805091007094040b900244031401240c0140800402c40001854254100440c00c20365034003010511840c5101403148190101c0c0640f041d410580300070079002c0780d11039108000c0400c03480c000710502010001104119204050046480f4203c45007860115010304010324030200b50f402c0003078848404010610158a50840200450140000664010418410307800c100c00c004240e600141c00040c0d480c4514114403960720f80812038074007001841c3c0b40d19851a070307d04c000743c03014082c40407006a0300e18961007501101d010f014245441ca407106c01c0d00002080795000304a810740300b060540d00c1c81c05508000120b065545502c030120740c081480b0300543c8800303018491400c12080ca18259098083d272420007000d801070f00554015581c4044050381e00c0c0317005001400340c004590400d407441b40440e50820b1891100c4540e01d9000030144c88038a03081ca240f0b003112034003400c030b142000d0031900d09100c0483d400c44a10030581c1510820110840c100d001c54904540b09410368 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 515906088 1250 515904838 515904847
    0x17070503100b09070f030b030703060c1d0a030b19020409060501110102030411040e070905090a230705012d020703050f070302011b030509060c01090203070f0e0a1509060b091c0206 79
    0x142c0c82202171078200d00c0c0c14100000c014421034046401c2c0760603904151420758030f0381c030341000e07040d4060315195120211002c0300d00c100ba115400a401e401552001600462901c0d001c21008406d4040119032500d01010840d5141c2d0f0358440d28002e0702e042d116007800b044003c442000c00c80c81c10300840340b045a101c0154a0a1204001001b0003007c00c9150301e4118401d800010503503034141d1140723900840640000b00000b0180b4504034a4480e41c440010840600d540d086070004030000a0b100300340c07902420108a2005007640c0909a14042e00000122404a144c0241c007180c001c00c0f02010b6a010f03600350b42580f000c4111650795094980300c000d000441d44261020030b101c221050340c12a0348a40381103441c0c01036607800940150480e00200da244d075500d860140440c40c0420542c3e000703080301c0d8903011000c0c1c9045030000095400600b04030003a41c4621f4078404003855034401001a20700400100403127500c2e00e80408590b00207808503802094402d2480301c15807403010032036040580c0101140d260 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 515907338 1250 515906088 515906101
    0x80109110d240f020c0a1103011e0207051c0804060614220b03151503010b0105091e0907050a09170307020111030f0f0a02101413030917070503100b09 66
    0x2440c0c9103a150398880c5664410210300384200d80010446000750030004e1006c183d00d41440059070382c000310814803e82c03402540c0502086171002071841c109440030016180c1220303080440c01c088809600355032025040040326642a00411614080c42c002c030002c02606480d10f0700078440c0155540815400a48030700715052400c001c041c00c54001d400c400001c10182200c10100c2c0c508480c8201440681c0d5014040002c401d005481284042034100d000b448604203060000e03000340b20f8440324502400c0780800a1700c9201380801d9096140e02d000e080d400701e51400c504000c2c02a000051180c0c0020f12031000040c1098220304502d600c4e440e55805545030240550055408200000081106020610200300030800f010046c10b40080d01112039940d85040900c001e051240200b40300c084c10f45000c040450081250198641c00300b20304550a1041c08103050541e00c01000313030702004189144101f00742000c08081504030850b0410b90880d516850b03440c1c161001c1c2d800c0200303078941248180000905 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 515908588 1250 515907338 515907383
    0x60e0c180c070507030b0a06150309020a170a020d0b0a0e07051018230907022b020c030102131508040f1704151722080a031401080109110d 61
    0x2e05610071012191202d0b500da8824100200031290644c1903507a130141003103128103c90035040c0e907544901d400c111078220f0b903002802003002d901071440035001a50030902529010004000195001814074403025035603c0c288d00e10402c00c680464000f03050900c9005c0000300050458103031800100207100c0e440c0c00d5801156240c010014102c940240240700141050a44541403001c04174040154448003c050a00000781c0016018400315440b5107800300340d000380042900702c480010181c0d2214524822000c9103006140e01e00183e140d4400034202c03503144100744085044030060f404804500b40c1850069621400454020305003080040842d400204042c08031514401c445002900b403c1e102c1d071260642d00350714800280401d440044c4545c424031101c90305940007440c819810103042c0060040c00840002c0030b001405807401090002001d80641c0146a03401f0140140222948e90b031500c40740070b03220702082074521020840e10700c60141041400085810b421400b052500ca1000d0403040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 515909838 1250 515908588 515908597
    0x90b03030706020f070f05151b03130303020f0d050426030a05071803120809030301140411040909050a030e06071e020111100c080c04030c05010c1707060e0c180c 71
    0x10131503141040142e002807128180228180e000318020b042143e20103401d28400302c00035040d81001d03e40e0405d00c03d001d4a07808101e0f40d12600541d04007820a00c0f52909030040c0c01064444107080c0800710702c60308240c03000d500140c4124000c7c20030f810165020012940c001c1c1615070001441d01d010030000311000c07441e420064100d1454940204c4101244413000619541c6400456030720304040008594545c0c88a44190000d00260107585194540034843c80d80d00380104071940915200c8285480400c4030b00240e900800822400380318045140c900951038018142d0100c0c00f09240c00705000d02c03410400141d511495000b00d0822a181084483c0300d6842c00d00704049040000311074000080c9001404480142d4103020000300341c400d000324018041d10070041641c5071801047c0010030120700c030581e0342c03400c071482800c000f2894401c0d424094840d80100600c0152141c3c00030300c80381080101c0c0e0040c1c5100400c0c038151000d104040c010042c8038161813000b01100b001040208000b40302c00340c001e2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 515911088 1250 515909838 515909857
    0x3030402010c1b0605070323030a0c051c02091201510503010c050c06070f0c0512040302130527030702040e06070206010807030309090b0f1903020109090b0303070602 73
    0xf04001095403c0540c081031141c2c029500055002c9801c804064000011121341c00381440c140d807021040d400c2114075070100800844c00e2940320b0915030281130003001210108512154403910300c000040441000c0c4d0301c821070003409034510342101411041c044c030402c2d1000150124010445241c0e034081aa100d60350340d8544144803000015000f206400c590041c4401c00322189525103510706000c01d403c5a0907508810103001081003606e9203400b0206101e40d1040c070070b080000840d100c0d04070445617410303807900042680c45030314803400060341c50001900c01ca0340700b03d540200501c03806109505480c0181d900c034001c0c0030401240c0c0595400140034241801000c022a420040c0a0f00020207803188105107150363342091003070002c615414024607024007000c4004040f00c0e840e40d40e004000245510031807203c181e4603901c20415542c1e400c0300d4242c1050042c01440325400c0c020848292036030511049010409140380000d00b0001401007000141d4000d001d50f043c41e01c41d0722707150040c0d4002c040360b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 515912338 1250 515911088 515911103
    0xf060f040609031e0c020f0d0f060203040c05090103060603060f1e320603010606020a3309120f030608070e040204060905090609251710022b0c0203030402010c 70
    0x3c2e5440d076804c59403e0318401c0c0b40c0d65614030705050705005200703481903107102c1c0e54016212680c150010605c00500c4030640c5034003c800580e2035a82c1d08003003101d000f10b5084141d0152040340000180301442c7c0010060340e01481c410090540d03103048840441e12a11511044800d80001c01d041500c0e4650202002c000b10320b511110002841c0b82c0802c2c010710041c0b0b241c1900b82110140031a900302480780c00c020300f41d1800140000310785619120302900380d140d500452141c403201c6000d484480d0040c0703800120400b42e0144030101070341ca000b400c124504c040c0b00000401c90700c441196680700740141811164901c002e45081402c3c41030307804004100601c103070307005900e072040064200c8541c41150300c12803c54016001034145214414141441141c00c40d80a005280c4146c41e8400950123203022295601d40c0c2000703184c081c544580c202a000034022410758800300c1d554030304852000d9040c1d50f00e401026050101414015180704690007002614010b83c802c3c000680154007a4541d944000d02030086c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 515913588 1250 515912338 515912357
    0x3060503010203240402070804180212100302120c011e090b0d0507120b100804050115090b0a08280512030901020909010b09010206070e060705011d0f060f04060903 72
    0x2080c2a43d0040e5001c1010f2112001407100e25030680007141821241250103510b031406d10344480304180124040c01c007070360220300d20692050400d503046074400804e00c06062001e14008051907000070076403205238042c03004680b4201c2c03003180101c2d0b08442001d050315480c0002078194041c4207000300642d000010f02180c0700004c20103429030030150902c101ca5400c0401c1500c1c0010000b00141030f40c014a080d401e04200324225641e0762261001c4100ea40c41c54818040d43d1141001030142c01c0b6241500020400030308007003003080e40c68002c00c09448007a03071422a040d9451440b00c0d03480c22541d20516241d0a03d02008540340c0e25483d500715594004c0080312039aa112003408061a401a42c2411950b0b50014024000c0c0c10080d071150f00401c0d8802616081c00308813030001c0e444420040c0100200859240d40c00c0c21642c1c0d40d0107407030700b40d50018001c00c020a0b090f044100958a6480502c40360701c61500c207403446c50300000e451441211114400034442c0c82d07070381c0d0fa00080c000700d40c0101d00f404440ca8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 515914838 1250 515913588 515913599
    0x1a12041202071d010f0602161806050414160c0b01050f060c07150e0d02061e0d1103180a020d1113050c0714060601020a0f1a160201050609060a0302100306 68
    0x60842070b9181c0071800c129504e515118120050702e010398810300030740d00030320408120030710190308040c1141c040890b1b00507016202c001c0d140c02450340d9000725a01c9440c3c07000c44521041c02094192084403490000465005c1d14541a074950440c004010085d002c450014001810903443e2020000c1020b00203900780400d2825490814140f600301040402e181c030580103103150b000c01c415007003090548032904d1249a58000c00c000d449040c401c110708020f5150201c42940d6658115085848070350010000e60711900500301003603109032900207030401c9500d0781c0e02182c14041961903403180e00500d0b100c000f0032503a40c0c0082c101411030040780c0c0090140d109010f2740310b4900445211b84032111056944114034a8056480007201c41901540d41c0078030300b003003001d0b6000104408401d8010070016160f081924003250341d0f98031206111040541201480305202a00c4451280444503070000c0c481a603c030300500486032811203d1592100d4030250400150a001d041074150880600d00841c0594456 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 515916088 1250 515914838 515914859
    0x12020d14030304080703090506070b01090e0715020a030305011d0f070c150c170405030a050c030904060e012306040504050a0e060435030106050f0712091a1204120207 73
    0x7100c003610058800103104041541c4102100090708d401c55180b4144186529203840c4040d050041c44600c0760344000d002c0815000300032441c02081070059100c50004142c00081d140d078001c1500310082130405001094491403440800b10102120451a025035a12b124103d00380201514650600c121581d214001c520012005040301410241c0495040420781d8000c28090510b403150158035207010034031001500110444840740083c0c545251500303085010741381980700b03000d10743e0307401407a059000525105401c40355048582e240e20a8250610b1361810200e1405031400495021508020501031403811758000c40d044112100d00190b21010703900b50301e1401405580c107885040d031b000d07492200c0110003070a403805105400c4030032650b40003201c06e0f0010703030206008d8070b8180706022454025003c1d0075400d80702c40f20f030808000003442c0384103680500000c049001b00b180d80b02c803001d41c141110710420b00320f80d00003d042a40b0710050380c541d11444000703001d14000004600544a00040f8031124 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 515917338 1250 515916088 515916091
    0x4090608031308010902030d14120907080105010605070b0a020a03060302030a030e030c01030b090112051606031a0108070210090501020f0703050d1808040e07020102090901181512020d140303 84
    0x100855aa0b25100000e56201a01d0b51007404540c4c104244140141c40108881034264520305101d0780144c280900c1c0c03070305c0707018034441102404050010010700200010300079048440d4030008200d141d880d403104171440e20505c00d01500c0340c890580440c20701549507000380307007510b0030b498001004c980f02d600013424503064a8040d400115040104440340c6400e1140480501090900300000e6221030081070440380705104030340319258003100b000240441405145a654510058040401e850714006002000d04c0041c465481c403c1c82d00200155001d205524003d200715001000c00480c90b042e10703005408216401c43c0c440d50240140c1001c02d10314405042082e01c42e803600d03504c031a94600f1442c204e0354144e0112425406420b13020003c1841f0200f218155550380c44e501c0250307600d0b982d00b680a0700c40c1c2c0e0205a0006440400001ca04290200030701080001400522000d000640d074039440b01d14900030700d0b40010459000c40c0062030807008081c038181c810341451601e18841502203017507420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 515918588 1250 515917338 515917349
    0x161418150c010b040c030204050a0b16060c080f070309081c1b02100e0d0c0b46050c1b07050a0f03150608060402040c0e0d121b120c0206040906 63
    0x442c0c490340c0c8200c1c5098085c401c110040b501d02141003d140c040061446038880c40740a0905000081c4801400060034480310034680016040c450b081c006070008082400c112510b080301c031026004038040c00e210303028058006030050314650400d103104a403c0685110341a000b2485552980408217852400494240d2085160058030600c14060004c038140c88a0002600c07558000f501540545074004003201d644942041281d54182d6440c031020030301807603004d0940308440700e080c0000440000180d050154440074400b5120660f0b010f04c041c808e844050301c2c0c4081c059014040b6406402d8510400104150301d070007140d4506a07900b01180f19900c10343c010f000101c000c92000d00900007000c0b04d00001d40180801044010300d0301000a4035800e020348020310032905c3d107901c41c0f0b20794401c02d81d29814007401024850030022070703d00002180c100404150100e14007800f90dc3c0b05441e2040c02c011407a41080d000038813404c0d043c1040340d24028408080307900c080144404101d5101a03c1000080c21 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 515919838 1250 515918588 515918591
    0xb09030d05070f0f090e0a05060d0b0c041404051005150f040801050a0c020a120302130320090703200c0111160309150509040b27161418150c01 63
    0x1007400720040a02180e4411081445840501000b003814486c00710703903111145503c002441e407200800030340c40c2148142d0160810309141c09024250f5510f4004004407056641880080c2c09444288400c0da00220742c2c0424190301904e0170019400d201510880c9003410181480c030304002d00d52410410380003508007241c142c0d075540c1040a90900c1e449042c20500c07142c002400780450300c4c1c1d07074226210f008860300002c060f00411020351074451009900040c0d03501440013080c041c464400d050004907040042403042a0035004605098028814100c0140c04204075583c3c03400354000f45e0226510010042c00151b680d0718a01001c1010540a080550711003251040742150034100102850510b800480703500400303882c805042c81d0002c4c00c41e1903d800c10398003c20039a1000300011503d000030560383c520f558202e0010340646919040861103040380e2441c04030304003114001110b1010000c0216401110208000403400708220203880720b00c0310081550f107000301e603180c600d040b030f8010541403005a03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 515921088 1250 515919838 515919857
    0x3030712020f270105070803160e040c0503041a0112021507021005041a030112060b030c0901170601093803030a031d0c01020304210c0b040e090102070507030b09030d0507 75
    0xf0180700358019144009103040e5040050f1038592520030304c800b520704402e102c81c807406188540e004d200c0031820354000400030000345217041d402034420b5008640446072034800c5000c00e061800d007600031038165038001d803100e000c0b40c89650a20004900f021a1325030201814445240140d40c0c81c1030f000004d030b0050717450360f4507149003014420758250541700c0c3d45040c00051006001c854644860300c000c141d008940840e00151a5010904200440d500c05400032020130001c5507a8041111440324018a80111200c503039076110100100c488441140c0075a07100c04c0c000d540300c03c0d4620703401c60701c05100c0c1020400f0480c440300000e20b90fa114500410100b510340450000180000800c10304100d20a80904552054080002d49a20680c0030341c480310a2030f80100d80e11482440e040b9030501e6401126143c0362030311580c1c021865000b500c201d14a1885600000301840818002d9584290380000284031280c1995105455560014075043d0303144018040354910700c0007030003240e005270a15103809156 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 515922338 1250 515921088 515921137
    0xe0105060f27030609150610211e0207051504051504120f1b200402041d010506160f0317040605101202011202030a0b0d0c08100e03030712020f 63
    0x3d2084c001e22040d1190070140140803000e60b101c01d4140d002008841c002070122a4035401d80c0d00303488001c40321001c02c180c4503003820400e01c2c583c4080018038103601400d904441c098002d2003a0f2081c807500400ea40c01021102c0180e80d103255600c0c0e0402d2107441551954610004043e50b1580100c3d4280d846d40715104400702d9039600840c2485500c4118079101c0d843c014054110005d83d080000c001b86800074a602c820502c42640e01c05c0000003800820665541c0d03911402d4611242003020101c40b0440c101d000000c651505c142101d960403003442c041103d00602d6240c1111031110b0100990501c0b100e115640890507900c031f00ca5100b14442c0000140c2810f12050709125142c25800c070120b070000c031514190260f070301320b04c500503400a2034101603981d17a52100340c84080c00f00d4109280d0400000d40002040141011100007507582002c00c440101540101145c2170f1a2072a84100c40d40d04104042044240710341d1440c10381e031010705c10140c503201d800e0b10741c500160703c240e0101e00c41c5168003442c42c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 515923588 1250 515922338 515922343
    0x3010204031e0218222a09060602030301060f1116030b0f0a0b061804090c0303090602010513080406050306031e010209030f0f190f06020f0405040c03060e0105060f2703 74
    0x15503015691052080b0300c0d001605c0300034422011340340307040c40c968600088100513040c00c0821102541c1100b0300000350000350101103121140c01104509410040c0210f445071000040c3d904a507003913500d170380388100070040c280e070341840751003030b51120b07010b082080401caa1400c2502c41c0298070464019040e498031315405000700380c01034021085142411940c80b102e1ba01d010990b0ba078095205071020345c040000e030011700205009980107101241380c400001c181908585913204a0320a9002403101e641c55403041c5040355100d08004024810601083c05641d20600c09140d01400140c01c03910320300c014141030b004030b060890040300141c0d000150f46809050902625512070b4100d401410084140f01c80c984d03c82c2c1c80120003c2002c03588000240a110149285c090150b810110855943e2a410300c000c2a5610500a0302e005504200c02c0c0021180310744202030480c0c0d000414400d45900300740c200001079000d881c560503040301c01d00c07042c9220f100e00c2c0c0040b812034840c003000e807900301d504005050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 515924838 1250 515923588 515923609
    0x503040218060f0f0307080f010b0a06080103120302070501020d060b040f0f030b18030d0219030e0a020916020309150c0d110a0b041734030e09040203010204031e02 72
    0x4064024100a002e066210354821030050b00044071314400303c041311000700c1d240c05030640c00220389100d40344048160381010360000050000c142c8041e220b160b1108800c1c1c905880c280b000600c021103500c04000c11078400e50103440303014800ca00141c41d2030b510402d0801604c0ba1078011010b540e0000904005005000030701100501129100d6541c0c1c5195880f8201c0f002c2c8010404d07524000050b03000c0d008504140308a81c900442054119111071542100d4200701c040a102000424070700021004160800074a080c480c039401090b03c92a65a900001150700340000720000a510052180146c1035480c1f51850052a80100f0740944a004495601e13251100e80381c0c1f0101801179099245811100210b603081c40c0c1074000b40c0b20310842c0c80f189801a26040303001d40c00f002602004c503111650700c01001176414011b0301030807040900390401440a0409108141c000d010030b00b50001c0a0075401c05030f4100b9480742c001000141095034031340782d403520114600102c5006424503c289811450f0865042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 515926088 1250 515924838 515924869
    0x16150516090308280305040c05090c07111203040621060501090306020903030d050117150907051c12050a110703030903021e0a08010f11090a060507061b05030402 71
    0x800a00d1100e4054658001c0340005850700c1000203001c50400501110030f5031004000d001044800010440100108030643d41261004000100000c0710710303022000318080d60741910540d10b024600d0341c3c0c100340c91201a104542008048626503407402c070a0004d000101240d803030701c05c81e0600c0030079001501e00c0c1001c12049090314100080c4510390384148440266688080f00607aa0307a00f10380041d156001e014400c0070309500305000030900c4d02902c0302c00300c01d0380383c0c0400f15071141c0c00001c03615030403605c129184800da03070081d14100564644482c881102c18019006500040e03003d80300c44100f01070507054a00454000141d020500f07600c903480f58080301080000d00b08075420340e80c0003000d0f85c00b280b1020b4807565406990708844010b1240e10102c1020051500341187e03580c420107800781c0940103031810018070701942601104803078003c8500180300102101007450400c0307410389440d002194103a13a09035440b16503403092a6004d110032a2170703265442d00e80c1c50345014410041089624041c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 515927338 1250 515926088 515926111
    0x11250203061906050301090503070210030b03060106110105100b0f07030302041203020307140a020a06030c030e0d0224010b0403020913050d020604300e120a0f03110604150908161505 80
    0x81f04c0851008402d5404199046079400d1840085403c118064180c111125902d4000c501c0005029500827900155a020110081c0203230b96070707000c520b60400f000340b04501c0e00c00404c200303480403941418014410b00e4400d090041c00c050302c5d0049801c80380241041200581e0000682c6010b00c50020100076421041a005040e0501d41c3c0d03001c241030750507610420b01410740724542c3c50744a40c044c3d0401e81132079041d5002c4441c0c403035942c2c0000390307200805040d01c04421102040c030700491400842c80340c103070fa10950500749000d2441c1d00703100203d0401840b1803403407520311000c000050010702c207080850505031700404460405050080011240501d5201e07189404800b001900803900400c07840e002c2a410240000e81240b4085240a504134220981501072072582108002c071720b81741c42010500036501c0031039a806a48406a4a01043d10701900415000f00c08055500c0c903a009818424807403009541810417800450a145844c640c0c1100e20720f0301c1e910ba00e400e405a61213440e5100660410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 515928588 1250 515927338 515927351
    0x70606030b061935030a1205010503010221040302030f04080304140405070c02012706020601080d02191b030b0c0307181a030a1508030415020111250203061906050301 73
    0x4455040804c075004000c40028541d403e14810400706414210841e46806883e51440700c0980104001c806040c0040954904400130a00741014400e4510701d170452a6021407849a0542c221341c2408001c1c0704604500c0304010050410b44481c0c040c00c001d1580b540155252070910035021801040c1d0940e07603000d02d04c4e1200b08908154411100302103d602800d080e03c40d98007041c803c030500c09503111713141d2003054007440028200c2e070700059140c12603404d4801e840900001c184d00300d803039803503010b07181d804840c00e03040c09030200e526003000840081c1d4030750106120641d6a607812101003411101601150004030030803a089070400482c1100581900005800714109010303e07106002c145500e44105030080001004074100d54084407148501c1e407000001550f4036070004c2d42d20ba1060198500e210040b03240c419200d4014001c4010880d485d01700701d42050005070800b40d28141e001e15801011800e80d100e000540c406010302405118003400b1070400f071003211850700540304a503000f14000c1e032401c003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 515929838 1250 515928588 515928599
    0xe0702011401030f1505070e0a0b090a360b1008040c180b030106170d05030f0a0209030a0f0605100f0803040e130b011d010617040215070606030b0619 66
    0x8a08505407544a68014280340007420864103005c04002c1c1008101e103401d0a200c1d080740c004c3d00d50881c142c0221080285c4944640f101d072254019480504e0b04601003401c2404070540303002030926a00703191041c601c1c00c0034100145482d0801c02180000c03407559600c413483c0b5941040140001c104103d410a0f40940c00c5c02d55138030320b10304042e1260b40840c0c803420385070701c201c81c0c5241c1051422201c010000d0090f0b64850460f500b0710649412103c546200e040c0e201a01c45002d84241ca200c0c1404039007214031a03070b4540002010354441810711343e050049455040000f0600c0c52159451400361000244030720b0314005003862450160088610040f43c54410407101900008840030307902c00c100207403c1611100c100f607100e0110034000800701c0000400101d004024503070216004041010064a40e9a8441c8169501c01d107019070035207234040c114002009420700901d000d400082e80101180fa00c022915054202d4890b500125485203110f0148201490944101071a86001c00c0006020a2410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 515931088 1250 515929838 515929871
    0x20303091509030405130c03061e0303180810050105030d030e2a06030903070b07111509121209070504020307080f10090903050d0c09060c0b10080a0c0e070201 70
    0x141c1d080c1c4034005480020701c80c00007442600e00070400641000c0803a2650703e110400341800640140001e40b61240010380d00aa4002491000c3c0341580741e84400c508544040b19294080780841c600e400c4948030001d2480303010802c0400c0d09918250008880d41880101400d00105103800d008140c184071032011074000c08920026204402d00c10030f2141c1801c1180e0b181c3c410310b00844540e102300d01204100c030030391000c4000d100c910b1090603e18440d60b6140d0003510b00c003448808a4045920007280b03c071480e80e0301ca082c25044402e11003250700241c1c410010800c01d91100100c402030160b11003d00490b02000c000b850041c0404a900350700307614000100402c072101c014000080c52640d440400c21180d40307011110042c007109082801000c5c028203001c0c1a40e809086144c09080c0742c003545030781c074510602c03803001030b204107540380c41c4050813945904400074000f50100c4011500e500000503440c0d02003080e07003031803880744c1030906545150604462840000908d03c60559040c104881c0c88607410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 515932338 1250 515931088 515931103
    0x2010e160b182e030c05040b093a03020624060a0c021905010e03060c0a031a040c08041b08030a110c0306070504090c05090303120618100e060102030309 67
    0x3161180b820001410009290040010010650344110040d03a42400d202c0c0081103c0036140341c40c1400328503920a000c8500344620712072804061018852109036207892282c04125010844814034100f502d000d60781e819494400c2c01c5000600d200c4048000c16805004d003580c489881a207026140c0404e42142a548080c0058540f26210024100071454011804911000d0700945076408660b80078001c244171034018010709000c00c0241c600da980c2032a00045c22445511030008060800351007890983c00340c003001d000c81185615841d82c402168940e440fa440d10000c4560302c061190034a07003840d4003002280c8581c1c0d00880391381181402415400000c4a07040119880c18481d04988280200e0400e0360040306203a00d40990f509109160390300c140a04261541040204090318417500c058401c3d20906807201d805400170301c03400d545000380ca1a15a0b108002805006801041f0382c114100044100e0385101256140c0e40d060200e03610395148182e03c04000e00082d4950305248841507500e052 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 515933588 1250 515932338 515932357
    0xb09030c06070c050d140d020618160605090a0302060c060402090907030c05090c12090105070e240c03090306090a0506060a181512051c020123040204060e040302010e160b 75
    0x85d60140e4020044000c480d08481c40a543c10f40e040050b406100035141d05090340c550000610300c0b0300c11306c9000404074450807214041c05650f107080b86800d0301620b45800400031180e01031990130001000d07895807402481801360a20141c012841c0c14810027002c00d07800b03424010709600050040c000a41c0340004182520800c9803446c45950354074070200554803510802840c0031803158180030122005400240c0212000d071205c6481c40300780f0050061000480d4410a00c405070b450344950a0062000282094000d8506480c500340500b00428604202a02d0148503580308042c0402440700038803141c0c0d0003210840b16082443e1604c0340017038440203102801c031105c0356241071607180450a0500400104040c0c07600c004016402e042182c0c8030a050311030741c0302e05440410004c02c8030b4818450240d00c142c80c0c81c0a0b01102c8500f00e200401c64800820480e0407580e00c980204e441c8846a038940c0c81107100368008a41c0701d00038281141401d002074100c1601c40c281500612507c0601c006640b0100d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 515934838 1250 515933588 515933599
    0x305030d0f380312040b03060d050f06042d230d180f050109120510060e0a1d0d03021e04060c0b01120f080906090a0b09030c06070c05 59
    0x9060101400411611111502d001c0c101681412064400780d070551840110380000842074500b101855140c0180604c0c040001c1c0040105000842c6180095a000a4003400d85450032141d55102c0b45410b512400a41c1e007944060100310801c0100f400e89060f000d4810110042c684041e14000e5200104e00310040c022110300d005141d04d60780d040e41101d1980080303001c880e076282d9101300c0500041e0807410880641c11002c040421501c0c501031300c19085400684d01d03003c12500d8002c241c1103001021104442a000e0048a0744840d00e96005070f801a080c044031120341420107080300d00445000611450340700b1030020502000d0b02010401a00000c1503080140e61001030141e14046a07030a030318261070420020a01060359035120301803020552103a9146485643c0303504140c10401d010890061066004c9610507002a100340e0140248500207401c1c2030070110840009500d8038100e0300314180062000c03c0700d420138a07040052840c03a8405583c141d2511001c0e803205040604280501070003030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 515936088 1250 515934838 515934851
    0x10603121b12030b030c0a0528080303100609090b2d0a0b0702100c0816080c030c010911100e0f030718050405010b090105030a0b060102190501050915010305030d 71
    0x10035501c0544140d055001001c4010890312000150050085074003150080c860120b50002c00d00341a01c0c0a001c0e40c40090410140507080841d40815003160001d113503400340d41a1001611040401c041d44c001c901945100d42e07024100302c0010300e0304074030b44d2100c40700301e040030541c0e046030b221007506190310303608400c2e04011a02d42a85603505121030b075284035002072030324200161455008002c0c24005108442e982901c040d80001103071803041d8000f000cac0030940c081060511070561030071100340c0a0300c180903450030501c2501c00e082c2190420702410320282d4646011b03c0030440e4000d81c0454200c000c6405003150600154003d041c0780d00d040161740600e840d9040c0f5503a0740c0d01044002c0003070010440011403001c0b100a5400038200642d01120507609110520300d442c500001664142c0d100a0028140d035900707600d0341080c42c0b1b40904280c0c154050392800c06050b4a00030f407010b048a000340008511401c001c4601840d04c4030314011a910010b4a00041c00022000b008480d00904c581358041500c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 515937338 1250 515936088 515936117
    0xb1e130522080f070b10120b01060c0302100e030c120c0c06070203010b0a030305180402040501080604020a0c0507082404020d032304031514040213110d090302030301051201060312 79
    0x52107548086851030f0b001240d80c80400810b1012903124200c402c030b0308400c0c80d9907084880e075040c0865100502c822000c10042c0001842100b110b05841c0c002e20448001406034071009003150390200c4121441c2d0000542c1c007118075410031141c541030164000152400000f4151542c81c1c0c5031408203a48a07a40c009101001c0d90b900350810301401100a02041d85c150362850090442d5000b54400091030807900c0e1303020030b98540792003500c0490f40b040e181c103143c1c1e550700c004100096010382d940b44144482d03902c00d0380101d48100070580c041d0565000074283c1c0313070b410703d0310f114007002072001c80341140c0300c500c00c1100580758170b80300c0a55241e01d403c200c1c4541c1d20420011161001003120840307a9140441c00109006400b03e8444c079806194204200e02da04a05084001c1002181c0c043d400444600dc03243c0444070710381c003941420340f0044210f8181f4040d6031400703080e658801410340050384048018455850004104c80b10a0703009802002960718581e11302c0483c0c0807100c0000180611000c5d41c002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 515938588 1250 515937338 515937353
    0x507020d09210c080111090310021312021305070e01090503070b0f0a110d0e090f062404081207021206070f030b010e1801060201051311040f0b1e130522 67
    0x58044c0e00000c0c080707120340d210140701507045407002c24840c1c422000201d0b101c008c03500c00c59155800403040e02c8002800c1081703078050700050450407a04501c00e5002015140c51501c0ba050040301d01d541e40340d40d48410000018607840860300000d00c250400c00041044d8150f440440f410304280201840e2201c11602043d580e00c41482d40c0c0900da401641c411180c0c40f91300162408110008494030311007900c0b40011450003140c2151901c0e0410a44651100310003400845120401030950680f4035060311449450b09000707007000503001c03c85001c11800c04515041d1080d000e220803da0051603507240c00724000300000049203401e010706541d0122002541d20510225900800151108404140c0400008508802441000019460300c400320311340300b400f4048600c6054005071514886000403040000500d0300c1c0d40040400c40d0743d90050002911039100701c0304501507021480b0350f82d075202014400381c04034a20201c410306c1d107841c00b003203444a00364600704040d08292805030003c20a1f8034200c034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 515939838 1250 515938588 515938613
    0xb03040b0403022a03060a0c0e011d060d020c0f0a05060c070c15020f070b040605040509100e012301142205041b090f0e0c0703050904020301090507020d0921 69
    0x603084030700c13901103103a01d44460225851800b09901300c801c1c5a480500910448010708a031200040200007601850341c41211a44218850941c00b000702d007c40070001511944902ca45001468010980144410050140c40c0c10400090007030a601c25982e9503454407034400624111615501207425024407015080103005442111881d03150700322103101c06581c81441400305944c030300c240500490341100100a4a00710746440c0ca8160030036040408002d4400d400038650300e400e00c00014001441c0c0804d41580f0300130407000d00d01400c26124003d54034040bc401c120514180001d0140e00742410384c410701194003c0f5111111142407060f0a0010b4100c0e001310340c4465842414071800c44807981070541a2001c0c060b440d190741a07001d645d102851040d412a02c20120301181510000e400c042e03800006281540c131070301c0d0251a1541a01c0001c08913002078229001030740c1e4032010080c6041c0c040190003821030042c01e0880d000c501d407600000c4400c015400c01010108074000321400c0020001901 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 515941088 1250 515939838 515939863
    0xf090912030103230d121e0c17070c0b0a0203070c120801080d02060405070b031909030306180b031e01020705060109090c120b010506030403050705250b040b03040b040302 75
    0xc035680c0d6540e042004200e02c448002c0704d258113200c21080714441c0001608070101c11182c582c003079060a135101c02ca00810100102081901e00601036400c180290320500c6400c850355110201980c847c0541c082404400070082800e004591000d88003280707407030301c40c1c542c04410010007694a0343c94074000c452152601c034008001400c01032000c204280c2150103603060340c00c86800c589882002110407a620b11041e5000343c02504411800d200c0c4401301c50041d039020b110303040000000c40c50500c41104640c00b143c1c0540003e80d44102c01e1141a2648010410b02c03010344d9000d000f5650208002070b107502e01852070581890310380c0070b4207080070000c2d016190031982000560380c5940c1d513440c0c2000a08462481194210803400d40071600d503121100320540c0c940c000001c00d0081e8246014001c05520160099082c441d0600104001510401441a940d08031891308160402d48082c00001e00b0519044280092814881442021504010303a907010380c0015410394191540e080c1a802e100c00c10002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 515942338 1250 515941088 515941123
    0x6080105070818071805040c031406100b04141e0d061a10050a0c02010c0c031203110903191502070308180a030c030c0624080114060f0909 61
    0x7000421078211090394403501102d404200c980c0c030000c040c0c039219081c5014114442924151968507041c0707030f510195004e84503201e000b80700c0c2e4503a1600101c0d449100d15004035940301c00100f101c2540c5400081000f0140081d1032410207003001040a40300c440c004c05240180b01e050381403c070040300505240e00280d4060801540d0082070304154001d420a04842d001c0d07101528425040c9051428110300c40300c1c066a81e60b400c01405840807140d0942c000340503810403d2004e01c0354003190015552038001c622441d0804011801d6003005420b45e030390301000f49150102072140700b1441d14045207405229811a910042900152501c01d09903000201d001081c0f910103d009001c0641103801d0900681c0c0c51108a900e11441e240034a503104d250040050000e2020b03021400001e009890905401c1e120764408125a03403d140510380407812010b40e0094101d042e002002180750038070440c20402140c1008000d10304e00900440d000156014807a8020b04103140020448001407000d030000c40340b0b9032003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 515943588 1250 515942338 515942341
    0x111203010f0302150307080103080c0102040513020324061b07030804030321090807080f0c0a030f090b03042a120803070923040b03010f0e030d0c09060801051306080105 74
    0x44140e01da914074007080f40a40080c036428041c20316408156031103000642c0c1d45208984c21907440101603000503074200c1d03140d9020321000ca0fa554400c0c0c941580d11000b00c00060f200d1504820425024854000840320030a00b0a6002d045480791000c40d0003450148412150505420741450318000740b99002400040000c1804000c059001c8492401c001f0400c204001880f178075402103040325070182c0028030191040040308009141500540341c44605000903900b41009125454103140c5940740c1100028146d556000686030807030791a8020789040800f46007145065912042c004070311298655581e9900c0d0116500b003000151040d0203083c144481096001c0359180038519500140c540d040401c00381900801d040080c402c43c0c1c42c012029410f071480310400365041c44000c1c0b1040c200c40e9015503e861802d100030075240a0910301f100790000a50350344c51240070680c202c0c0e50070600c0c6010024180e80401c021a0310101c205d0655500f226101c1a441d0380c11600d500402245d440220b45508040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 515944838 1250 515943588 515943599
    0x50d03200c0d0615050a061b150f0507260a0e072301020d0c1115160f1104060f030339050c040615120204170318090606070311120301 59
    0xc10000c10340c0c680040b8002c4d400e44900c104545124075001c0c24001a02211600c12024109440c4c0c5000d2030007901882c480801e10902c0006442c009800c050107241c58a0034058880d034030426900750b00f0500d000000084001754005050800040d01c02d6125680700c400f1058515014031040d001070154000c0c4417003200c054407110075101d40079910f0b0b9015006070030030508181d0003003503038981240d440034a9102c2c50070007204014036007408005012003c44144158180e010701e866914460300d0054218600744020ba04c3c10681081502030b0190299081c010100300710760000c0c84140a407076260402c1140c4240f050f0030340c0c094040302904062203003880c0603140494620604080d2419009200703a51032804100148010b070b81144c8111a002001c40380704d46035043c420342125405400e409005403500b039480b45024640c4040c5203c680b181d400c0001d1380c03141c1c1801c00616422049003601c8104031407816200050703e5000d0380d000074060108a2a0001c031038281481800c188642c0e03881c0d82900c07945c541 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 515946088 1250 515944838 515944841
    0x31207060b120102130f050d12030e010e01020a0320160f17030708010602150c16020117151806180606120708101d06040c090801050a15050d03200c0d06 67
    0x1b4490f12003003071484200417465040c09008502101d4001c4107420403180018402c070004c0c0500020080a95640c812580e04010300380020aa9408580e070086000810085d0840300c1c0c20041d85050b05560080012058106814805411141c0c000750b80580400d1a0304028000318040d20942c1404100001080003154101c201c1e5816201150700701ca044200c00c1d407070702e24040816280c8800346c05050010743c4841103d41c034140d812a2061402c00c008180501169550030800e5600001490f0801042409810141c000b41050719520858241c2410f0410100e0302d6036400c0540d0041d0b800800c0000b035519200e54045642e0030f0135100880e0814500030f4001440c2100a0350322800c0060f6000300001e03100d0b4030204c00d440f4180401d036000040d865807010440201680c005401c1400788001c40040c468000703201c0c1c2441000c1542c400f1030747d445443c80d207070304000750340d0491403240c281030540c600407035840307202c0c032140284902000080204101d0030382d28050304603c069030b2107001e2550340410811503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 515947338 1250 515946088 515946127
    0xb0408070f0501031806180206040e1614040e13020d03020106080d0203070c0b0d11040905040c150206240d031115010303050f030a020d0614030c031207060b120102 72
    0x1c0d0350040401c16150001101a500020304083c041d551402008012442d1a48261151241100440350140e55a0b0108080360002c2c0e1051001c0544c80b41044003140e0b6141121011000c2c520384903103c07075100c8444c14002d00550140c1d80300b0014110000302c158815000c40b100d6150010080e5a0b11002803500902914850043e51070600403e100210304900010035a4601c9034841001030015082541072072298002510705038000751181e0410440040305401400600400000030443e4a003508201e0312021179603000151000d10f86003074109807540800e000c0e0700950a000142e050030700d104084419640140e51a0340d1013401c1c810b0040406401c03160303285442c01440161488040030289200146200b48000f40110f1400c002e4010141844e0307004503489070328494010704081d00b2004000031118150020007041c894609840d8143c9403c0000c541d03489070450082014586841b00c5103401d014481004007007c1d151010701d0210341d035400074030800541030703c001c40d00c42000c1034501403908203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 515948588 1250 515947338 515947349
    0x1107080f0310090e071403011503050a0b090d0f030e10020c0304090b030304050108060d05160b0a0210060f0510020718061d070c030c020f09011818050a03180b040807 73
    0x42c010700020301800030f0062400340a081e8000c3c1088900d00130481e101c40030202d0405503d95aa02140342401100300445c0c40a50300400080000300f0441c0381003812a4070191040205512203440b582d40d403540002d0702c02c444062072078041502d49410382110b00e859940340ca4048101c7c008078007179141180001c098001c0f910000000c0c000f4010780e00c00d05450388140e028203070019840000044c0070b828480d01c101c01c524400c1007112440180d025100410b5141c682020028860016568800d240d0400030030540c0810f945040103072501e8018821613441561041c039010300c1001c203100c02c1c80780c028407a101c020040b100038011581d079040610310003002d00b401603c500b550142002036510402120f86031003440a40c59002c0208015141a600903200c0c1000721392012404054840e607031158602c1600034000001000504007101440c00240c0c1e070110707201c00304449840d65140104000103060f0b95625007506105c90714030040382c01c0541400694015440551002400040b01c1c480000d51408841 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 515949838 1250 515948588 515948611
    0x1c0b0c03071b02151b030441130608070e090111190c08071a160309021c050312013b16030b0324010605030c0d1107080f03 54
    0x92188044400710542c888020750000480600c1d0301d0310701c5041d40204003840d88404240004000703403644619552007034000c0603c1b9491904019400c21031402d034403c2407410210f03101c43c060a180306100c141e02c802c1d1401d91080021340c80ba00f103088492350100004d0801442600c902a88030012001c0300c4000b81c80c020040d628010070900402407000a0b114003150b600203035400c010b0b011000300c480e680c1c603c038140d0719404100110f5001984074170a03080d5081c51034500521a141140302c4118103950b4030301c40b030213050401c0c2100780160b40e0f0f20790307400904642d03e800c1051a45a81001c2c0d03d94050600c10701c0f00c8003020000801e0003000000c5c0b83c05101141c101c3d1100761804511b43c80c80015000009565011500d408503080300c410103582080a101842c0009090410100003850070790b1040780080e003201031030924500c0801309110217001d009a428450324605028050001034031510500b0100320350303241e441407203001c041c2c0100c43d0182d070804452602c5114400c0c8041c0a035206607100178068 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 515951088 1250 515949838 515949857
    0x1f0f1503140a0302060a0c120504120e03070524090409030507060f021608090f10090914040f02100201140408030a0c0305060609151e04080d0305060a051c0b0c0307 72
    0x7a100020341212195040d40038110341e481d01800000640720080105c07050101d440680c02941c4014491148607500500c0ca00f0804d0862800282002c071044128a00a4203d410140030a071220400c060242c4503281002c5060f00364201e942549000d0b882c1d42580c058248242e0406150307001003d040040c0c06402e04003e8940302c15001700c2244510391070003415400c0031035203070045076009000c0d0548060291030391031002000000114a44155400c142c040380d100701c014007000a5a1051446c400e8904220215904140d265070340900410580288a600700c2681040410310030340207982080c118501d004e02030308061401003070070f030021650060710324a00010341c84068401c3c090540203500180c1101c0c6400002d5044c400309031104920810f0030441046060080707d44046140d00202404001e603841d6400c1c03000e054103000250401030704150402081c0245a90b4010301402107a200301e46000c40c031950011024009003980c0005000a401141000300001d0a080154030800381a81c841188 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 515952338 1250 515951088 515951123
    0x60306050102060717060919050c0a0908010504080f0322060203240f0103020a020f0f100b090f06040203070e040207201203030f07090f03061a060c1f0f1503 69
    0x140154035241c180281410011900d00d00f04030b481a90000713103c0f01072400d007107230445605060342e10541d0415018800000ca000f07401d58491240005441c0b0f1030000d111504140d160176405005030754a070315032540c2c0080421040c4840e19000181e803083c3c2111140541d003141440402074004441c0c0c80780d403564000c1010f03d01c24180d240f140c4443d0300102000318a840e1307100114025000b0015a9007503105141c44030304800c40070480e00c1200005c810081800181e280088002d5070040c04540e0b00038180c1005202485405202203a4045801c2d00c00684036590030340205e400c29400070304540c01510002d203442c1406080d1810b2907a0f070034100b22010954a046050084244400e60180d407650014808107000c0d004a494543d003000d2036203401e00c10b1a8503840e1071404000a40e008590050b03445c400c0c00b95800d000c7c468800318120480c1d2050504001c030082c181c4840030b070074040d12480d50150801031031100c0f950090005400c41c4004000c184020604000c44940e01c0c007003503d09014540c6038010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 515953588 1250 515952338 515952347
    0x503120406170103030f11010617100609020c0d0c020f06030a090606171b1809030301080f010606120b0406230901050603060604060c030519050910030b06160f020a0603060501020607 80
    0x100d0750305651b000b0701e4082d42c1c1811a0f03480078400602442d5521180009900c9003100c0300c9040828817200070b0000e48204280030300849240341d108107042801808501100300004c900102d031082c3c1810018003001d4140700040a03e03205c030b42120790148011050020254096100b1100188500c904002054903544880c1c000d00c0d4120b0403000d09d80c0810740c4d51003824000131094000d040302800f603030b0200e607204c44880e4400d901240c010809900c04401003103040410000b0a1304041140000c01205080c03003c001c007003848045800394080c0d103d4010904946591340410000c01d62441c50021100b298060f2141032203103030441511407800900049184c0c41d004084070f0280d54000c0119150500d0b03c4019660800c0340c1c0340a40600106006401d40d40070010000043c0801998a0310369410344202004102d8140e140301104161501200010648a820480301c1203007080303d52041d020085c0c644110f500d500c01c80020b4000c0e061060000c2e101e80c05800250a48809070241ca449507680542243e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 515954838 1250 515953588 515953591
    0x60e0a0c0903080409020d0618091b0b03070305180d020f1b0d020d08040b21130b0a0506030109140d0207061b0b0402040e0102031e01150503010902090a050312040617 73
    0x180f5100d4100f00030484201c00f50f0081400e0340b4800008a96aaa6000d4a24040c1294a0001c141a88031004c440070003520481811702c5d8804e8004118855050801c9995640002000301007490b41e10401b284030002180c80b21241031202104560a06a01c0d5030000e4607800310030b01d100c2c0a4452918094445840e440e460000c8000c09401c412070340c48650208160007103429410f45100c4c104120214001c1d10300c00041c59070741e540310828400d04000020788501c800c402480612200b94000340e040c0040c040001280d0170801940e0003080070b850345400640105240c10004101d140700f0022010001004145059050f50036029120740350f03a035440a8541555030003d14070f094603451000702c00030b00103140103030300a40058800146844840c584a003268001d440f515010070402c0e01005080c0e4840400324054103d004010806024503c8c000d00070340018012940301d19004283d0590ba5164041d00030024132008044440104960381002c0d0b00358400c0c014030000034504c070400a01e2110641c03d05 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 515956088 1250 515954838 515954843
    0xf02040518100c14030f01030c09180b0901060f1d060418060207061d0303060f100f11150103031206140105070602130302100f0323040b041401060e0a0c0903 69
    0x303051024070282c1c0040200b4075070102c1d400344400b8083c081c8607001e018000d5840307035a40c0c543d6100c1c1941103050640c400f103c107602c0001d0190a0006080c1410744043c5000303102d85d448080801c0759141d05884d2030161006030011007410324400000910b440c8a1780103600d01002c0c42c040340c2241d84550003480151a03040285044043c040c0000800294865008015803800741100191406c114004000802a54000c41d8556030009c800c1c41924a0100f9032049004401c54035620001c1800b000507104240c4080e05006101c01c0b80360070a0201c02c240002d070580710781840300103034540e101d10b00900442c000507803000b03c0030b28101c008141054510389001d01480705860301401d04085136a180003035400b2040344010b100c1e40da580000140c42d0700300308501103080c3c0d03200c0c481802d607440801002c4684407800c01d001004070f00300c1c96402c1c036100207450343c0090700100110001d44e241d061241e1134010005014105629003c40091111030807403405028a040700c5c8240030101c88140221110040c60002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 515957338 1250 515956088 515956093
    0x90f06030a020d18020315041b090f0c09062102040b031321080f0601050c120d110f0d090812070914010f090e130807050a030801050315070c02040f05040f02040518 72
    0x74074951010390400a580035100e2704004031b1512407800640b00040190f401007001c40c0d00d640508400768405e0003861003280692400c0415a0300d403440041c010703179482c8845651545a075114404044594040318064000c10102c0c0d80e981c00e1120601307050392690841900c0e0030800c4e503a501002c1c3c0803011000c0c1c11485d80e80e5100d0031601c0e0342c5c1c8852116000500a1418050208401080c0b500309029244210301c0d2040001d458a1100008406580d0000440210303c00d00700504603050300403500740c441c0c403200580f0003e070074982171400540e1441811498140b051070741c001c11040f2a031203a03c49060350460031751708010409440c0151004885460814086021188140700740c10340345030b4956010003032100084800a480d10781c00f11035844404180d803690001c0c0a25000c0c150440c2881340100000e8005200c0308180c0041550100380140030001040b1840340f21505556858105c80c0903035200950400aa05140c0762983c0c5034954440c04030b005a061400041c6d41b4145100080c0102081401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 515958588 1250 515957338 515957353
    0x8090309040513050a05071406160f06020f1902120c1e120a02010e1e0706030b06040e070809100513030507020a08031903060f060504030206090f06030a020d180203 72
    0x2000082e001c01005076039501e401c46121804500100190440c01d4000d5001d0010325040081e0b06030980307040c9550500036a010805466102240f00800b0311403a00082124030204091900c0c5010b40301c1d1481100c090f080110321115850450381104010300c4070f54007141c98500c00441a402240201c0e450788078250444003003180324041080900f00c840c030b03005013650521a40038131005115080000c4140040c0e554a511401a80c0308102d0360f881d01002401400080791002c64907641c030308460061310101501c682c07403010607851b201300b43d802600040d1603400d51442d00001c0201403034400c59854516114440c0080310400307140c03251500852460404000c601c01d81e403400d84685e406031104a1b004ac100c6800081c020300240040c11114000c005029681c0c4031600005041e1412600b041e400c11001460800c4015000745c100c4007280e074141c48035600c0700680d0340020300c14240e1401c4140c014400208100d0028202c2d4018281031000f00d50400107400c0c401800c5203692500980213406a20040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 515959838 1250 515958588 515958607
    0x31c06180c1707030605010e0a050d12090513050601120e030a1d060d0b03120f1c020c070821040f03030c0203240a1415060a0507020402070c15080903 66
    0x801a01209100d402c1609602d6400c5009a110340811140003000980d603410a2100e980c3c0b106406040410840c2c0c2c403194503060000160821107450402416102140c62907803166000e40b0707440000b4140207191000030703041041100c0c040d000844541e03000075070f0380d010700b069005103215500311620101c004601b840c1300048103441c2c000f20209445503600f00c540920a0b0381e0b48980081010307202d00e0001041d40000602818600074011f10058290b02003400002d101c00440c2066818100440c066140c4804480f5001c070001d00c50017881c005103005d5850301140407480018280d07100b441c55241048071004a031030002d50317402a4001c002d566440c840c001c001103845010640045400241511092004031150703204148440c850f0714070700d000300e40030441403002a214240544010360390840b005d28100309500000540d64000500c659804100303160003a10070003e9880c980e5018108665a1006040c05800001310f4410a1042d4032003483c0102c00d03a00ca1100f4501941c2c01d20000c50070045901c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 515961088 1250 515959838 515959841
    0x3180303130b090118211425020d050f0705190b0a050c0609060403080f040b18030c010e01020d0c0306050d030e0d0605010b2106010905090c0c0a05031c0618 69
    0xe071038443e156403141440480aa00c009840506500c110320b404015500411482c4010008500160501c405082c1c0b000d00d0260b0f4030100d03a5110144081a1031f200903403d104060201d040c54080d42140310b102449041010010b0601c030840c0c0050100c0c3c6d0365542d0780080148141d1140704a5042031441d44c02004404031003000380098400a0611604262406111a1070040d08581e04d04d4145e001000340014990420300d5540c1090040340003030240d00d0551224542c0c0b0748041c2030048402c24403001d01703042034018002d540e1024810802408401c01c03180c030f443d011b5001148041e440a140c914458642c502030303c40c400c03c40704040c1800d082c2050944003900c480c82c42c403080c40d8003ea485071050340015920704c42c09019207a005103268540d42120141051a4400100031640e0340e01c54082c0310983c1c0c2c000d00c0250480b0800c5a14140b6640c40491804c41f0340a03200054950744129001c1c6010024040050f00c200750100f40c0081e070504d001c00300385055500b40c1c811107540e480820b0300d106110855 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 515962338 1250 515961088 515961091
    0xe1504090e011b02030406080c03010f0e18010f0c1205043810090e070501092607080a02012303011401110a0b0a0b0103050402330d0203180303130b 65
    0x5140006003030803d04154000103050501d01c50010b030400181803040c2500030002941000c3c1114055041d58108005c501d885011030081202e100340075000111104c0381d124411186600c1c4200a0008410341ca4400d00a00382400944000c100720035502e035064540ba214142c400e0750044130302d0265030244e81d094104c82003007040752040c01030780001e4003011500601c0298011001c1a10200d2820720301050a0308171500c5407101883d5801030342007006580c0c2d105d0803035026103400c1c0e10904c0c951214041c004d07504100350542e020303041c01800702c00070300c2d0140420500c00e014001e0301c48401b40a00d818400340c00c4d0f0424080740d07050350002e10050040321403040001034000c4040c14180c4000034480c408500e44115140100c841403605002c0140f514850b00031220901c1c02030806000320305259000481d00c50741003c1c1c5181c05100504241c071205000030402048607405218982d4428058613054084e51045419100c0c0d4110042c5c114040034000080368800c00e0386000c9441d102d070483e030301c211b00c00d0310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 515963588 1250 515962338 515962361
    0x6060206040f0b371805061b0705060405031801020d0906140c1902040b1504090b03032b180807030305100803220b0a17040218160e150409 61
    0x700302a000701c0c41c445101c03080c0c00181d003c0b41c0c4501c01382440b40c190020360b464126101c1c50302d00d11984040014030300240da2500200c00d40d40710541e51040d4a00c11000b070281d4a00901240306040038001030080102c0200702c101c241e040c540450000281c01a6a280058184070000803d00341e402c024441c801c0b007c40b0030407041000414600602001c800d85050701d850a041045420480181c085160a00c260319001c1c3c07040e202c2c00f11140007610007802034001e922601111607162001440181e130180100c68510410102070f4251003070301a504140008240c840110740c81c90034a144089140142c403140d072940d0700c54156460310800e60740480141c00094a0008400c00019001c501c042040c009480d0340800c3c03103100294904244400c400103103003a8005500700070b00700100068260b20407800300c0b40c50703014071030203036281c0b034507c01702e45180c0c140d1401071004203841041c450088800d0108403040019652140a0349034080100304011034081911403141e01c003080200884211504440346944 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 515964838 1250 515963588 515963611
    0x81c0302070b0106030c02070f060e010c0606050a0602030a0e06040f050d060b040e030a0212091c1401091a07020105270109050609060412030501050609060927010906060206040f0b 79
    0x50709940c0703882c40150280c100c0c2000c03e440388010128903504006a5009141441100c40910304e0031401601c0c0d6190b80054a040114000c8401c042c04a40d820060003420080d1100440380e55484000791070b90005405980014950307016800c19140c854203a400791210070501d250036a14000800c00d01425a00c1c0c101c0e0400e4507403240c4070340307580c1c4ea105003039440b8a400040d695900480d540281445070f9100ea448141d9014421030b41992241081842041d10760084119007004c0e500304000b0714072100006120a60804c51902d0411020342c0c050f4142401c0c02e09003032a81c1c2c0b175864040e0309a4201b161202e01c808141e44081404041c400c501000007444a00000f5039403031161903460522608480e8441d5960100c0e05000c01c022215503032540d0a4082d00e001c01081d410b0600242c043d00c070f1150070341e11922000c500c0700c5407580c2c0c1c950252000d00040c100c01c0302411100d0b801100e01175003403040c01001860f01c2d070006012070010586c1442a40e01001c4451250256a100c984004000c0c04d80c00005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 515966088 1250 515964838 515964847
    0xf040609020a14120601030b010b0c1c0507020a0909150209060d0f0e0f0708030412170c0d02070b0a050910110303040f0209070c2001021f020403051006081c0302 71
    0x1600d07440b441801404107040404075180c3c06000344244c9181c142d4a000fa40da20601c010004950481001810f5454000d10307141e80780c20b0303c24014500250790840421807420311001d0345110b504038001b044034500c2500c0016400d642e5403a001d003240d004800c081d00d100c01000c41c4142481d413942c02440700000c020101030420409403101800c4503c080d990f60352007035640f00340c0c126441b0204008081c02c07942c0c000524502e4100003c00382c0b03e000c0c0340306642c9507460343c209a10070814401720781c03470410b04000030042e22104000c0c1c0e11070b6190016640d500c0036000380000443d20252183c225001c8481545550789050204000c1c0711000007081420020072102e206040c078242c00902c011070107030b402038a0600035a4a85d00421640356000340c4a02e0510046a0340e5000107000d00c40300c9840c4140d6420304c548200c02500050341085000000490700c08045a0f00c948518150340c003030005e40f8040c0d0111070910510304144422181140115981d80d4003d0f080f09400c0032124030b0814440c5190b01e00507040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 515967338 1250 515966088 515966093
    0x306130e03130306050a0501030201020d11330705041412070504180506060f21070302190f090b01020c0907020a0b040f11041a10051201060503061906080f040609 71
    0x256040511041c06a92500900700107120704e80c010241c02560010042046500d9075001079594034001c82c80d1000e2000d00100a9107086052004100180c100411100c0419485421070048a0f140340004a00c01404020517200da2044003a5810399100801d41032100700480c0c108400c4410f050451034291140e124040780c161200d02840b00019820000e10000340d003e49001350074060000e010f58010400c0d00c1c9128030311359030204441d1810040d20360307070005402001001810b2081c0c81c3c00107900288050380d4004c8541010340d5000440b40c50038062148952101400425114181e00c2c250040e03204604100035840c100403580d030403c1d01c500454040a59943c0c410280d0a403c071029112010f1845842c02405000c0402d4070b14024100c0b800c0040c01c41c1d240039030039400074070007115004003085441f000140b80100100c400b813070b828848402056a440f04024540d6100715159070207000c01907060b4010280907400f410540740301d43c451514583d5401c0f4203080c0c0c050001c0043c0c51481c0c40d525407101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 515968588 1250 515967338 515967343
    0x1d011407080d0c030b030706080601090501050c0a0b011517060607022106040f0201080105221a090411040e031e0f0d0e07030516030203060c0a0e06040e19110306130e 73
    0x40000044d2404a485800042094140740041c2d00c51814031500d607080061aa03800202242516024203100f500ca000b4500114913000400000030400d4600000200c0ea20420211000c46450142e54541c10101c252100b0100c401c0b06135a0b0a070400707024030004005140a8040c0000201c0222400b1078010704e00da40c4500e0300070250707401c1d00d602d0201c02281082d540d0007400240548820340d0000c00b55410f0200351101c1d5904210111905076950701401507003203004803101e64014008055075050308181c00d00b81c01c1161150104c80c0f059207031100001d0341c40d1001c4252252031000103845228900416851a126441030800d4840350004010924074418980b0441501490300c000030005503086192441c941511828240503a0080c07403401c00051b42c000a0003940107a0300c600892b1145484101550000f00b8050182d90103000400d021032031200b4608c0044c4100642c14840c1d503645000d034804000c0f140080780c2204c40c01c03010000200541000b15189010500c0d002000603c600c0d07030b1607900e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 515969838 1250 515968588 515968601
    0x215220e09060f010806070c0201050f0f0408060a1103190b0a03150f02130519170312070f1205150402190908010b010504050907110a0f031d011407080d 67
    0x50644902000e001e22120100207490380f000c003180303003440c040d4102666a07640d020000c00e60402c00c402550824210791058042c2c1e0302000614041c182c40d40349000c80301507290014000c80402e4441d81000034201e12460152101c461040f0143d9890340e228040c4485e00d1028403a1850b500a458100102041c3c450400200003140944140070444080d102008191482401400310090041c030030701440b107076010241d070210f135411950b02510384820f0740341800c00c540d00d0707022001c8112000b000301d02c001030100091202e190440c0044450795242c1105613a4810542500c10024460000100c0c418400c0c0c1e001e150840e640c542b2403a13010381000000741c1aa0302c480d6402c1020b10418100c803402c1030700701c01c0500c06840f14000a0051030b80c4a0f00081042c0201d104662280f035045001c602c660703002301d01281c00c2814400130341c2c10302c00d010b042040302c10206900071800140d03080e1050484004a640505074140140c1d0b074403101c10000204403089030003440c01600c0c0039508110519212171948900c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 515971088 1250 515969838 515969849
    0xd06030804090b010816120234050d170112050109021002011a030c0603071b050d02030406081e040312230601020708030a080a0203150303072607021522 67
    0x882c1c00003001c0f0005003800300150000f558111168026401141c01c5012020f846c2d50700d000040e00d42c40b0244013410076a001d03182e82403511b843d015400000c16060510712800390b0040d01285c0b08140c3d104422a035408480b0b40c60303502e0810840c01400310700c440e180302c0800c260241c400444c0d010250340028001020184400d0050707035441510541901c0000e00699000404801034050030082402044140c0720061a110400402207a00b80740000000c80d440c0c810f6400408507a030000030940040e50740e03481401400c000c03a14510014032644409422141c14030120003074060300391215038041e244028000400c025007500c8800c004042d07044040c100040111580844d0158106080068107044460300106043d030030030050382d0307100f42c2c11101054003c982500e0060342c960761030410004c0410b22038011681030100003182006d00110a0b84003101d400b0210a100d00981c0e54a500c0043d032142c004001c0d013000e038109140341d1012004000c4c218040390519810f03a40e4104215490000c501750700309 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 515972338 1250 515971088 515971091
    0xa0203030424020315130b011b050f0609060a1b0c1b180b130b0607030f0c02120606030106090b030a0b10090507020d0e0d030e06030a0e0111181507080d0603080409 72
    0x1c5e4552505070200340006408003004c10540300201c00080450210143c021117180900c2050000c01c00704100d454100084034060303e41a0410103003454031480e092303800c0900b0070f04000301a5422910100381003111801e980314032642c018a03544040c000100b8415101c1c02d105032042c00207144250385401c0040501c858800aa03400c442d000308541800c800107051402032905100c01c00303a0f221071084901c110303003606200d0810018140c0c111200d06a00f03c0c02034015651000494545800068850240004a0090110383d4586983c0c0c3e046901d0000c8490b41a400207400340042610700d080385400c120403800740340c0d0454813040c111040e5032069030700320700507408644c582840d554040030081d140ea000b220380444030b004944009054140c040b5640340300d40380001c045400100309030300201100700001e0007840000039111201300d060300070f250361181d0801d208201c0000c9103440300741c480c500d0201051541c180402911030604e69005255002c1c105c0c1e03034402001c03010a580c88050002002d070310070b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 515973588 1250 515972338 515972371
    0x6030203060901090c0b0d0e0a150e0f0706050a1103070b19060f05062203060c0f02030f040b0901090f09091a060d0305160b0126030a02030304240203 66
    0x5041c60301e140248804002e900d0220150300142e138481104d021035062410f0720782c482c0c07143e000c0800180340d0244a502c0c507104280c07598003003107581019840340c0028100100200102c15402c00d4603000d000000e420a504043c4040c0324050050000d051540050318054500c078203469000352859100b40310a03100202c00b1820862a07030640420781c0e5400d1440003060000901d0010200d04121940c004d8522030580070410318412820013a1020700c200010f56009941a9242000360081075208201000aa40ea030000c280c214000812a8000d1b550b40c1a5103141c1850507072001d07040d4015000444c10401c0d65580010081e1070001203c0180111000000d070341c041601c1c1101d03507540c843c00603a01c4400c2c0c800400c01e203a41c038410010083d03074240c103140742d07110303007034922f07401d000c083d4600040840d45004000320b6109044800c00503850b400c2a0600000b100414945581c1c0c0114200100180c1c002c00000300001ca50065900700c2d0001d1124076040440c540c1030440907a0001c65144500185d0070a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 515974838 1250 515973588 515973593
    0x120a020f0316050d05071502070611180a0501050903061302150c0f1b010e010f030608120405040b030105040b0c0d021b010c090b1e0f0c060103120206090d090e04030e060406030603 79
    0x100300d44d0352020720309055140a5056071920305030041c000c0400c3c0b4603540425840c0c01c0c40f050303812852602d280603100560303032000441c1c8100d2706850701d100303140200352140e404203803540603100311001c4001c01030060400703959050140180c003240182c1260484144690340d61042908005040303515502d501400030a0041305a56182c90680403010b80084041a0145404d91308604034004804c001e103170031100030004d0103094000c1d100c1680500d600c0e00c0f0325240d400c002e0310f4100240c02640d0301205d040c4101082a410142a194240d9015101040f00e41c041840000c101340140220104010098144108032210782803519428174001d01c43d0351031300c414607000b82c0d0090010010301440300030350f420a000c000d069050a55045180390030072100082c0032000580240c16110b0490044044400540c1c4901d001458070f6601c9200c04050311420010402000b4007040e8002a09240da48000f55149080110000642d0140c0b081d0280041c400240981ea180d000081000d80343e143c5010030361900e1361 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 515976088 1250 515974838 515974843
    0x1e07050a0c02151e2d030106051324020c0a1a0717030a0e0c041b0c03030204030b1005011106090303070c11040606083106021b101a040c02120a020f031605 68
    0x5003003403680785d40c100c0031000701684900740e80c1507905510382241c507a00803207000c13040150701e0307000180e103400d8140c1c0c04600e04c100d8200001e607444650b401d4900188042d4240b001a03031b0b043c01542000381d26030074201c0c1d00d00340d04d501801c801c1b401014186190383d00c044000940342e006481c04150b00d41c5600060110340300402c181d110200c0142e408000034524541410038030703000b0100320810402d0140880003854030940643d0090341d00080c803103005080c03102007030300002820700c01d00b03000c00c54049140c4a00c010100d0180c0c4100003d0700a10315656440340111401702c1491802c560300e0122020308141601c1c0c070700c54a4003070b005c55158688141403640306c0141d21100404014925582800b2562404030180b0300e00b102c26500c030710090f0711134400030640c0c1280c2071000c40c440701610a108800258269581198022460b003c99644610b2400c109010a40d004840c50101507405941e0141c803c1488030028840341c811841130302c000442d64140315046600c40d6140f1034101e0050f02508040c000305 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 515977338 1250 515976088 515976127
    0x30209070f0c030e130f0b010201180f0230010c030e0307050c06070303020c0d03390c110a0303110601170a080f121e07050a0c02151e 59
    0x16410540c41c88011904024460b8501d1000201005100d6250202c03985031541060010082000709000c1c0c001012410001010302080c0580151b003804040c800e441d0800c041c0c0c5007000d4024100c01c81a8550342c0a000010307005c0302038016020680c50100ca010680e41840e821041c0072200080341c3e0000c0054010250354078124280415001000b2920001e00f00040507022802c023135502c60744454490805030024000c10070001180e0050030100c08078203600d0f0307200340d2480d84580b42d0300400503040302810180c0045900d10051000c2a425a059918003e41c0384d403659502c034803276009001c984c0c500802e51740b046650088010078929488078802110901041740505040c0c1403800c610785209506a0b0344036254000a81041c2c0c00144150100c01e41e00c040701c1800b4000d0803454a5814641140d03172130303159106502030b034040d0b9820220380c105200e003045034519041680d5814000c00702c1c0c0c00304506406a00300c0900310344030400c50400758490344000d030341074000b21850f00c64490080b111440c6410b0300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 515978588 1250 515977338 515977351
    0x52d15070512030630010c0f020d090b0a08041b0f180e1e0c04060e07110d0e0f0409061104030b0a05090d0503040f0203070810110309070303030b0102070f03050106030209 75
    0x414020448903407204808400100b261081120b4480030071007a20203171a40103c07103e4015420720860103040c80c1c208400355a10348031542103500803402c0c02c204607a230b49101d001c2c04040e90000c000603040300340314000d250b411900940c2d03c0c502030301c1c00a9440c1d80f0864541e10802904010510400c41204c080d9a506c081c64281c0300148451082c00d203010351603000304551100e80c91210822400e41100802c84084215800b0b0020028a80c03101e1800005400440c1d416001030a660700c07400304031070046100c0c0c203142c529889210810300c0507030400c00c68180795450f80e50401d903a50620004640170b8082d070200c01c0b680866455446085051002e04007070010145201d440c100020b00c51420b03030000c0d84400710040740ca00729469840d07074640841745140401e406507151042583c0414400b201103500111a010714404000702c40e01d10f001c021042c04101d840b490341d90040d10080001c80e0084d001417600000501c19100800d03115068000d035078006400c2500c1c1a991100c0900c00c60070690806a000314 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 515979838 1250 515978588 515978623
    0x112050f0f07060212090f090c130b03041202010902090c0901021501091a09040c0e04060204030f03110601050a03030203040302120705090901140705090904021002010e0d030207051501052d150705 86
    0x106c0c074004202c03d1007228000500032013004002441000030101500c3c64029140d1004880595903407480f81560404c0d20265040341c5540d1142426900520446140c258050082d951300d550b0140402e0098011602d05410b6015451016281c4400751001a001e05214200092959a950503510a00307031507121542c0500101010300020035041c001a00442d4100703061491035a580d0314240000e40129070004208880584603c02010707085501d01c2d4401800a04544036a0399440401503055118031018025820801003400582400c00e4003103811300c4d18000f140e40b155920307400b294102100311101003017655201000780404810b201a1500615940742c250b08142c0c3d0721000030170340740c8082c2000f0310510128140c102c1c030718000e400c049020700c6454142c1e220f4074002c03107015000e90b2103601c2c11102800f51441200e0014940300c1d40078141e40b409024a1b103140c200715000c403108420810035044090b404203c0a10075035880c2000040d00b910362081c5074980e4250714081d403504140180310802c40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 515981088 1250 515979838 515979847
    0x2011b0203040b0d0b0609060316141c05041b060f02011119180e0a02040816031e05011e0e010f0c0e0f042003011802120112050f0f07060212 62
    0xb6000c600b80c03090301301007444c00214104000005a030714412100d200303803c03032804002c00c0118041c103203071800608555122600d010040310059110342c130031541594141c0c50501450180e000c0140d0080e9800f600c201300c5503480030585034410382c810b50780c2c0e8044400151794026140c1040d50a000d165996121010440d003070521003142c1c4110741001d0708078101042040d0305c020b444a01c4011861006002c107c3c401411428001c1804000e1360060148444134843d5500c04210103001c030300000200c2c1c1e00681e01050745a800c030303000800100d1008040c2c07034564844042c1400f0344042403072092804d4101f600059440964940d1500351050340d0f00c5290030034603001d00b440880790002e21100d2000c60842c0c480d0b0301c1a1100001a00400410b101428950001541018464164030065058648100301c040f001c030020f04d660010382c490309035990070305800c2c100100652043c080d22032a1861107507080da50031000390745c0a10704d41402d400c0c16003030344c0c2c0c0000d508000130381d010700003c07141c98600d03407005140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 515982338 1250 515981088 515981099
    0xf0c29160302041a0904091a1008120f1308010c0e0109060e33030109060f0f1a0a0c1a0403090b0403052d030a05070309210b060112090302011b020304 66
    0x820612808500e51340702d0015150000d80d5440d401300a60035480304503118942c0030303124404036110084032880c50303d80101001040c0f05400203040003807120303089091446c0ca4000c0c954101281c00400d030100200300b41c0f85000c90010b4080c000c542d1002d641d40d44070b030b000e42450000108002441d13400700c02071240b1203a80d642d41d03880f0079000342c903000070f101c500c1514181855032044518282a9150400440100c00441c81000f01d4000750200c40a2200b1a80301980300e035903d40b60040203115200244144020380d0050301c0d50b00c0050300c00c01d036072400e10f4981c03040f0584503440c0046400c452160114a80741c00c100415401002060203400018035050070141955503140c5c0e9070902c0a441d00302034000446003510301c03c6c42d02c008440d004030381082d039132208000d25015110340c010400c00c0340030030900c00c4042420b80044566100f0b0041a04180760002402e80f11250080700141207941000203540800c1402c43c414010464038600c0b9500000303010010201a00c0324013221540541103401c00c101c00c009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 515983588 1250 515982338 515982359
    0x3020307060e07050d08040801050702060f04110f060409020c061b1803011d280f02010c0201021608030c010605060306010207210f03030204061d010f0c2916030204 72
    0x1031580c0c0040d00040803003018409500e080807550046603c01003021140c0c080000c1200600103c0e00c290000b4452034a0b00340317069850303580843d5041c0c440f50281d000200451100c1d03502c100140c4010f030008245c41050008900ca0361b0058010341c034001d8002604a80301c103401c100941d44880c1201e01281f008511600b8901c841c4980c03000901d07006c1c070354071280405540030b5001221200c1e6501840000351041100e058960418448030158030b8801c3d8407009021401d44d050079541d5030b010700300c4440c8000d90307401550341000c40c0e0790a0f030440c8190700c09a0441002d5070803650180c22500011900ea000c407090003401e490081e0080c0f40520400d0050011698000401006490700841722400410607400002900044c8000c0a402121258020070515800d5401042a14001d5660144100050070341d1210700c83c60a070320301d00083c000794100c51194810f00004040605c40c0304d1418050b442d83c10607502ca15040d26459548241d003000b4042c1e030340c4d0f80030145801c05140d03082c00d60070186000801c55 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 515984838 1250 515983588 515983597
    0x10f02150a0b03072103110105010e041401024302181b030c0d060b09010f0311160506010509100e040f080f0706090b09150c0d0615030c1704030203 65
    0x4500303a1940c0d14041c1e943e600f401003d01522aa0082c051228404c0ca0300c044002494041a8081307003811030400c1e80c404043c0070310b5045c0c171141d00388080c46031140e9441d1540c032443c5a01c190190f542c20f1120300359140c40d15050b1254005104280001d018000852003070380703010201408596240d9000301c80040e02c0300d42400381800d10001c00c0d1482665404010042e502020301c2c010100b02c00042000070a41c980d40250160103260002000003c0e218245802d040c4200051540443c0c070780e0301d80881e000d200b90020640451501c04460515200a040005250041c14100e0b0150001c00040c807060501400300380d0302605c030340c10070b1088070f18190700796801030f03005403000d84601c0c03042d0320034000d10030030000311130364010140000da5603001b60b41808030041010b200220ba10200da04003044186c000018540301006a06410007116101c0003a001255070003040d20720319540c0c550b03000242005040c039410407400c040b6180400d54030b141040c018002ca41200e0140b030044c21074070920005c29030002c240c0313 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 515986088 1250 515984838 515984851
    0x705160e01093303080d02031005010c111e0303040e0406240b130518090609010b0102190203151603051b0405100903020406060309050613050d1809051302010f0215 72
    0x5100b40e459006050f000c41002d604081d11038030000803160800c0c07102e43d0065101e130307600b00641c00015844000440e5428510b04000e002d1038048550200c140c0b42040c1406960640d4840a41e0001400d90110781542c0280c0e0103c10100c1c2d41d0f60401c010320805010749129007100f03403810a4005240324103e060791000e40642c0305130345400714004a404040700d80040291034000c0a03030080840000401c040004100c1d40c901a40c010708011418000703050040111140050300a42001c0c4e44000c0010303e0841c6890090fa814410340b54070703c5003003000000060040c6c1c1c7d461a40080c552031038902905680740078140084020702011541d1002402c2810340d015207404a0f1580c004400d956422110358056070006944145130103000115507405138029920103100308103403900e658805201c0641d00001e00c0c00900582c1255000c1807081c0d00c201d003801c15522040700302c84130803611140d00c0c00c100c0703100322544c080b100311303150700001990303004101d00060400901c001c01168192820181024034042c002d0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 515987338 1250 515986088 515986151
    0x501080d0818070810060302190320031f1d0703020108010e191d0c01050c0a02060f070803040b0103110915060d061211091305060c0306060705160e0109 67
    0x1101d000c0c0303090004100510301c2e2400c6540180700c145e05070740113111510040303205004a41c0b407005000240c00003401180e401c56082001c00005043e4459003001c0803c0132581400b480c44444100b040c01c0a02e01c0c0229940c0500042e01000e110201607001c040799001c62590b484000d0400041c0c1c3e00450941c1512143d50701f10a00f500d800107401d8100c0506030083c0c04180c1004a2072811f0705500d19618180d2401004891940d8400303801560b1603c07903c0c1035200c107908681041005400c0060042007444e00005910f403510325151124221a082958111144c03155040100140024202c03a199104003c8507604014241a040c0c1c60b0403080303030880c0e24007402c2c0106280c40060415400300c8010710b0030941e6240000b0842c13411b40070111181490034401c0301e40c40d0200740c200c812426141000e59010009004584842c040e41405070001843d06038001d0301000031000044050080d0794918084401c4049260700b001e0100c03402c443c05030040705401c0d01d800108100704241109081031007130542e52 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 515988588 1250 515987338 515987371
    0xb0304261903231501050418090c0302091305010b0103020901020d0f18290c030319061a120f06030a0206070804090212010f120b0a0b0427060501080d08 67
    0x98001c3c0000a628404060501010400c0400d403094034030b00c0b0f0121884041d0401240d0710055515010304d020300b0b200340c10250030041085201d40d00c80321100b4022800f0040c0d10fa600e50015a03006011038608441030482512502004000d005030225035109080550a2240701c0340001d5549400042200401001410041c20b55005102c2c526207440301c1c1d8944080c071529503404400c007108400400030964151400310364084072650568900445001c00384d031850300c4041d6203d6038948455103510b1419035a40000415038080034101404408904501d07855041c04a034900000c10000c141c803a01c540a0400c001c216038010507102280b582c121141c5450743c40500b01445140103903004254034a02c001415040c201401600d83d040340c00301c520113648207403a41c40c0f180038003014980080a8559480c00f150181c01c194200d07909981c00030300005040f00130a03060aa4050400c649800108140e400030400d109160181c0c40c050840e00e030041c0094145040e00401e4020001d1052450541501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 515989838 1250 515988588 515988637
    0x50d080304170a0530040b1902070b0613091e03110607020105010302030706050a02060105010305070c0606060504050111060610030b01180806060109081b0f01050c070b030426 77
    0x1c0707016080100300c0030541d44600300381801600d01c0c0d10000305c203000c10032040b0100e020940e00c08030000201c0070702d5004842c1c946556072111488000a00090b1201c1c0c503020418407580f0043c4060a4050b0086c840303088a4100002403249000c0306a07585001a030a02c107404004c00c0c42e0b903030900c0e82c1d00111500c2c0000510242011500004012a200c0701802070000780540c0650540085040e40c0c02201591a9203542c3d006c1a296403140340314900141e00103000400c00c2c2c1d0300036401030b644110f0a08000d03440000315178801044680d5908003801003440030038240140d50303004e0030b4020f500c8607100042509081c00400103070811101111401015141c00d403030349650b44141c10700c0c500c881070306400030304558642c0d0341140c90301c070308581903400204004c0001030050070000340990307080344594040004191039000c1c068404c2075214401d06000c42000071a078400d0007000480000c0950700f0505440f41042d28000741480040c1c8441c0c0090b00b5020b07900c0c0940300410044420201c4454002c02e401c17103d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 515991088 1250 515989838 515989853
    0x2060c010b090f0106110316020f0a09020a020714010207060203041208090a09060302010e040c0c03122009150c1b0301180b0601020c04050709180f092109050d080304 73
    0x29000c950061942d2042c004002d0003d842d4505885640d240c0c1e0031084008140540e590064034003680e1a68407800c001005410464a07860070003601800c1e030026030b5103c0000500786d82c0507507407650040e0311080e800c03c854440c00360750301c103209824800751010031702d4a00002c0da203000d5405a03c070b0203a040f103003106c20040000216041444060013b403192039480c0c170650010501d52105038046100c4041d42c5c80c40d45054440d9031006003240d12445001c0e400c588044810b02e003a5111154600d03034407030b0b0300000c410f42400c00b250f607144030010b0b2964461300340041c400101644d00c0c100d540c0d6907003400101504100811441d8003040c0c4181c1d4040c00c401d1290009015010800e0240304c12162045940701344100708104c1031040b142a0200d5145506003400e00c01202d1040320800001940140c041c025680c0c0000740c1c140da41e81004e800f0071590100304e00b28080f81c1800c0002c6071919100700f8000e14074444501c9038100e0300c9942c28903410349880c22000c01c0c00200c2d9203d00a10740c1000100040800000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 515992338 1250 515991088 515991101
    0x6091b040e07151d06030a1a1c02011101020301150f0507120314150a060c0305120112020a06030c020604060e1606180f031e02031903170f100302060c01 67
    0x1e2200b00d840c1aa0b0b1030324100000d6840450702c0f0001010307101e0038040014100001c80e05000040c0c200d03861640d0302c000501c010001e5411005c10190f040280d020680c0d100d0044146803c00c48810001e41900c5100240c40070307601002c80d000070b07401400104076100ca405001c2240300214204060100e48402c0200c905d4404e17200c005104042c3c6110201115078180d00c0028031048003112000b003030712a90f401406045c662200c1551081803590184a9a4400e60004086074428209a07040000008513140b2510b0b0913044000800700410302e00c000e610b41154184002d01d40d504082011880e5000003c0d2a88002403000d00602c0c1c07110000400c0d542c0821400c001200003041d040c0340d080c1c070b4842c000c107402603400b05c9001c841080080410340c0c4065190030012a0340c0108500f015221404034501c01d000420000d0b64103006850030320030803030112490381d54594421b541c1c05400000800e2104813805001e4403030903c0c0e031250000c1110715003007806c0c0001640c0c1c04817810b940340d83c0c103000c40c0da015000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 515993588 1250 515992338 515992361
    0x30c0f0803010905060f19230402030a02030f0705120606031003080d0f06090c08010306110f04081c0905031e030d0c0c0209091f15050d0f0c05010206091b04 69
    0x300040000303115841980254020b4600326064607450340040c0401ca101e00d15407990404c200300003001046807540503240301781c01d4a840280d101c0d40d640003400140032a00111640800540c0010401900d51081070500d80d110566061003400d140d40c032604203170b5050f80200450300400001010a400244060f444801140e11000c0f65030744a51455034203000c3c0c0b40c50310b01c0c1c0c6180790800f00c0108142500d4029401045000d81c3d031281a6865921030130301a0003c00f041c0c4070118000c101c00c01c0651400c40041024209000c014075580750360f5200305c00d55400501c80d05040002886c0203101954000c40c00200700c034854024085111060704030300d4114401c60192040440c6040e1914502c2a0012007a51082e0b008850201c86580d0f001d60080e1a12a003050000054400340c41c2d9104c1000c00790b0150900d2105000c0300141962150046042c5030031400c1c0594031040342d2552002048410f01c801c402505d801c0c030251045060105d44588d881d400340c0a921320016101e40c410540c1c0d103503603201e03c41d13800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 515994838 1250 515993588 515993603
    0x204120b1b0409150b033705010e19150306020306010908190302160f0519080106030f11041103060f0301110d0c09090626031303120f0e060403030c0f 66
    0x2036440300304000130080c50290700c0068020b40b00000e040305100d8107491003040c0c0e901c0351400c0106000c400c00c540032805030410301e200300000c5602c0d6102e5510304c5018040c0400a034000841e003008224540c0d005030203000114014240900243c000b40070028160440754440300150300c1383c44000050313510040e01e4220801900c190304000d0702416030b04446186c2c690080e0242c41e06040d1501018100d0720309805140301c11106484100102d041014408100200c40c1c1103180005031180d01441c2507c11aa009845055625606400748503003199120340a0200316802c001a068070b0313040c481036010040c1000d114107882024400f00b80c900790802034980c941d02c101d40f560f42020b1501d0b1030080c9103c1d0354401c002007500101150041c010b10501c410f07180418000c1140e6008400503075030445018103984098042400080c00348080014600042c61084a2800d000031070803400601c40c0102c0300c24030003004119050800c1940310901207c1c01d80c1d415151404817102103050510800402500050601307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 515996088 1250 515994838 515994847
    0x80703050c01030504260307120615050c0703151a01020c220204050402031e0f04050c0415050405130203160b030f0601030e06090109050705370807120203010b040204120b1b 76
    0x6d826440080d4403030308464903504c060355900a01a401c032001c3d4010b0f0b090040e03241d808040414000c0e005803070207195500441d61015180d9580b800c1c5d808000b182e109a81e52100f070620201944014108040c50081c801400034844690010301a80d0508500480440b80007850b03030400b82958044501900e0064030540d52400c0c100000c9044400c3c0002041c00007860a02050601000c01c0ca50780c02660031000070f00710b41e4404e000300320003014207040c008105042e4003000201030304c0700e001d00d900c94004030954100840c0280181401c2c42c0d04100740c82c9914590310f20910682d10080300b96900b0941c0708801e0001e036a11640164000d0850040301c201e43c2c07091400b004075800d030541000a03039900c24000c4e00c41041d51003061007601c60f0a00d800c484011072000004c50b420600000d182c4d86070506003e003142d05c59072008114101407041d000b0b480143c194020740800d6040900a6003000f15090700c4c110324151814000140020914170014030040c010004105101900b00503461071224a45032243e95 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 515997338 1250 515996088 515996153
    0x1309080306040c03152c090a06150e0705071a010b07060b0607060501030b16020a081c0b1f0207050307060e10121104081903052a0a030f0801080703050c01030504 71
    0x103800e42c2e503440200342d5220307a003c601c50480000503136001f42c0f590002040713054800e07510000075182042c0714102100403200009401d00c1140103941c06840b01d41c81c1e9917034403045801d140100d103600c2003034a8180e0303907108010451109404212030405030050000134108080000117030341c2e4400c41d04050031090030980080140420107900c0c0780103030340e00508480c50790300c0824243d864000311038001d00088001d10880058008040c04c021280310b000e4400940a03030030000040390b0000341c8034584102c1d110007907421840c0b50108040350151078124001e098135440c0c0440103103180400d1003458058050f400d03815888501074400030b440003010319014404955505e859038025003140c8207440c5d00d84034128196100001005d4041c410a415a48151600139004280d540308034030048510b022440219010070032001c05c0c000481c038a132090f620640e01074400c9400400c22003041e0440081508140c1d810000208001452210b502c000c0c02c0100d01d503903860038400a00741000342e80396032203840c0d00d203150308 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 515998588 1250 515997338 515997359
    0x301020712091502010513030c02030c0d030305150d020f0d140601060509090c090114090609180702070506130303031d0a0309060f09082802100c021309080306040c0315 74
    0x5441900d030b0f2110111072040000c0f8240c0b5410b95180445181e03101c820360100344101940b1000d5400a0100d900119002d2701090069641c46801d0340003940d58414400003142030406410064404c0700d68010722103898001800100900340000d04c120002071180c0104100c0e0490300142c3c000120a0b102c20f0f6941c3c03a0040c00c1940030600540c442c0b0040b01c001401c2c461203000751000101c0c1a990740d02c800805981d03016150340850030f001d44c01041400180c11958483d282e00d007211804014007901410000000791034150310f5044170b0320a030307414406106041400f2410400312505807401044c0c194222030b06030360018004d1244000343c01940d4641c0c1c10304d40c214114400300d4581d0b84d601f40c41c0be2031041c011a0103215a002c0c0c22860342106000440400c00211440e410010102452005924a0340041d80c2a50301303c0a110219484c0e51400b010340c9480703a020240c804070142c0620001000e9a1500306d04d00c0300802c424030840d51600100d00b030701e1296115124ac03045c8070001c1070409803a0b482800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 515999838 1250 515998588 515998607
    0x71b050607020723011101020c10090b071119020a050909160902040b0405090c040b13030c0503011a040507020f0d111e030f07081303060e0d0c1106090301020712 71
    0x8000d4481c1c3c3e400010308415072a11040d05a00f808942a140c0a03010011584000d0030b04103410f056409101c15400c0c1401809442d24080d010324000800b40302030b141c8107944440040040c0300381311101031000c50810300031465040300e050742c4c5100740900e511480040e0361403850b0f4020a40003003100b4100218440d0020b2a00d8154083c0a6612580e82d50340f0b1161050f0300c40c2c8d014101042906000800044c285100b007160068000e001d020b044c56160301030050300b0340011841c040307120f20700c01040061010f00000100580000c0e4002d204414007031154603e10110300441d03900dd1a41c0c0c1380010b00d00c502c01d12142d9402011181604ea0040803003c005141e01080c205a000500607905c40d1040072900c0c3c41501040c40f0013101650a217200c040c4003004582200500750b900100070042d032a041d81114000030051482028000350060320344030142d00d040784901030300040c00b04002414022800c1c00741102112442103404aa54032a46000f0901901076120300074841c00030b49690003003c54208100e103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 516001088 1250 515999838 515999851
    0x20a020f070305030406050f160f020118030209160c0f030e041107170313080a030c0f18050f030a06021815120f04020418030909060f0b030609071b0506 67
    0x603054404a00340351911009648030040c040d5008000402c036090081018000d210a0185190700b040c1c0140110100358964040450710706140c4800c0714219030300150151500a82c060340e524071141940e011800001001d03122618075503041100c401500c1c80f450b085890b06500010740249131205147c0a0205005035098a20442c1400c4c2400c1c522801202950a03494000464200c2d4100c0c894401c8104c0e407000d02003090041e1440c0d40c00020504001c0286030305805a0780004810740f155500030800a00d0107551010054643c4254a91500c07482c004410344208030742c644100695040064540a1001c5004121600200d030f03c0c844c90041d020382e00d49008090302c84c0654001403405060b0b07036108402c01c072000300c210070300850a040080b80d0001d90081c8060b02c002a100d801e489821400541c404007100050b84291050100c50031074028400140000d07078a07521a24100003d05c1c1c4180001003603140540031075800038040c09d00c1500700c4418040c0101c844030307091000381482a20b0715400c80e0603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 516002338 1250 516001088 516001093
    0x10030902040c0c2a03081909120206190e19050f0d03020a030305040201170c0c010f060f03032129100f110f01050c09042a080a020d0609020a02 63
    0x24111003c0c054200590555402103615103400f18903100384070100d04901c0030342d220103511040440090031940040400741e0380c9100d0090316450082d001402a020f81d00403000414260003103800688603442658441241e5084003c090745c2c08082c1122b503d4012600395501840720011007000c4420341e100002070300d1090f900c104101d1891400c0c020705c00360810000b070060744541b0a010101c1d101f0360002e80c01510502d0300090700c4109490070005d80b40242c6d081c48c00e5180c0002e400d01c040d0024851072040c410200c1d014401c003031a111800002c0f010a110207002c0c4103028150100860f10240c10307482501c0d45c4001081030004514000d580c030710003012005541515031100d40703814039102d4850304070f0070704941d50215124080102202c0204c58880915810711070b800a080070002c00380a043c1c41a41a446c0702516654240104026074502e41c0080e51004009124010f000d0b0031903403c1d40d1b140115007401250f684481241ca0300902c1141d16043c3d486140410100f1201d12980041c00340c649a0b80c01c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 516003588 1250 516002338 516002351
    0x180f111509040f050408121302100503090d0206010b0a0e010905040e0309130905120f1209010507020c060403120c02031212010e0c16020415120804050103060e0f01180b1003090204 79
    0x55000711341054601400ba0311090146040021442581d1540b0180d80030180e041d0380120b80c00725140c0c601041c0c2d0302001c200c000c81000b000070340420152007410300038802000c255140c11520300d444e108070700c000000c0000c60701030040c640e40103c011400901e4007030400c005202c84c081e80d440d1603401c5101038030711a0a00300014540d140b078601610074000e8000700030b040f954910000b14501544585220482d00c41d00380184204040307510a203a00c61000c140001c5003600c0d00b07100003400c1160019245101d54070034481400401d034044880d182070881800c0035202072542c1d000181c42c1c680710b85010305404600042614848034282c242c0c504940401903c140c0c0c03921010b51801d0580655034420341811313074420071000540f0380742c5c1109000c0c103036100030000703070365142d4450b01c1d03607021500026035046400140c2004156410f00c1040d008151031980840c0e82d0805c1c036590a20701b01d061040008080800340c900e20504910b611040807070380000c01c03e41400904800180140841c000241d21940c540034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 516004838 1250 516003588 516003611
    0xc15030516020d0c020a030212151f0e09070b0a0905240a030b060903010e012405101214070f09060e010203090d0c05030d0507050601050103180f11150904 68
    0x54900070310616900601080245031404843c281c0851100340d900041a91000025072103404103242d0180840f4060328840e480c03000c00521800011302202c046a0982c605801c00000c000501020f540702480c0d048211b803200700900307103040015042201162000543c1d41034094006904908072001a10201e280300042c0075191109401c1030540b0043d503004000100304a0320036440642562070080c0420300b000c20070702c040303030031038203a4001b07481c9030b80d91840700b00d0700c40c0040c0c850006821a851000301c92b45080c40c0c0812521800c10328070304148001140201400007860700422010420141d900507640b0f46000018000c515001800e00800c0c030409020465a00c220446090702c003060b00210700e4a4802c0b42401407080c040c000a035034808610101103101d5409010303c80000500380d450b80d031030b03c81500b00303541400303010b0784000e0501d0314100048018500784034103240b03201d0308296855041307111402d00b84403207000c0c0c00c4520b92220003006014810101c4d034000e85030b0003909907000c210071036044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 516006088 1250 516004838 516004861
    0xb0f0c0115050d0b090a2a050d050c0904080f190806010f021e030f0309010501030c240507030e0d08031e0609130f15361e0c150305 58
    0x14050107400400007124900414442298641c00c48001c1003150361a415903182c0e00403c03407c8000c03d4000038400d40c0c15044220000c80843c0c007811080310315030300d0040560f81e1513546010b05040c650088408800190030300443c1420b4810107640070130425a100000f15040880500c03141c01100482d02c00030218046500c20081d1101001403500141034000c14141c02d09120300c40c4030100c80203480200181844096080080c40c090380c00000045401e50461420f038003841855003000d0002c2d1000d1120800710f180199482c4c46110321030034226a118405d06048900d02007000340030b40c104060058000411507614011481000782c2c0c0b0f4146010200e90170301e1800030901351446c0e5440071203000840c400104d4101c0800e102071140e02c0900d03982c41d00ea943d0228003104052030102c0b4640d0b0303204460284c01d01200030100402c3c61070500110042c0300804900c02c0d100b008000e44aa9240c007030051856040e410b4464510707800546401308944e80304040e42e101420440c0d6100005d040c140401d01c2030140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 516007194 1106 516006088 516006131
    0x5240d020406080c120f070b0a05040b0307020703030201050603010c0c0b0619090f0b01080708040f05010f0e06150f0904121202030406090308060a0518040503040b0f0c01 75
    0x4600070030200034a8078a80c190260400411044000c1c004580700d0300b980e0481c2304040d10382480071012582800f441d00701882022001090002d1903400149070f000f02c03446540203000681d40c2c2c90501d400c7c1c0e44a2044480801d10415103600001d01c01e0440740c0d4498030240c940c00140020f0300c010240b401e90380c3d00501800f541c1c0c11104070000b0144c02188450102824810711a0410680003040414024006071002a0001c1c070b00041050039040a490014445e009000d2174088402c12510745000362185501c4402d000100b29581c1884085009408001000340841d50b40b50307200c02d180b18a8000e218030802c02920401c1d0030481d603c3c03001d907019900401000403640e04070324000d040043d000c4c044e80c0c801e2070a8141080203540e01d04000303114010102c1b035010243c4840c60140e24600440d000000c206102040c08810030100320050907003416000c0082c44401503444c400c4210022 = true := by decide +kernel

theorem cover : BRFrame.Cov 515827338 516007194 := by
  have h0 := BRFrame.cov_init 515827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 515827338 ≤ n) (h2 : n < 516007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
