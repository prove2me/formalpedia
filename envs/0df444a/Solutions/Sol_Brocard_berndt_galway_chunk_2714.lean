-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2714
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:31:31.437396+00:00
-- url     : https://prove2.me/submissions/caa75bad-fc7c-4d15-8ad8-5e9082c74cf7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 487949640 ≤ n < 488129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 487950890 1250 487949640 487949663
    0x5130f0509040209040f02041d0c03060906130c080f0a02010906051903110c0d08061306030f03050f0412060209091f031b05090c03091912210e0601050a05010c 70
    0x51400c0103030964017501c41d01e003a07242920103038007080a460044101c0300300d00380074200c1130380d0204080140c540c40003030460042002c5c2c280303111002d89414000c0c0003060000b0715158041c041c49070390954500280781001c00c49c0c045d6540000c0031529003060703400890006034400000901c0d5842502a2810b440c42c81c0300354940b04150030016001404a0003100c0c86030300040c0200e100c000d01c14803411225a05c40e4690250502d0040c04100f1008001018480464500381c020300c007050000e441d0f1540e0940c1824055510b004918038145103008551001040303800c240070420030080103070082e2204000070b40710880d564541d1644113021601d10300502100a80307051041001c517a654a0300d0030504000240021a03c6e00e0304c003c00c443c402d0454100a074107500005000f030180c0100b000303401c81603964490400138074042d541c1d0519180d035010300364100b110241a8001c0c0845031305501003080100038003003021803009658a0348480c1c007489164880d61600300c0000d21380d401105500041ca0b40031540354034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 487952140 1250 487950890 487950893
    0x303070c0f0b0a14090111010912080a0e03030a051f0b0a08160c030e04060b0409050f01050402120a2a0206160e0307030305070606170604111512060d1205130f050904 73
    0x403038000140e980d0400030f0305140b10030303c7c10080c03080042090081211205035812200050720f0f804014010f110307080c0c50604035074000c9401000752034014408180100d40781d00c034800241980440100104600e81d8103040001d15240c1c03001c000d14808035152101609650344141230700b4070009220100010a00314032452000034400d400141a050004000140701e589418407140745401039000303491290ba80f0000d001071180c4a01ca00343c01048222001e526080d0810080100204040c14098620f6114098851610301c5485807100704c0030520078100a0307110b82900255145c4040d5a000380700100c0c20b0000a009100310201c00307000304050f006201d41e600e1940c044640782d2160304143c800d50b0759958045200005810406c0740d42030494014000390500382000b000b85d4a04647d2284503d00292034045120f88000039941c17009003400403041242c0c0e694002c13420800b4948401000381440407280303000c868002d005040410761005c40d100c0c2c07498071340e039410542100b0760040744d07484190400040c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 487953390 1250 487952140 487952177
    0xb070e0a0303120e030a0e03190507030b04080409230601080f070f02070f060306060f050a09030b150907031b081e2a07120c150c05090303070c0f0b0a 66
    0x403a4070100302e0001915131645030599046030007210843c1c0004071000000d01191030204500094114003c855080c108031075920265240590310008040b0342d00e500000e42849a01402e40c2c1c000c10000005005000c0030ba5008000022010742012288030008040340441d48202d072401d1140d0160700554119854190055810110420580e021481400004035450341c03803608150007012592401b00c0c1d49420644040c0421204141c200204402400380024a562041416040b01d4000f0f00c1184252a09010401712050381e402c0180c1210b01c101c14001380d10fa15a00c0b0308084040d0981030001180c8100040b03403450801d503114003142d41b441c0549090040d1500d6455004076200c00c080c2c2558200d080402840c128074201e524001e0404034412081c010542d0b410300280306c1c0b40c2f0b00780034440d04994688017403145105008078410342d00c4454410160051040b00c01c1010010b04503903d944c0b0354035080b10007030818015041c11656250303002801c121a03074103540c2c242c0601e89030100001417410003403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 487954640 1250 487953390 487953407
    0xa02070c0e070c1425050909031201180b2e020a02010507060c03200c0706080c0d2c0a0c080a0506150607150203060109080f0d18150801030b070e0a0303 67
    0x112882c1c01040c5c0f60b403100c1c0701024040704c00340e410b50301035161042c940010400100c0c0b0007040e41402d034000304603c1368480610240701d030640f4180c00300610104400301c0340d5002000f0200710182c0100c40042d003031405c0f5a0045460403c012215000100098191000ca03119988104c0c000d020607000d005d0f02001a131180c1081d08441c4151500050801d000b442e00c00e440f0002c0d200304c01a001e80020107003407644080c04a00060101410200d1140c104541c0e000503d00c5020070302d054183c3c0c0c40f0701904042902d0500302e01c10f8000c031104a0500300d141c046043d1030301c2c0c00050854621380ca040c40055221400f04400c8015a00000900900e40c2d88688071240607844116242e40203804000d18400034215405101c010103100c180183c41e8901440090035451040d00f00c00020f50040080701212840020003400120507881c20b1850540000c40340620070300396030484072a80d805020b1a1000d16401900b09040b03d01a03120b1411588a00d2005d6801010389621142c00c00c910000038400300b8000c5042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 487955890 1250 487954640 487954673
    0x30a020a110612070c0b0a0603080313060f0c0f080603120f0f070204050a0501080f0c211009140d0c0209070806031009050d02070f0b0405010807020709050a02070c0e070c 75
    0x50602d0483c101500310030303034501115202c010811558103a018030002c81b180b2544011000780c104480d0341552210545404001d008480d0182c02101074401c21503950021240b1042007002801181c0f101a8007600d00030011300c3c4000041d002a000a150b46000550580142c038401040c130314061030a03440710029440340c4041d0711044c1c410015100141c1b103504c50310707129241d01321000502c0d506000c00242071110300381c240794141c2c0c800310001c02640da0707200100340c100c0d42d68140716020340100361110382050060140100c08610340750070f5400b800300039a01e8611032600c3d2400d5802c040000d010a940c00242940007a410440807070004003a03030b00034980240c11000003001c50701c4010303000c0f441350240c40040c0000c5446d500071050768207125030100709101c080e01204104c1e004490900b100548140211301c0703014104240da801041c1880d00a00144020b00541603060000b031034002c40c6035001e580f005034212400402d00d4000550482d8000d01c43c2d0155078035955940300c008032900c400944d410840340703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 487957140 1250 487955890 487955899
    0x30030c0702121501060302040e010b03091c140d090302151501050904290310140f040f1a06010e0d0f0609140102270301020301060c0f05030d022a030a020a11 69
    0xe0f891801400e804016000f04400d50f405a551418420001c484100c1a802082c4000d014000d11810210200341e042c460361000b805a04000900b007000c880ca0361180d440880103070400a2148400c022a40102040794066001ca600e2407010746452000c603101140c602c4242c0301603440c0205150b100d00001c04072014000e002045408140399102e550f00141d04590250050b0544805c406040912100c41e20041d401c20810851910224a4010507401009954454091800541040203450303641d0b2103960081c0002c0307407a690b10b44450300d00083c00c1e00c5190124043c083c001c1458a0309044840400e54030040c00c80f0550025591070000c4d0289000c1200c00c010800210072000100344041c0c00e03041414202001d804103030000007820b500c16100d1050080c1d00400c018404a45c00071050904654040c4200362514101d00b4041d00314081c0401030360400d8000111171035482c24000460131100d80b02e000c1944049054120580c2c0d034400e416480016030410f0300300e03070041000b0116401e07000c01d002c0c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 487958390 1250 487957140 487957153
    0x71407181e020a0302090a06050414040905012004080111070c0303050a030e10021c1a10031e0501050f03070305060601050d0b0306010806040c0b090105070b1830030c070212 76
    0x1e01d120903030704841200c600003a404250604103103400d4203008018925030611030725103402d284402100050442103103000f961240c0500c000c12000b580007030340c9041800688052001b003040f00241c03e512511400b42e5541c00d00f81d003120005407010440d01480d40c0602c00724031062171583c0c11f580d190041a448400d1694420180010309000e01a0010748451980c0059035017002c2e40c0105000e00d0124201c0e5020b610f4604a0025420b8003403040d10a0764044540e12410490010120043c1c00c0c40700801d01c01c000420041030700406c4a40201e41662800c50340607180481c14024195248910321001e410b990148021a0455020714000c015519a8650100f00442c400c00460311b000c20aa12030181c0e50301c090100300500440e21180307000f43c480a000545003c0d24100001d0080c003844001500812011004c900c1081801c1d01c64010218100701381c81002c0007079000110040d03540c402059034401c0010748030300e8807410b04007105d2140c1c0e890540c40d403c150541e02070200840007030200c40c04c1c900c200e5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 487959640 1250 487958390 487958441
    0x7080303160309140607050d1107120c0213090501020a12020a170702030c070305030d05130503090f120a060504060b0103141b1c0203100b0414090901020d060b07140718 74
    0x3842184d04c0743c41d02d80c0751f590b80e802e14600d903801201c80c2c41410003c110410302844000528109010b043c0d20034510300304014031654000200494501080c505120f80b40441c041d0401c0010b401409050702542c540100064040c2c0c180b07401d92045c050b481000401c1001042c100c80800304030346810810920403a4100b05048010070316208003a04141e0742980003144150001046001e0542c0c041010301060000310515074034545e5074000d4441803842070a40c0320306201b880d11005941d0403000c00d41800c50f041e01c01c0900706480200001d84040e2112801d000003d103055009005d9080d10400040d0100d940d56200003030003c000000d0300302c2429100042148001407003168515050a240200c00140ea070305010088250f40d0017940d101c46102c007414481009601c40d0301c0301c0b0494100d000d0701e1b03e1181d0354948dd20f6500a1241c50b01100c1940d1400c2808a10140d91201030301c1568449c2c801c202c0f40c0d455803600107580c0d450a1041c5c50750140341c01004110340780117800055446408800d152416080c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 487960890 1250 487959640 487959643
    0x10e01051f050c1902041b0c080a02120d020a020706030209031b13090308150d080d0b030c03010c182112090302270a050c2b0603030c02030708030316030914 69
    0x1c0c1c0803404040080b40c50b1903029031405209413102480c4170044858101c1f00c030392015042c002204000b0f00b00500204030112b06d103000384030490700140c0418496076254503024030500290040c44240740107200300040812007a0281c401c40e03040703000040003840555401c0d85055032300448548066004a110008141008564011066030340d20a4540e01d003549001c0362a50385100c88505042d06c03400341d20724000040303881c400446050548c0814042049000f400c04a840e0060000c49290103601c2d0140b004411933108204962550381210440c11869031140b00d04500b400080900005451200400e80062022540645454a00d0401c1c02c8450740da40c0020b8002e51a0f002c03000303160f4a40c41201045039038010390385540f050141c05c040100b420030500c2c6002600843e078044015801d0b80132100440c0740d031040780c074881414107802409183c1e1a4035000780b0b01c440699089000c1e100301d001c0410050070200990380714071311103041c4020540c0080800c0700a024840307000c1d01c08007194040c0ca03010100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 487962140 1250 487960890 487960903
    0xc090302061b2119020606100c0813140a29070312060f1503020310050108090a0c180b1c060f020c060412020c0a0605040504020703090b040815010e01051f050c 70
    0x229482d142c2c65204001e45580d0a0540300e1380b03541150041e00400c445540c64030700c500d008142c40d00d007240004080b0300c1c010b1030310321500d0a5849045400840000c6c0364000880301d103003d40702510f0220f5031507603889241c03240488003c070300c08002e8407030043c1680c40c0c2c00d2240a080d40d50701034a401e02508620100750303401c9450b580c00c01c00c004070280d0b5090101ca500e0075074110a1081518045180d8034144401268038810b501a50381008040740c08500d41c02e60130000500b0303840d00003100a109540c0d8415170510f20302e8440e03095043c02c0c20400c01b042e55142480c8941c41d00d21000407030400701142d035075954004041e00349041c00c03800e50034004403d5914040208510075071041445203819070132040c001e8a0102c81941c0e441c842c0302c0205091111650103010348003110341c152005621200c042c076041d078426450b0740080e02d8500c07021400003000800014000810300140100310b01a076214001c01c5420703082409555009020000c071041c4481e400f20b51403608484a1404900300000c11407068180034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 487963390 1250 487962140 487962193
    0x3050306090112050307030806040e1605030f1f020a170c0d0f0605010509090a1d03040e01090c0c030516050d05070203120903280c09020307030c090302061b 69
    0x140080100312150404400d014003510f40c209240d10032143d10b40d10f0654034851a40010200300340704011907001e84a0342c0141e003003c0c041106a070b07644144510040441074492081c6071080c496405803680082c40803400784c0004040c0347c1c01c4001414003020131006944a03026070b0f0100078402042c00c04800381105a40d01800302c1011841c3d507520607404034000c0d02c1b80e522200720300d40d1900d00e007044140c0c0c0040803100040d005484c40c2c000344c2e581c1c500000061404e00c0120301c000b08081e0074802c606a01000800a5410460300210300e640c0700c5506034112100465800d009c079120071580300c0820b0043c3c0103401c3d1115940c154012009681e036038a8200396040780e848021030008101d00d0214034090004903402d4034540761a40c00d042c100000070307a0711422030501032070880200c0c0700707a405910b02e00c0c103c141e210303040036400c0c031000c0d640e110010081d4000c86080340002d00c4d240300017070407030310902121040380c0d001050f450400d05900001c1c1400803201400100e580f0031941c01d1350030040c1070642e4540d6034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 487964640 1250 487963390 487963397
    0x9060d050f15061906020c01030906061205070e090102030105011d1201150609080a1e0c0801050c07020901141f050c100903090e0c030a020904060e0a15080a02010518010309080703 79
    0xb41480c80600c0138900c4141c14025403014100004d0103011b600003030940c0460002d10f808556055581040f00050001d030b0460010b41945994680c140600001c45000722991070050421940c2c50403030781800c070302081c01113500040f615000024580c22a102040c0340d1000180580102120522640c0c21603481904900108100f07c00400078941c000350007a00404200d000740140600640c3e030a46c101c1017031181050040354155008007800a05d1022101501124008004905040114811a4100e15000c82c407520b040000400c0218503400c8900d01c1c41000713080700c4088840c5005040200841c070314845c04000b800d00c1070407004001007142d0450740e00c60210004582a860400420600c49d5422410308010f1510a0202409200e02242d5020401840041e141c405080004002d4006503010200344918901440201b0760f01d6445540c40c07418101445100c69074901c6041e4807601680b802a000c10740034802a0062940114010540781c01454000b030700405c1b0340d4440c542c64008400a6002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 487965890 1250 487964640 487964683
    0x80d0c020a05160e1f030c0e1015050702010f12091b15200c0d140105102601060803030106020604050f06040c03200402032d0609060d050f 61
    0x500400703003c156010394030145041001818045650640c200280113000c1903154820081c103103500c0003160074040d55014111001082c2c0d64040c2208141c0250303406142a407040d100001c00c2c0a0401c1200441403454a51074100359998005480c0c0800c107040c5441408440c103040e49401c1498403c2100b00391050310200c400104444200845514075080501100c1002a2800405401010f05a601c00c594601c8640c2c65a85c030310800d0501d0302e15040306800034400030450040003000d4002e6010082c2a0000b00802d07524102256034845041c42440c0c81004910800c2c00d80d00458417400c501c8020690021541b42e6941009518560003640f183c001170300020240000c0010600042c6040002c480040c00c4508054507405890780c1240320060481c00703420b1001516607120003a1b8880504000c20864483c0760a00c41205d5403803d1510501404801c22202811b072040310102a003c0d00303010b885404a81e0340c1c1414403a07201004403056800303114103550703515000e4003040781e06070741c003900d5007a07015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 487967140 1250 487965890 487965893
    0x803030907230f060a02160e0403020c03070530060a0c18060906050309190320011e050603030c0a050c04050906090607030c21091119060507080d0c020a 67
    0x14144080a2000c5401e00e0701d0030310040e43e4681e080d07003c0c0000d08031280c99a400b0000000e03440c040010058902100d00358034001042a481390816110307a00039006d594026040804068843d01e01d40600f45e0300112440300010000658021f603040c240c0c2d00d404005100c8000304800d481e1400464851390740b5611160040b030344551000700c40d068424150300f030b880385500740203026024030081e004002c100103000c80041c8042404001410b24000070144510303441045040040504006101090469006290045034204140b089a480b04c218028100d100010741d4040806088054412070f818401840200d4041b103060084100c42c610400007401c0c101e076034405201c141c9400500d000c255412030010402418004200243e00c030105140c0025059000b101c00e0340e0502c00102e01c6240910302c003502503488000717548140d007201d003c1d40c5505030340a5410200f10300a07480c3d640e55a1400b03550300082048901800c054082c3c0741c858240d050500c11500c90b0041251100300da4440140d0001c4480c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 487968390 1250 487967140 487967159
    0x18060912090506030c0301120f02041b200613030201060b03010e0a0c080402030a1b1a030f0108030702031c020106180912030e0d1d03011b0306090209010c0305130803030907 76
    0x1c008280a0b0758243c10b501d400c40143e8814001481242c2003080010780000401148070100482d241e8001e00812084141e0080000400702d49100d401c049681c202264030050390075603140e41c001c40301e1401070040342c1d140748807010b0f0488654000c40c1076648510010890082c13420195004c0c1043e00704150803031505200d0002520b11148220040c130200303500307000141e24041802045e80e600f0542c45502c1c2c19803c81d161400100d146d001280c1c007060b440004904000010045010f0a040b041050b071998031110790313035203034420640001d6141d88030400c0c440381c040c000308480200344001d0000090b41030780d5040707e41d505a042c1c80500c5c2c042d96178960040c01c0001202007028040c04502d410014261500302180e61002d9100200081c480745100010703036140041c0084074200380290083c400000000304040041402051b1100800e0400c100411010a00e00c01da95124005a41d1200c00e0091924292030344d1b40201510000303e03040c01408158401c0400041d80241050802001210b16110145 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 487969640 1250 487968390 487968407
    0xc020f010b060304171c02041716060203300a1416090b1602030d090e070c0218060d050a05060a0c030203010f140d0f030804020a050d03090918060912 66
    0x96200d624140305000102d2120348610312060f017400700480c1d48001d40c12450004850b070141500c0418000030300866003483c8240ea00c000010f010341140c00b00c0701d9480d8a01080c1c00a800b9500050340180b005185107900b201d503540404600c20441c5031a0044200504c201c48400c9400c00e00b42070700d0307801c4650b03190119240f00c3c1c3c2c0406580c166001645d01e50100422442c4a840345501001c0d01180003440548001c10000d0599070040842d00d1502c0c070440040c0007188140304511407410484002400300340590600e40d00320760b00030503801c080003288049880181010300301580202c04201210002202041401840341c0620000c0595180c034984c001e081d81e210102d22020540144010041c101400c0125411389100b60b440280e01c4d8400c2c400305444e2004c00e0f0f00904402d5081c014481030503008a0a540114001c0d41c4041d511511481400002c0001d08c200800142c0000c80800c503003240703540900f00600a1341e07400c529200d01c1d91608815255250410703114000d40e0030211070041d4207c560b2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 487970890 1250 487969640 487969661
    0x30b011b050d17071d180a050609070807082703130807061d090702151f0b0304020904030f11030a02150a0b0604090c051c0b01020105090613020f03100c020f01 70
    0xc04901e00307a00020700d04400d500165500a1000b0700580c030319906c00318000560320700c0741c0007081c1604d400281c042c0a80010b94001d401101e80e0008600303041c1c854403005103c0c0a40351960000e0351140c1680e11110220f1104003035000f1400a003115000400748010b11010004d0000046c00c00e0a0184003030134129141d220300c051082407016503240d082080300d8407008440440e1501c41e032703030358525081e070500403804d508003101c40740d040402c80a004134002101c000d4034103240c0100403a485017014801d074801920080e522546d00400030f40000d11030344480c42d07664000d00c0c0c174140301444007846603d181c00c556103000140e000400048100c100c1a029140d01c0005028248004103903040441c0c214425801000661502d440c0c2407614903000b038086896014175508440c140c0e01050210381c00070000900498019400c00b4013286c003070ba40001c0ca050141194420240da90001942001f0101800031070090301805502810300d520f032040c0c41041d0b400303a542e07000703000c044400c2c0c45042d0848403209007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 487972140 1250 487970890 487970927
    0xb1b0d1a0108190207062004061b020114070c0801020c0703023d02030c1906050604140121020a0e0f0106080403050910020109020d0507060909060302060a030b011b050d 74
    0x4010801c00d586101c040c8100500000517682d5800c2d040500180c04681c8802200c012050500003e07044104014000c40d401503480194900342e400440d0481c0842c844042d0009e04412102203216400034014600c40380314180e40d500c42d9684030806826130700322076525800e43d04408810029030a2817071101d0342a4001a0383c2c01e000316403c20314442d000d0008988503603110714428010050600030421a41c40801100450341c00380718051440700c011844000c11a001070403c000300340035040c07074000c100c4824100c100c60292a03090220400c221448800d4a0304840070b10441c180168581c040140090108003000c2290341c40d10300c0010501d001c1c1a400007003004070701001c02010903484400d40d031000e001103e141c03c020034000e40490141030700850103035001d4240080902005000507600c021200f054440003066941d540700b0408980007884069080001042800b016610991015004d102d0506121100e56600002d080c0300070030625040710390345c0c442c524525145801c80320708008291403e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 487973390 1250 487972140 487972157
    0x1a1e100503090c1f0f02070e0f1602030304150b0f04050109151221090801020309010b01121103010b03060a03050d02010609150501020a0b2703031905130b1b0d1a01 72
    0x4481c8626401134210000400402c01c1015800038800c0c04404020300d0b900220304604e04143c4a20b010403031007500c043c0c001c1c6604d40e26141e103050011054038071403500010428888918100c5c020064131000c024607030702104100010003199078a114071030207010007410000e0704100d071054070b442c04070142d0800444e403940043c030480041c1d203400740a200785082c08202907220025200031b507484039841d0400344141d40080100035012070154001c0345200c000741d0b90895034074a090768900c200c03180340c0c498215a200802c014800e00410f1700c0251341100010344003460f825620348070241403805060136140140d444460400011141d806000141d00d0000940d412040c941000032b99500c046030401080150880e00062030f00c4149a201607041302035824841c0864103c001c0d01c1d031070368001c030743c0c031100c1c2c0920024012404020384030752480b882d416415000b15179001d464003012404010224041d00036a441944080d9040d54003500c0441c20940003c51000c2c040b8000d01d824022400310981000200c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 487974640 1250 487973390 487973419
    0x1a091b0d0f06080610030f0f020418060b04050c092d06070c061409060412060e07090b1309050706080a060504060b0414180c072a06121a1e100503090c 66
    0x1042948001d48c1c4681499200ca02c10301c0880c01805010f800c604150882c0107194003400910f42000180d18412a4108035035076030700e40822960b001e0160065000031035171000b40c421604400c00f40001904a81d100400c003107040000500715400031a0480306050860001c20085800c060140501100080800d05101500c00440c0d582c1c0a0342c031800c0269580110007800340540c95006100702040f1405903820030781c4030402c81d0b002c0d1003080d00c00c03401192071602c0070900c040184508001c8039884401341101ca4a09801240c084c81c004d00002c000746e6031942d00241a50303c038881c01000b420094010b50700d45180461084080c22a0315003240950b491300404018084a003080c82d508c9601d0084d1162104401d01708641c19076412200b07a100035104007101034144c0705503800c4800b04e55055403120081440f44181500f41c81d01a0001006403450401d060818505000d130100f01080014414084028120005d45d50b0307092804440041a000428030009000501c12514810782c00c5d500701500c00b80c80c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 487975890 1250 487974640 487974653
    0x70903030219021804060b0f09040203191502040603052e152304090e0f0c1309060f060306060602010e030f0d090b0f0702011a091b0d0f0608061003 65
    0x4110b40e108441c807120800440d034031103a005403c070344016100510b51a161a1000090090710459403007160428030500b002d10304510118407503503014029141000480403803031090721601c58200c0b480d01301d07912250355122240c4040c0008000540d000300d039900701400034892140b54500e07035800d03120490188161159a0218510032200303032107811100700308030701d0080300c4030030103208203000c803212002940900c031030044040e10a0b20a200c004200708070301e450300d680d5200300024041066800030f540140c8589840e50500c9180da0300c20a0108401107180c0d2a9400c0750120803803000525950b020500501800d8401c11010300124002004082d911000003540c1e03010f0406265040c2900148001d1038102641001d85800e51203850209141004000f06800007011210f04006620b4410140056800700d0b6060b12900c50240c1302c80c00c0c0da00d44205000b5005c1034070314210700302c0e2010044840b0501c1d03184140251403890303140000700c040c1400d24860030400e000e482c1500304039030b000c01800071480 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 487977140 1250 487975890 487975903
    0x60e0f070f120f020c15010f0806040b04030219260c07050d020f04050403170a1103070e030a1b0e0a1109130e030d14161b0c1a0a080709030302 63
    0x9036810101e24100042e00c40030701070241e4903800d5804070b0000c100312881607400110b40703501c5d81d840034480402d40e80b500e001410340c171030920410a183d4028000f04010031551350351650880d000303105075116043c1c07182412201200c1c1c40406c071400210f1552500b00d950701062000050110131703004e58a0440951700003a03844100f4001c551190b221084481c1c21580c840f000022100400380c07040c4482d00d098103024100211030034500f1148220074000441d24440e920419800100a040c0303a4115101c0c4c5804a03180c0c00381098050701481400c0041c8081529408903035074903140020401146404c0c0480396600000240841603401e0600b80340102998080c4241c07460340c5410303079a01c0ca00b007004120440180a800300c5200c254000081c00340e5400f101904480030b8492000c9001c079964984050400b084010008884000398050340d840c0420280e940180e94803034000c00386c41901ca6240c00c40d101c01c00340c0c13004c02c10240d804001140034016801c03003640c90b44100b050610039000c074916240a0348814 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 487978390 1250 487977140 487977167
    0x50c0c010e0c10111c03050723250c09021b010e0d080c040b03090a2001080c2209050402030d08090a02010f11030304050a051612060203071403040303060e0f07 70
    0x790490016054002c1100480d100290394441105c0f0743c0c0507402800a00b0103840c0800003e170503c1c0801660710220040a0418480300e14862819541c0841242c01c6006000034040103201803121001190003010b442c0040c052054005940d44000c00001034441c0c1144124207035030741000d00c0107500d15004254a91041e00c3c50400c188642d803242d5000c4840d108580094403404008014001c840c03100049540c08148642401c20900c2040800407801e03e131403480b45c0f40008c800e00005000b0410382006003040c0000036080c103124203424281c1030032440c0c40d030f040a84040e42d12410403096140420a520100c000740c10030000900380040740903103070f02243c100039050114a040c2d0f0a000b83c414030340344003102070004c141da8503130074a460b2117505d806450000395000c1c801e1180b2081340d290049000c404071400c000b11141440b50f1503441201942000f0320105c2848001c5a040c0300d42c11044d002148585d00c2a50009001410000915401840940355203184d061100400101d0743d00140b880f20800c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 487979640 1250 487978390 487978397
    0x303030a02070602130801270809131514090f01061704020d0c150216050102100e07030b0403051b01020406050702090612120715050601020307020d05030d050c0c010e0c10 75
    0x59140e414000c02921940002245c405450540020004010344c4030001d02c02840d402c04002070291444609811900714001d00b01c01810000c80005180c1203144c90b4880c0350001c0045200500d544000400c40301c503900c0003d842c2c0a441c0b42507003d20713051103020350000440c4400d0032a941000c0c001006440841100280840b1520114043d50385004800505640c031001501d565a1990410b074504214041e69202502c94500c420410803101d451030416a103040c0c0c000c115010b0344443c400b000d0314030b001d200d038242d02640d000030000c180300e01c4103280308600903201c650b555110500300c03502e02a03200d1081e00661740b041c00207024242d440400c03141c03482c1c4c04a841c030034a912044002005000aa094000584220014042000c0c480340241c40220300400100044c070962034205020344800322041401030b0400c102a20042c07500c21078195105020b0b41c200e070b09007031901385042d084a5040d510150081804070303d8658404003401a407003003c0e81c4201402480b501c402c04180d451540820382801d2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 487980890 1250 487979640 487979647
    0x10506060403050c2211180901050114280305060a060906080609090f010504031d0102120d0203220614010b18060309010207080d02030f1b2d0a031410050303030a02 72
    0x45a172100307611180700030400320030032420707020b503000f00700300d0b0b119004981d604070200300c11044900e0094512812641b042c0c50b0020354400c0c2a00a41e40c075880f03012008409131015000300403c25044a01304100700403502c0002d1075042c4101000005021944490100200d45c502481566485003207650020400e0b22905126151861820300340b40141505075220740c41e0a04000c1071503441580907030311102d0360000901d40b040386001203845080e800501704011004102188251906034006c560047c01c140940352006040c07000640c4070720400b5805d031031494454401d41501100d10159500420304021101d03d0150314900e401303040c40c00d00700010310903800400004c0380e00b1020740485040b960302108681e034410000450301e0080d0420360711184427510510009007000c010601801c14100000e15290504a81d502c40c40c84410403241380a9038a58400b140200c100c90140c040c1096103aa40c50218000b200c000210582d114010042e09a002000000700502c1c1c030088100c0e500301d20008005642c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 487982140 1250 487980890 487980919
    0x1418010f030209100210060f05062703060c07032006040f05010b0604120b0601020312040807050111030117100513060b062b0b0f1008090c04050c0408010506060403050c 74
    0x3d00a0000441e00b000034041c01040f050f5006c1755200403040c01e0300003085041e4450701c03500320002441c002c0c0f48e000304080044000c0c00c008104003440000c040000340342c1c1080803002007410898161205158548049501d000b0141c009000d0001d4014440e0341e1043d0400648004c1c1c0d641501078406480b0a09a10501c001d001e421f410840703443e18007a00b407030b075265607541c000c04101000003c240c4800b0f02c5400801d20b558404030813500007181f079915040c5640c8464490b55019403102c941126190340c2c640c0c0c0850241044801745000b004081103178811640b20004217414506120030f5110301070306c0c14040040c01008070522095898010800190b58040d040c0803401610030801c45420030300311040d0315010803d000805003044c0503158030078003620b90681c0900c00350128813030050354429580505180354500c00c8188990080403142224009501400440c0c110360083e01e4414115000007001c0c81010801d01038650007110a913000e42c58140b81d51145510b408000c44440c4c13081c46070108020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 487983390 1250 487982140 487982147
    0x120507061103010f210803010e0a060503121209280c0504060308300a090f0b0c04050307051909110706060f1a03040203060412020f031602011418010f 66
    0x111005074100040e0b503541c4504050104051500c5100c45541c94001c00100c805000c4d0300c000d00302980308090b182982d003001e01062440364000d000000041d9201c0340018255070410044a05110313204000759102040c0f8203080e07807148000d0940444c0d42c07040c41d059260f020b05109411808840b040c21510310394440c5402140200298003003540182414404000c0c031441c04002d00344002c0740001c180f40c0e250750171500c03c418880c1c840307070003680c044090010300c40800e55040054424418603144c1003913071039a44c3d80e2003034180607902c0e101e00101c08a4184400d040420100b0050308086904400384600e10000d42191201c030b02a4001180c0c40f0520070712b500c000f900a40d0306003580070409021070394070b0b080c80c2010501d0911813261400018030940b840340100300e04890041c2d070003502800c0165990703147c0d1380c0000241f11348003085205131004030320704483c1840a45840110b4920072881d0190b50b000050643e4804107200200314810440580703180384042800c94030040c00e0810841e091170511094 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 487984640 1250 487983390 487983401
    0x5010503070207120c09060e10050d0204291309020906121e030d0b04020415030c1209060b09090316111f0e09010816030305280c0506060d12050706 65
    0x141e5031404904c0682d810003030901030307045c02d030351082d0400c1000603a19468582006030665251a1b007204e482d400340014241141e0009150740064400b19940c0c81600004180602031021100001205410001d81e441d003145021000306801c032061080d91110340028550280c040d00c0c4922a100c840502400f0034005c2c010505164100c01c111980910040302094a0341c6c00701c4201d05600e85020075100c0d41d8900703403095a007620b8408080070118085214150020680004240f09000317003881d1608c01002103004400c1e1040c40f4400c0842c3c006249814840703080f10103031102c030558105110048100c0107802c203070000107810046038010690010040f40140c039003058140f00c66202c0310010081540c121300174000c03414003602c0c84806683c4e1a82460b49410414041c008452221071082002c81e00c0b51000e80060000c503160203e16a8031720309800c20325480b44c0c4403140450502e000c410240082400702c40d42c40b42d400e41c2c10090003c046d039500400f0780540007000c010b010001c1441d1045c041c250707000c0e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 487985890 1250 487984640 487984649
    0x2100509151512060a05070807122004080f013204060207050105070504050f01022d0313030c050102100b03070306050c070b09010501141806040e150c0711091005010503070207 77
    0x400500140e0440b0044e100c1000f15100320103903013014003141c0340c184540421071040d0a207540d81e20a04460120120140c042c1408244a50100807a011aa40a000300130030080039280300514441e081881e0707150a5904c800c1d007200741310020012040301c00303208890301d03c02c5410783c0326094242d035150704c0d01000902505034045e00642c0b80c04200850503420500810135194100e560b6100c5038481d500482c0d84d4020b00104549203100020084030740120f01440e00301152840c4c060b68209091050707902244000c3d984240d491605400c400c119070350301072250f03010050740d2940900500d000c08002c02d0366004d01d4403000300515030342e03000a010120710400303031094a035220504050a040a141d400d018050a010b814910860708015810b9460200b174901c20403825401654070681d106003c010080c52500c200226601984c0c516002c4c0315070441400e031066a68078140c075241c070350500f400c45400241110240c080d810460901c420552060401e0040b60740910301030f50380740e65840c422400c04510f41d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 487987140 1250 487985890 487985899
    0x1b0103150f140901140112050601030b03060903031f060c12090314010501261b120a06020a030b0103020913050a0f0c080103062301061202041a0a021005091515 70
    0xa01080b0380c11030142e01803141000b200e1001c01a40c0391042d41581a40307144241e070210f0340368150110314100300e410941d800b00c8141400548494142c000c682020021603100d446a00000304110341e0302d000b000c20440c0c10b4105100d01c40c2e91418041d000e04024a025400392440c420304030702d004078034461390300f45000c1c41d80f02001d10004108900024042c210a005950245605020201d0206050701801d0010b41d804001414080b0f603a503600074034130811000301a001803689890b800108807c12001103117a106d10f0700160f82d030703058034001411207a6031000c4034101401005495080d594201728000b40c01706141001680b030f00c590310048010040a021162a14180b064080351310f44c000d641c49049a000d00014081e1903030500c5d03007002c205080954041400c000c1c1d001801740d107219000c1041402c064104c0140317840d4488420540180e030350462110200400035162100380d906102c4003240c0c00440304144118104440f0458844103d111050580320003c400154088007a5094010344800540b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 487988390 1250 487987140 487987169
    0x14010807211a0a0b270a1502061006080402011218150605090c04031707050313090b03160e060f0f10020c1804110103050a0b0405091e1b010315 63
    0x1445058200b18000c80188158201e10000a60703900c1d800c110341c2c0c2d401d2840100c000480d084409800500035400642da0000d036681d10202c3c4501245e060329511b8030700d64005200c1403170207101a018814040d0401c004100e054028000180d800c9840350001d1303e040040494000065041c0800c8204441c401501d0154001c8080c0381806555100340261a02038454117035503030341c003034603600caa214511008001e5103114840c00b800ca030114026001c2c0714862000d17a49401050261420380f5802c0390402c03010a95101509000c514040040282141e80600310102840c5080d4520b134604500a003482d0090507951b0400c092a5245425401c01c0200204002048042c00d1002982ca05000c001280210700180c0c42c40c46448140140a104907844158000c034071a9000044000c0c00f009026022410388402c0b015072145d40d1401021700c01c1200780c006011008840d2150f07559a058000784841c1c0e41c010310002d402c117001040105000c03c0c0c0c00c1c2070104a105002c03404501c41240d9034000140e511050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 487989640 1250 487988390 487988411
    0x20c0a0b0711151b0309120c03130509040302100e12040906090506030f100b0f180a110c0c0913121e080105060d0b0312070b0603071401080721 63
    0xc48000302c08400902291555001201e201d410408251146951421400ca04202404000004643c03040381c11080c0d803c4403a04071421010354000100c40c3d09941c10104260321640715400d0b46c04003c1000b215810107a04164030301070745403454110b42121403034490382d05100c1b8503000c02182101166030858959265070f13445440d0000e02884c010308d06083c0c10400403c0c0e440c41d000a0052507110303083c016146002d041d01d036001c01881c001e0030054101c21800902030841c0d890040d030751082811a0a0040d907860a02c030319504440081c0c400c00340e005c10922400a52103400134407091195000c0d28000c03800c0d02c6050a40c107913000503440042071640280180c1c506142d201004103504000311004200141c0714040580f075680c024025140c00a030244210000500c858003c907440540150a42e074501d03200c0c100c8901190b000340d0040e910054030740c003403103214201004840028030000b10032607400161213000a200303a4014000004208a50500020003980b604681d0000d0802e28000c20592100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 487990890 1250 487989640 487989647
    0x60f01231911120906040608190204080a150e1902031e07030b0a020a1b1103060c040f121703150306040308042f150403170c070609140103020c0a0b07 66
    0x12903100007a81c01603020b43e0451035002410703100042c034001c03c020304007400d10104680002c3c4c0103100307a840384880012440d40c0c1c01d1070310040024010f1440038200701000c2e81482140210b90001d0700352114034104040031110340124040710385401003c2d42c001d00260500000e490b01015a04000c04200054100154400009000d0084901ca40e640c4075190759071001e48012401030328001c0c80410b90880454121201c0c080c0c14000070b0707110302c0703000040c01700d940701003450050103e4602c44201b4001900340b100008034803500e80200039200e00044100301d195030f03696000000d071446040b0580c02001094102d2400000701c48121000340c100e681d145014180140302c43e2050f14207071008410748030001da43c4149851211109591046511214655102400005050244081e034003010a00c004400101c681c1c0d40525114005a111034452a00076000750601c4c0560740f01c5400e00890f1502003040040a160302584000c0901b401620347c18560081030404105c010010480a8185c0400400540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 487992140 1250 487990890 487990907
    0x60b0a0e090f030316080c0d1509150f0b0702150315041802010c022701080307020109080d080f130210031b0207080618070f0906030605060f012319 65
    0x31500121602c0000712000c1946070b1000303440b48941c1051011440f1400c07801504031540001890401c2c1703241c042c040803a0f030125422100c4160144001e803070b0801480000d4080d080002448c5803501c003c1074a091590020900b007071180c844000d002150010556485d03521800e140c0c100070212950300d00d004150b24558040d11340620303215601d0300d40440d940040c3c11003422209076068440c09a021601d40820071030300202d6041002f10071405038101d403800c031000c034a14000c0004800450f02c03900c8510000d418400a030708001001d600c0104124000c5a00080c01a005000c88032842d0f12a125031503020300407124001e010303410010041110700c21990560295910f00c24440812085180046080341c54000601c00d94500e64004408a00c20081c50324072504680d100a044412039662802e42e5000d0500d190b01401c03c0030b07901d0100304148445800f500350f00c03020881f044e04558402d0800a006000c2d0a07400c40c90689002c0c100c40121040c0300101c1312040303a290341c407102d1180c1e0804000c0141d403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 487993390 1250 487992140 487992151
    0x10020304031e151109040c02150c0703050a0c020109050a0806180601051509040f1401080d020705010903060f060305011107200f0603070309081902010b01111207060b0a0e 75
    0x62409042081d070040e10880001c0c025070005030f96034100b4581a24802030520941d0400700340380200b00d414559a0780e44907155444107141c01800c2c812003001410640a0b000030a45100040c0070020100002d51000484400d091641031460481d590307800100d0700c0328855005a90040d07542c0344081070700200000c81c0d43c41084801103803002242d042c61001c1d2a0308003841002d030410380c0385c5141c0c800224154064404003d0250000861000c48556078040ea41920803c10962000d1001400b080400b4411481c02c040d80b80001c00c00e103490700c80000d000ca0034601c0050089030307454501c00701102d4650400401141c000700280107030044081c0864190340228800c40702401403050011a40320541d200344c0301102c0c0100f0010140e01480d080c04920360006241d4001c0683c1da20030000025210700240c801401c5010800380d0200724014003a084076181c640c4d160500010410440c101c000010301c41041040e0103000c5601c41c07555140c040d01610913a0301441c1d000c0200500441c49a1500803020300c5607 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 487994640 1250 487993390 487993403
    0x60c120f2d0f13031d06090a1514041202010e03100f060512010608030409200403060f05180c190b0414030114070815011403150411120f060f1002030403 67
    0xb81c840c14800f034001d940e02e14000340443c01c0c0e0740d030708020f803148882c0300210702c0340280c8524a0050404000307820384813590804020801142e1070900055030003c445001c00d600c002c046860207003804241a4800100345000703041200c02c0b4510201600d0038010798940c20207030001030000e40c9062010002a181768090140180b20310101841104014040c802c2150b061002441c40c003824444075101820a80f600704083e201030501c40f4190740c80b170780c000300011030140c0c000180c0c00d11000c1803e004d43e04081c001555a000da0b0030540401040842c440d0940401140c0301c80c01c080c0e00000108654090b540203243c4a103010400064020340c4d4800d01c6c3c00c0c40c9084008104034000c000c2c3c0454008001d4450000007012180010b4403021ba11201010340c40c0c0c141041c074600d03a9610004e200680c02241c2400c11200c94542c0703004e2a00749409000701e000340d942002404c050368a4a8035805920050042c001019448041500c0b619000d400600e0108041c00403024680d511401035565402403100b100c94 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 487995890 1250 487994640 487994671
    0x21602090a060519180e160303021b04050906060d020a0915030605090111181f170c03060f01030b0d021c11040207021003050a06170a0302060c120f2d 66
    0x11803100404c1403003034a081e10080b10b04038402c071150070000d101500450000b0b200345c032511541d0140448900b0021407183e0b00400c041001da91b8221107000c100385081e80502d08100920150000220b4503540c400410748030844108040c1c00001c0d0b08595a62009010314a004613550320114041c41c1002500e0282c07206002c5600c40165042c200c402080300c080d0160f0091210903404262500c3c140a0290001c0524070300d03c101c404500d088503014410a030203c1c81650f8061016036810301da0548c00340790559124154a040780c04103003d18804422503041640d80d4082001956038014121109500682070121520303d10710040f02011000000f45c40d0a0b180c0301800c5080d2415000301c80d600c2d503018028410b8600a024282c000c0d1038090100031102d5150200840e608444290810400c4020780c010303d905903903410042d007410030141c080b502c2e4500801c0003801d81c4c5403841219030040c40040600e080d0f41e84010244002e60706010001320703600101001c251905d00d044034254010300d00200c0d0f8442 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 487997140 1250 487995890 487995919
    0x70306030803130b461d0d090513090606080a050c0a091802040504110d05010615030203010b030103110d050f0a060e03070b0a0c140c031e1309021602090a0605 70
    0x11520f07600340000c2640c800741d0807041070f1709070301c01d1600c0712001c0d00070005031881210344607101c19640c200045610406004d2109142030f042004050580000d0f414002061030600001c03540d12a41c088040240a0715481a402000041e074400340040c020b241c25142c0072102c034a0501d403240c5840c801541b280c0d00c035400200d8404e01c1481002100703448031048121161180d405c3c00042e11004006507503e060008000506444400b0a600308511a0000054003400d282c0881840841640e00c03104040c4140b006111000c03050741220b0660f03421822851034084114002640c000201c50010000c2c090b00040000ea11070000712110414400c1100744084138010031581c2c2d0302e0182c00e00c080c1201d00a24007003403a0703440c154820389405400d4540696007000c001021400c99108020f03810443d44006030550042a003e0400b041c8840280741c2c03945420300003600303903209244a0040c070304140d49c0010f40a0480700401c030551012035010305030001c5071030034410440c0108198414240503194464a501 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 487998390 1250 487997140 487997161
    0x20c0115050621040305370306050303040b0f1306030204050a05120c0f0301200309100b1302031f03110306010b0a0f08040c030204060308130f0308070b070306030803130b 75
    0x3c2418491107841c1807a4001030a00d80301910700680150f06000d81040304070307031001c07000ca50048010392035444080c00c0704a000450404019644103c0b003050b20302441440310384e60102c112022101000781c207a80f560b48000b80070006120b080c0982d0680098840300203015901500604101e40c01121050000c90342e4006008100a14034028002604901001c8000745442560305603a0280030f4000079042c0440500ca550701000c11500846284e40802040200c18041021811580c007041e800d01040f00042d0116000c070b071a1041740d0580603004000203504d54131645403a821600d074825040000b554138207160003000c0c101200c040c003900598002050a4029200302d03541c8204030350b2002c1000180c00411269400e01174021103149081070000400769403030b400b840b170103940188a199918082d0501a135411000c41d4425801c1207151142000400e1b04241581c0240e900302041751000c0c3d46400044005000e99000101119004014002c4000c003203204191503e220b6104402a40c03140442c03034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 487999640 1250 487998390 487998397
    0x18020304020a050103091b080f0f0c031903051c06030201110604020f0607020a03021314100501140c1903030203160503040c03060b01020f0d031a09160819020c01150506 74
    0xe5005858280b042041e0b503c6540315010080c0038201c22000c214500c20b10841c26003980d402680b4a9200400081407140144468a82d80e400c0e0401414042d2801011984607282100329901040200035600d05060240e0300315200c005680022149100342c4141c4800201050b00040e400580303000d0f00c0e030804140c0001e50038000c1e9001485640c0c010520402c010455009880890308080c880c5000801038a50700400000d42e2114034001c251a42c9141c04848a0000201902e070211000d18007001607980200d83d045031488849520b690b41c0d200340c0d00c02c918040d0380b261b00103104802229074501b03055041d4055805807181102101409046800482e8a4081980c01920070141884104002400359018024411060060301c0c00c07803000040c41420320995801e501b000c02e882d00c01d402407094072001d40002d44001120713116003a04180c1714541d00704043c104000180090707000800c5002054010000c060b1501c80010b5683e03c3e80c088041d406003c0142d003800300c507002404041698503000058 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 488000890 1250 487999640 487999643
    0x914160e01060206070c12020109020301062d0b070b0402041b11070b0c031b1608030403110108040503090d11032401060c030f0513092a091d060307090e0718020304 72
    0xb0510340031041e840c4c0021f103140944c040d406641d61008a040185c40a0043e080280389041441da03c440e8001880d008a2100040c01c20740e03010346550a00003c041c400595001c0c68000040d204180d0b030301d00c0800c00900244001084605081076502c01c5030f584a4080390406540c03c0540c0c00e02c540d02c015811a5005569043e41140c006020740f000c603a490710054900550350000b2121011080440d10091014640204070140c00008040c401d0140145024000340428a025402850243c83c0c0545a00030f000101d032140340f0f560030050511143c1054146040801000e03035800308588440003032240c0410a51a070b07038281040002818500801d0440c00554058803804000358001404458a600c0031090241020000402180c110b4a521800500000b001074900140059009a42403510480144d1007007110407881440b60b01010043c1040c442c0a090100041d03859500c0020b043c8030064002c0c9982c54513210000501d0200001c04c0f004075804400c1d00c0724040c0b8621413181c1a803004540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 488002140 1250 488000890 488000897
    0xa0b030c0d02040f060b0708040f08060f04322d0a1e0c0e150409050c100c061404140a03051801021501030501050a0b09040c090914160e0106020607 65
    0x4200340541026001132404200020340051555210300c0210801e4100e03800c1551754010205080c0455034140740303508007414080005090500d8052402200c400c40140000c08544103c14400c90004c001078000146442c48151001421680b5070615074030201840198450340d0203484140c1d00286510004501282c018054407401c4103d4580041480e210055000240c00352180300303010550000b410809003170720307941032207241c108000122141d00c090315001c1c2c8213501d000ca101000800000d51010103010a551081c03410041400980740903c0010b0050305803070a000052004482d8820054805d502c10204210b40c0b45051604c50f598100c2240c0080101c2c4003048810f40140c00c000aa0325050414030449001c802c0365981d0049840d400e906c1201c00d03070b441d0f1040c031081c2040b50042d41080d90054a52907841e15090b00d0b808202c059038800d2021041c2e440c200f0405101c0c0081e10025020104401ca90114036a0542e0451200c0e89100b8032650032002000400c0d00d034808200140140200e58 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 488003390 1250 488002140 488002159
    0x32b03090f060902011709010903032a0e041d030901140a0f0e0d02101101051302060913060305071203080a020901170c0d150329070e060d0509060a0b030c 68
    0x303468000812180f0003d0341448407444c1c5e00705407140d01c000b480744100b50308030010402c0400c9150180548422205440201040902d2480c10b0300c203c1c4091200c00c2d205140c44143d10120302c000c2001489504000300c2003110022039003031080b00000080000800c01e07030715103500c103c0002d10440c40c3c6c024410a0ba0000728400356001c5118481d03000c803404003000914000c1170381000d60001ba50740d00c404080101007010a034645000004c01e1051036486081206042660542c503800250309120f0414918801e0480c4000d140038056190f00000146030712404031015561a0307407105e1b15010300f0410885c0000c421000142a40c0e55900903585081c1301030b12406042021540e000b1010100140a42000c00050007001403072070880c0144041a40b01100520815040d800c108481c605000e00d03032900c610800c240c1d0208840401d081950041e600d240001002e044040007507814860300d030f0140c07101ca04007c14080018000310303517a806500c408508020380511503017819101c00402d09519440181c11 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 488004640 1250 488003390 488003393
    0x3050c0a05060417010605060304110301201b07150c05010b0604180f0b060d0c02070503010204030506011806050a030b180f0318120609070609080102030108030d1a032b03090f 77
    0x4009403c214951313800030800343d4031000400c031a600111016181c032000002003403c6818207208580c0302864646400703040300110320a20256100d100b41d101e048542102040742e8201040c0918000b40021500d1880c2c484080140100080300034082900c40e940b07021039500c140d1909604840445603500b80c540303209c0c040e81c007100c0c2c018603504030360303000c4e141d10b50001c05040d079038000c010040302510b00000100f0070401d100c020320305261500024040da02c10082400810b40000d00d5504646444000300744e01211032541074060666580032507085403030000040100715540142612500c0384003c2c109181049503405a503462010213800b1103500100a0f0004019074000321148580300a0143c41e2001c5180040b00e29080c1c086030000d0144e080458144000c40c0d10210200c001c200e910000d6080d5410040d88a80380d219070242180c60036a61803c4034248002144051414500141a0349460541c1d02490100400ca140e048019820304610200050b009110b50b540d05030b0420105030600015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 488005890 1250 488004640 488004659
    0x70c081c0804060207170c0c15072a0602070e160e0105090d0f0b0a0c2c150a0305041407180f0e0a030f08160e0114090402070c03050c0a050604 63
    0xc0c0c42640d07455001c1141c01c0101c1e41c04000c0e2404506c2000d81c0555402d080040d05007030028103420a80315842c06c4080e0b841d083e502c001940c6c0c2c061b401103001c2000c02c0c0e0303481e41086142c4509c09401d480d08078408000509a8010420000b1224008501140d0f42d442c481c40f004642c000700400b40c045030f40310a080c181c40d44140702828407004040c0102c1510181501c84d0420780c031f06c900d400c0b2200c858030700c01c100c0c940f05503015400a221060410640700c0d98070302c00021140754011062044102c0154000c412581c1782c00c8801421045214082c0d510900c4500c01005490304981c00c1c3d030005c0c5140c0d480d80181c840010420301b01c80346940711100500003040b000015124150400c00a41d840e070300c201501c100c00b84413007103104e8843d4a0342202c2045059001c0d00d0394100620301c49a101405401105050304945a9240d9510034a000e0f0b10440c400c02141070b00b0b000354010507410610101d00c1008005d4a080d1345001c0e07038042c2048650a001b4a4100441d840e070b14010076801620512041242004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 488007140 1250 488005890 488005907
    0x12110402040512030414010302090612040827010801060503010b090909030c03131a030601090311030f160305010608011109010c050a06090b0a1d03090618090a02070c081c 75
    0x1401440945460b03529000144803c0c824401c070165900001010003c10011000d01030300c810080c04c00758144095800014118000e002c85c0380c3d00740c0121000201000000021640001d49021031460f803100e8801c83c1d01e101042d040707203843c003085400c0c00100300d080c01141034074100c60000100d0b92030404603405000920001401130480f074402406046c0320140140041c040041e403d41300c01601a1401151841c860111166100012820018040d140e684000710b201901e400c000c4101e000f105040100380f402401443d080c640c2d002d00074418824031144025042124012002070242c1c0b900c43c0d00b02400c071071460600384062402045175035495401203504500d55070040e02540e5210015440301010748030b241d80101c844011820801c581d1000e64860540001c02c2c00b02c4d0220001c428264442d528842d500c44e151140c480031900c2c05000ca054841c04640031005004200d1a061030003c000c080d40140104895030840d001001c10070010003c1d01816940b25a04100064015048103031020350 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 488008390 1250 488007140 488007173
    0xf02030706060308030906150a03020d020619022505030a02010e0a0819150b031b0d0c180e0f0706030c27050907020a08030406020a0918060608070912 66
    0x400d02012000c1801481200d00841c0541035040c0e807403a04814103400c040d402090b001c00a5113010315202940c40300c041d0202aa40d040c2c6040102d5003003800050041e004980518152807020580340311030342e902080d0464001012860030380d4030300143d003c100084c00c1c240141d68040c2d0011417a00050f40c0302c1c00d07540041060241001100a485144940c00d0807000d010940a00314189101002c21690404648140200110400c19003200500107030300e5030321a07009000b00911a02d4035500680d50b007841c4550441c0e0101c145210740d03030703110300c90400d4044c40342036402450703e403c004c0301c005040071481e40810300c448070140071605d0070a038050300105407410103103007003100880c500040060000300609500148140d000501880c000401000c504010000021500300100ca4000290032a099940040e0b000d140035849501c40c0300c1c1103c4490450b401150810f4142c0c1c003e00600e850399209400781c86c1299602500f0b0350300c0131002e4038030006e00d1140f50f25605074004001d002c6501080c6112911 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 488009640 1250 488008390 488008393
    0xd1505060f0603040b04030912051509030d020408070512010c050703030e03090a060c14010e0c0d080909190516120513080d06141509220515090711030a0f02 69
    0x11018030104086800880e0221740c4c0340840d00a2006051f00b06900d00001e00181171820740c0103185644460300c54128003030408004944c8008038094207000d105a448c81203124a0031506c85030384021580d80c40f0064820a40202c1070f00802510940c3d041c043c260351003107130381c8034070b4948000350350300301c2c014480c410244140780000d201c0b40c1d806959810b50740005050300d41d11030018403601d041405903110030b200180c1082e0300d0208031180c08000803544d4882641c04446003a03420940741015141c0303110321220b042c0d200c800c940c10892503580c08503940603801e51418042006580d52203030700700e412000585140c085690000c40b5801c455154000b80e6204401c0e00502a0003001d40d558642c40e6044040428400c1e034803400188003800c180c2d200071440039401c45007112040d141d880c1901d9603201d015900c50040020b99001c000020030100c0001c07841c00203000800151500c540d02840303501040d04c03079603c00c003103c1e0302056106100340c1403219a001080051803805603170f4042500d5030600a000c490a6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 488010890 1250 488009640 488009659
    0x60b0901120e1902040b0a050913031202120403021b0d0b0405010f0c0e1914010c051504030e040b0301050f011e120b06040501080a050a03050904020c010c0309110d150506 75
    0x15010184036011030002c1d443d030303410781c010990300c10481034a581c030301028000d1421034400c1103a41d44480615402c90b0f040b0140d0740d002012410100d4541d84954031680d02d040c00029419060f04214403003d1080340240d003501c00c407050b080f1100203915038045403194440030400100011907196004540c00c1841071000040c0c1c0c0e0000d007400300c1901d40140380d02011591000000f2458100f00801a0710701c0c5240c0741028081c1d041005251416041c2d003529410480b00c0485e201c10050708002d900e1000c00010031414851810749402413060b403080360b5050003903080c0701460b003c81c2014050a0700540b02152968126800c240d1810174801c046513200e0807600100000144640c8107580c1c800c4205d010f110034212900c3c04909100c151541039008003510f6101c08401008101d01190701200d040c0c0c14a003e0340e403041031000086c080d00600b040160350307510b41881c041106826500080b6654441d0241e51034003182c210400c403401300510000b61211046158020f20074400e076004980c4080028410707a00f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 488012140 1250 488010890 488010911
    0x9051014030721060e0a0c1e0201140132030a170913060812030906070f032a1103032a040f080304030c0e0606040e07020c04020c0d030b04060b090112 66
    0x564081c9100322003ea40e0b440e18203014045850b01c1c1c0d254001d0b10100103001c000c902000052116070040050103101c0400e400f9615114800e41000c1d1510310a00b60400007542c48002e6461401c1180c0409144601c2c400e54028880c081503231400c5080c0f40050290204000d03c4e01c600303030341c04005020207240307031001c00102100b5500c0300e400c51140800c20000040c01401d2540c1c83d86046810111050b1007501441040b40d07180c00000e40070343c410501c1c17a0220802100c0e85040e03014081e1888020310002c400c040c00303004004104041c091020300c5548001d50404166440c0b9100d210907140c00030403034600ca50f44c840c94070029541003d60826032445503d004d40c0c82c0a07010303e041440d08069100c0e0800074080061181c5038070300c1c0015007015103548a132402c0603000a41709100e94428841843c10001c006040c16000b40450408480c01410966a611800780b0491700c80307280520000c00b00e031400032510031500b0248240800e0718016402e070341c509841e401c01035500f5000103030310780b210b50b80b50303000f85a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 488013390 1250 488012140 488012177
    0x7030c0501060909150203060a0512010b06040e07020c0a0e060103111204050703030908150103020906040f0c08090d0206010806010b09030709180b131737090510140307 74
    0xb00500d000c64000650010a18002c0300141045040f0040b107070043c8180009681ca184081c0d0407108100c91004560947c1c180142c05001e90820580d40168045400504441c0d15107449100704071550903980d003d04030ba403c0045401c030b6801292118500700000610b40d500076400b01c01221201a021810004170303103003144000c58110360480749900004820010150400074001c00f81120a004e840100000000d41444081c1403202910802882000c1107040d2a02d07030250000030072286050205440d16a400382c800345083c2c3d4414603500c120b44003182d0b600d03c04915030f4140c9002c000901860703442d00402100300d4201c040c4143d07060184010000361062140300b00b0100c144000c0b626061042e042c10201c9114100411101c0d0150b1510011800a0000300b406210b0342c030240c480c191640302016408400150f12106018107081b007500319410f800c0c000c040c888402d4040e560315040e00307441d0400d1000c1004505010340c08104a03080f1281b00200c40d40c051540010341d444c007003030b0101c1000e0488 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 488014640 1250 488013390 488013401
    0xf0c1416060509030702030607051c18020402160c06140711180703060e0601050304020f010f02071d01181401140310060b27030d0e1c030224070c020607030c0501 71
    0x41090383c0000b501c1000c6087c14071810340d0020307090030250309080f00d8111081c814556075400e03040d403550300c0015050346140051180c43d00c40d00130788215112454003010341d1400c6544c800550341410103100028919100310301d14540c0c4241032003000d0410006035100b00001c0c00c0c4003d500e07484042d050090300300d40c408840451250302a41e034081460351908040d18401d81c005001d103410480d00304104005a100c00d0a41c00c0aa882842c0412b00100ca140c001c80c140a00c903042180c90041ca00820022151500d81140c1607a81000e01e035040c1038000700010b01180c00a10b0a00ea501c2a428010020091142d02055107060080c043d1108400300f620120110340040d049411400c5003c15030407002d148012000010403240100c0780f528002d81d03000207540c0c05000c2d00017005c000342c04005e0f81c01c0e40c4603484882051040301d608402d40c0c9002e850040d494071500c0ba104003059030455294040c006507a56880d0242c04c040d102c060300d4048903024400301c0e0307000d10426001d0110120102c00000c90900ca171 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 488015890 1250 488014640 488014651
    0x131b0b3f06030a02090708070806030a02012f06070e01080609072106210605160206011509030c09140c03060a2c1f0611070509130506010303120f0c14160605 69
    0x5101d07d0340380400014015400213480c29019a00c40f080040050b42c10824584541000400c1240f024600c0c110380440c2120b501a41c0a0354051207085c8005143c1140c803c2c140f20000740c0340d419603952048240001d81808031400c90000e02900300500401020041c000e1100c943c003107012a4058880b6144822690070601e1009810761411850043c4a450300ca8150001f076012074404800c00000350003540c2d0318044c081c5c07036a00c0c2c02243c2c0c0e6845060240030080011540500b01091301e0742e441c054003005015403041010f003000c070000011007031801c01080300e1042000030100500c1509006c1d0340c48d004844030850441d1441c00c7c08809041da42c622035441d2140b1410380b071103c520a4090b9000c1101d80d241e60003503041c803840713845540d002d90003c11a5000d84030709460030f94840d924440107500d94000020094054051079001000341680039030705006803c2d039070790b003800101d41c10010b81c42140d80b400c460300c00040f02043c4540d040c0713403244020702c6444102c41f05184008503c1c0c131110101c44080d5007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 488017140 1250 488015890 488015897
    0xa03021308071409090606030d0305101802180102030c0a030e0f0d06060503010b100c021020010c14091c06060902041205060c03070206131b0b3f06030a020907 70
    0x640c011444c0440d0070350307408070900b406400389040c0000420f40d118089051203081c5074540000501da10002d1810034010900305041c1580100d981d0322900007940030407200200203480090507066175000204554a06460700000d04070150305032811540001d082144680c032140b15540c142056450401480f081406204001481e034a8001010b00316641250300d90302070038008003040045900083c62950f0070790166403180c504504203104640868a1401c0b01c0602c80d41200707040d9030514154004101e055840d103c10010340031803a84180320780240b501940e40403110302264402060a83c41301090b641c45140080740280d01e6180d042c060b138025070401025400752006c04018880c04008158014440b00141469400e1445e002900d40c1402409500a00c0313120701c4610800415404010b00e80c0e0913500b11462440d1502c140d101c0030740c0328000c042601c400c04407810095584440e40c021707020302c4200d11152050039003a0390032400b0300020241d5505004004007040940c4400845a100701c42955 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 488018390 1250 488017140 488017169
    0x2c04050c04060e071709030c01050f01030c051503040602160c091406040209150a11030a200706050a0f030612060915270816140f120a0302130807 64
    0xc244000c0740c816034005010410310303100744040c0541101520310504000401003056544002c0c44030300c1c511a10000c140b480d860002040b40034404580c074941a00d10a644690340e465440302000201031081c1911504000b0030070100780080e400d0303401001d8404921030801e10001194031500340c4009260b20080c080c039200c003100c00028402410329a400042150218100400700006c05e00407250501e903402200e1000403203c0074580039a0800d01c1c090130002c110b0b0740c1c41025030750040140000d030a91070609840c0d03001c803441140000c100c0000380e80c1d9990710507003410720304001244c40c28441c0410000340765a0f01000f150020b8030384d194400150040a001c03034410510318018032010840d40444028500d0300840c500d010918429085481ca039181d501611030307103182031420740342c400c02c03400c5a4111a044403076020000c0d49007811080700e80b403900392084412100c0040ea240c003041200e0752410001040514801c81c0650701038030440400144844030725032241107251821000390003100c0c03d4807064 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 488019640 1250 488018390 488018413
    0xa020a0e070219050c010c0c0f090b0112020c060402091003080708030711210304030e030a0c081605030c060c210904110a170405010b0a06110708060903042c0405 71
    0x10060002c001c0c41a000c02c0b8a090610384807180c5031175144001d02c1c100513008101005208802d40e0324806808400f01141025943e10a050020084540298017265034465000d55050303041c8240d1300058020b03c0600540d9445500300b004c01e61005140c0c010f2500300c40d20100108103020003a0103a2842024410b5490510700805000c0b18262044c1740305650000054003002481d41d211801c81e0f04000343d16580301d032903914059880742c8084035925003603c620f00a40c0107124040035050111000d940642d003204128076800c2c5d032076800034000c560f0164860000c0c84907500f0b056000300a100260f0069130038042d44440c61603030b01c5040d580a806540760110310303014140361038843da0440034500340240b0f1810404203800350255040300c906007134540e68000000c0900c202900071107426140180035000da90f460300805402840c000014100038852043c02141d006000a90ba600034508200150b042500d003180c50603521690a001c085c0c00d00d01c5c0c42c0e40101d0280e004030703001d001d2032241001c1c201c0174121 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 488020890 1250 488019640 488019643
    0x7030309170a05040b0c070b0c010506041d031204060e032b1a04020903010608030a021b0901060c080d0e0a030504060210051009110c1914061b0a020a020a0e0702 71
    0x100149901c0c10400307240b406030000708550840d00e036940442c0d12440300c1191141460034540c015101c4944c005041d50130301d901036001070b06c201001c4500700074880e18000c00b5110800c82c1c0850300c405500c00c104401201d51001c0800e60301500c518070208180e80461001c0c0d06540140e03002c0110034000e43c40240180b490440074250b14041d000c4104035914644890054941c0c01e1031059005941c0002c0140250300c00790400c201405c03d2800f220f84c0c2c3e00d0301020095592042c0f0001d94108441242c030040b5600d40103030454121a456a1890b02010303150b00d500c4c609600c4002082252651561031a0700700d40244110401c090003034a445440703030316000020b4200320060807800c40080c035040400c46001e913048408001c3e603801c1c010020702d40a6101355440144160030341e0f0b0416200e0040c03012821030310088408565482001701048517505a02590744d00c0b2003e55410a4128000d14814000401e504c041c140011062040710480c2040b0740100703c0c10b01c4035822401c6c001d810201000440c940 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 488022140 1250 488020890 488020913
    0xa0909020703080a090f140c010201111305092e031406041a10031a0a150e01060e0a0b0c06152e02010b12070503011a0f09071407030309 60
    0x100044294074102055030000c21801004190b84045a60f07280d19105000c0010f00601d1010f5100d83c160144101c4007481b15541d45c10851100d00640c02e025041c081c4031803401c207903154031030032142410241d8141001c004003110000d050541010b02e22001030705140c40c1d00496210706107588406044503096080c2006001d031307074030700f40c0703c0541c40038042c131000a1060802c0c01c40261304015080158030341241084c00744e80140d00282207065454000b05020380d011100b42d002d010715200c04c002000c80400000e21259080c400c3c810358a440c60010004980103045440e52640010200ca02d62900c5000d0700000c1e410541c0c41b1507040e130140c0204011070411000c0030450240c00c4950b0080c00b07030000c845a84035966069102a00c4014030340c00c460b030038002d4002443d40c24000700000d4000056072000c2d9610080d61084070300c01d6003040190300b601401424220704a80c0064081c0001c0d0200c3d0081c030407907100140400082008130003141c401c000e400c1c0040e002c401d1107560082000c10301030814141c580b8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 488023390 1250 488022140 488022149
    0x2030709050f040b190614091018020c0703060515040b04022a28032304050d0213061418130f0c030c03080a0f08010305030436020a09 59
    0x525107424090290700281007640e1165021400b051a995402d82030782112031104900c1c1411803c1044c08a12400040d4400c500740c8070070b4684c3da0450340c9101d40700414000074455840007503003142c41000710803029002484c2c03444880084442542e41ca590b154200e61048508115524100c10041150300e4580140401110101d0342542070031802401e500e00c16521005158104040302241660b8150500c110018005000b425403035069039014000040b000b0401c0440020744903034040101c10101a03140250340080008143c1414100b40030300c6140002080c051340c3c405034441c440404609580541d00181003400d00300307114085c407042889804070246d285c003a040d044100400000000d140101180c0319004000c04003c80018100000c0600082e040900082e10f4401702005004000000b0020a020b99070345c000c541030600c1c01103510710780a010007442d5410411003044103c682c8580c08403501e500b400000312014400103d80320301c284401c42011415004140c1d10011a0021034400050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 488024640 1250 488023390 488023409
    0x80610021f051f18150306020a02030717030f01210506011701060602010e0c0d0206070c06030b01350c16060b0a0b0a08010e0c0c0f01090215072609060a0903020307 72
    0x1141400354029040c2c0220b102009a59502d680717141141c61405400c200440d000003045558445000000b5169440000d045e107001081501e106569a06c100480388181c03c2580004482d90030005c0400e2800300038000c124081200c2c117601400f01d4401c2c003a440c024003110416900003a004034510b820f40d440e65006009591406810f41c0045d140415140f840745021964004c1006a600c0000e5240c0036540703018003c6241044003254250301a4081c001d80780003602c6052188440f04058144000d400102240301000318071a0101100f04103085604500e401d0549410309215000d070851216198100ba00d103180c45044a070314a0411f2010300303029120400710146850150030000d0503190061103010520800f440000d80d0552001c416200786041314800d581d02c141c00304c03006502030402000305a100381040c032052b03408241030104a5044590040307100071140310040c801c4081d00440025600714031003c00c140e006a645540041590103055115840e13118114010306190003829045442c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 488025890 1250 488024640 488024701
    0x20906061c0f0b0619021e060f07140a020d0306090605031f06120302030310090e03031909020409030c020f09060f210f10140c070f02150415031b080610021f05 70
    0x1043c1000c00c0c0c2592110100341041d80301d03140c40c81c045404180c0e40d400c8019552f408101502c1c10f079400700791540030400035035042c0011901c07003140754103d452a12429515912034090701d205c00f1840b400020741e80859540000e042a034a0104002031011900204c0040c0c000204100c0316802d0f91464002510010704100044c81152400c03e643c0d1101520549803141813519403416915190005c0500f0381d40a40f003400b000c0d03058540a010003440c1842248907841030420a18141071030001c2d9486030300700605001320000c011061100c0801441642000015100162000c245003000940403041b0600d0041800c0302020074220225082156400505280310007444030b6801690213440a464000b200700d0341149007440054041a91241c1440c08802c010034009012401d2003005e10662110341c27014410a420407ca81c408252011004804500740d4804100e46040211b0b2000c030316903c0d07004a40a00280f6144c0240070b04819a6a182c0c164840040120f010301d42e240002c40a0824005030700e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 488027140 1250 488025890 488025943
    0x603050a06031e0c0f0e01060f110303070c05030c0d08060108070905060a11012417120d020c0304030813030c05270a150b07020906061c0f0b061902 65
    0x43d829540350003d0f05074600a40c50014026030001c04801000c09804c1500c00664810816041c2c0d2002d101d0b81021603410265400440c0c000e484080074106050040c500d10b9850600640d054003102c00c05035200d00c01409645c05404081061003490051038030f500038245410000140741d082c1c000c1400c010814145404c00ca141c4449003516040c0c3e00c2402d1902c22940703164070260042c904840381c0307150b40d082c8605a031401c003100e482810a840c8500650301e488a201142543d0b511103281008070401030070800201034043c9030f405449524080e806a0703117060f5407900c6559854101e6003140c0007803661200d0070000c0200d0200800010481034406001021038500e4480c10030380710125000c001d841d01c07400a090905244e0024240349076030082603900903103940b0f034041150000102240034188040210390700e40760500075541007040310f036135192606408445030300c00b810080c8940c01c0100c0e19190640c20550310340e8081c000c1c8410450900388500d1510400900d844004001c00c442c5070b00c032a0b081c16 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 488028390 1250 488027140 488027153
    0x180c051002070510050d14060301050a02040e01050409030513180f05070f180810090b060306040507030809011205150108160207032012031e090f09041703070302040603050a0603 78
    0x8030f420403a41210404240802a28284a45030707005406606e0184104400c1051080c400d001e84e2059000304183c1c2e0341c2d00c800004a00c2680900288949440300400c800d281c1a00094882846460a94180001c0340d0810745103c400707800549400c8510200b90421241030322410845159909060106051104001d0613070b250251905040182041140c6110008181e04000030030300d103411a00c028000041d03000003406c1070041142c4184400c80451060324000506e00d00440d04040905441841c0d035031401095801030840c54184040300c400d001d500900c0b48100c5100d10401d621000b1450300f080c000600e031003001000344420682c0418820035180e400079501041c1d9500c00113000c044012640c0900302c3d0206500c0740c980c4902d108110100a032402301c0504114079411080d012503480c00035150a4a00070300501a4100c80c0d0b1040001c0d0074601420503540040c020421030303210032907410100049502c102c0354070011076000581009900c1e414410b4590006403070b2001c0028506541d00c09 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 488029640 1250 488028390 488028403
    0x220510081b100e1503070210200301060819020307030f050f0c041404021c0e1603021f0309121112040311010e0102031605160506130b0c0c04180c051002 67
    0x201041441d1080d03d005450300000c02c003a189031240100e8480c900300030003d560711007084a40c0d0310141480104620f410345482080d40f606514441141980e003024003c07105060000c181c136808110700c1d110900881c039144000d6000380855a030100d000c004440c0f8000a443c0080d000200039081c50b0b040010f2804860191400c4d64900e21201c074803001203c001401034001c1051160051410740710011000d85650702c02803041d07810030151500305070a00c103486030040d068031019410405c1e004c4510304414840da504c0b4030b100047d0070f0008514417152500081d40240d41042c80c08174150094240500c2400c10054084170840c080301c0e45018250360350008042441103805043c40901d06d20a6282c0c1c0c02482621100004410420307c0b110340ca04107960303a880404803058505800d800d0214860910100726034106850f01c801c2e00801d0715005071341034290302031005480030b401908082051a500c17805100000c8054202d0912911024140301a41c0503181c0d1200f07115800c1d142c0345050064000c1001c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 488030890 1250 488029640 488029669
    0x507170a02090105131706090a0b150d0f0b040311031c020903070e0a09120807020a11190b030a110a0f14070c06031b021902220510081b 60
    0x540c42d01c10600050b03901d40103203400d04606006004010585151a1607100c0f00c00c18010f045500c281c4a0f510071540319511040c02a210008410000d40ca070820100303a00c0300000c001c0c2103415250340c1d588660200c90100c41f0210740e000100700501041c5540400c11200e01f4906101a600d0029200c100c101100c1c88502444003103500030550032020380e0141b00220040440802050583c500450303101300418078140c3c00c07210303c1201000c44101074820351000c0c1c4100d07801d0b0020a00d0780c54a4951a0000c1c1540350825404403091030012000e8001071035281c0149815180a0b03140d040c1540c080e015900d5a000202c2c0030a800e003c0100001d82c070409102e078030103480c140500c1c0703403c0300c1207103902c10b03c030740c05001e0311718101e40e400040c20580c1030344140c2d03112541950150304280a540101c0e26992118015500750a0818220f0058605101c0d409014441c0900034250413010f1071442055680454400040c44991202006100014062411304008030160b0340304030700c2d003980001c4007035582501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 488032140 1250 488030890 488030911
    0x3160803181905131d07082e1d01020d0606020705060705030307050a090302030a03050d0f0b1f200109050609120307080c0c12030712020306030a060b18040503030703050717 76
    0x40310400030905034000e4803c0c621400084900405c403800d21070741e410092107403100f148602135600c40144445031001094103400800400742c03403030114202000e4101c80422101a091210908642d15000d00c0104201d244107400030030a40d143c030b400a414a01650b001c0d9000d070000b004034000080340407040300e44c060351a00b845626900005012941c03088640c20003034040c032800e042c1e0801d04d1b400c90b02401468044800c00e0000504440820040d180307143e05094004d4450a4400002d08136520304c5000b5100518007441240c0e032900c0b044c00c00d0903415084a455035507030805401481001d10060740e014027500000d00c0c910101512201e000e200080580301009240804100004001c00496031009030100c00c503200071185001100c2e8640c000d40e200b80106400c0700480107505540d00903203100b8240140517000411080d10307110b003d40a44c03808164010340c00b0714070300c5480c00c03600441030040780108000c54803480c1070b200290450313102400003000d0018104c04409955003074505254480142c92 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 488033390 1250 488032140 488032159
    0x1914010e15041107031b080d0504120f021c03020f30070203040519090e0f0106060c0b0a0b0d02030a0302030910081618320a0501080a02070203160803181905 69
    0x20b82c0c46ca000c0031040f0028007031400003c0e54a4500e00c00c0c0c100c0343c081d40c060012402080300c640b10507200e032490641c8904c0580c1200101070f0784145444114020401e05050161510700b40c002100c034a0351004400c0c2d20b603c420f482025986480644000000c804000780d95000c0e03040209000e07589008500c10107105244243c050b110b00121003000c00c0040c160482c080c044c0656005800352a40485081409290300e012800201c1d00e11078003070004040e40000e904c04441d102c40100c4e1025006903004550003100382e24000006072001c02901400c54060740c00756403929000400c1000c10b0303e0611411003044504411320026950100440d505441141481001d4030301802003140d948500743c0c08511b06015070046640b1992036076607410107810345210a0080000320108000414070035000c1c0e2400210300d000002c1c0c0a84140d030050400e103000a0844142c07240c210a40400004590020103181d0030114540180c4001c1c1c101d000c141200840e0010134841003900005400041e620805101b2454107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 488034640 1250 488033390 488033417
    0x10b150f0f04050d11190f030303110910050706150b0d09031808010b011b050303011a0903072c0c030604020d1b020a12030b06031914010e1504110703 66
    0x49400910000d000e066054040b820006105024440c100d0b00442d00e10340ea80c200020f202035040207a58040c0e102401c7c250550310200c0080144804101c0040f108000e007444555984e80303803843d071107401d5031000c2d41e404061a00300b045e50808030b0081100c038400780044c0151660328040c2e82514180384c0000076034084030705017203803407001104d102c1c1180f28019101141d12030040d000310b81c02203070030303200c1c01e500e040e11206014507003404140c00360494005000600909010245541302c3c200e0941c120350409540c0c600080c00c1143d0f59110401c5040038030100c80c0c00c401d850900c042e03080846001000316103000c0c6d07210407042c800102660300c1140c2c005003200c0c49084a6000b85000c6500425a41010441c0c003006940e50b0103500065807071001520480074242c6c4a40508840c40d10050421420754580c0c0c514240c2e0301a880080d80f140544032145000c00e03a03d5415258000c00010840859a050009448212040d120f50460040e0300b40b0360010782041030300c0100d50340d4950500d8040a01c0182 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 488035890 1250 488034640 488034667
    0xa0201020d06090501140904082d0307020102130b070506070f2c011b11010e060c0f0106090e010c0206130812010e0603070501030b011b052d010b150f 66
    0x64000c075034903441ca00a800b2031441c1059100b68103803503d080f080c140f803078620740c100000c0c09412500100301040421003800c0b00401e0110351003580750719220706c0e0364021101400c001550000c86102005079408180d4214080551074540300034500300c03280502c1c0841544071152104001040c00050bc9419980c0002d0170b031207052144400003402c901c40750750740c44503889030824035004541d1b603000802e4600440340310414180300405280e40310804c0c101080202005460700400b601040e68400701c280004442d900051007400740d05641c0c0c10000400701d08200c3c9a40480e82c1307801349058a68501901c022245800041039900803480d80a200d51a41c09031070113101e06c0c840c00000723203218141e501c000242c01035600140d90003800d00318181c4070b420b80c03144011812a400380d909540010500600304804054074600740c99618025025612282c0c014005401e112044003600c02c000408204d020b80303552828421510400c5044a980c5407818801d0124000c42c040c441c2e2151401d84001040d00300d1001c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 488037140 1250 488035890 488035897
    0xf03100f03080d1e0e010b240307140706090f050d0503010617040c03020d03180b030c03060111100c020f100e0604021c05070f090c030504230f1c120605010f050a020102 74
    0x4c02014040000c0300070501e8080c00703200d0351290140176990a900101140e02005144580f00403040b00d045035542103048031050007000429102a030100100008a0301ca8026100400c2c0a0401c0030b43c15031452a080c0e16003c8940440000c0000900041c48a2940022454112640552170100c251a141130100c8041a142d000070340c00603003040e04004250704190454103020308180071320007460780c0319040c1e0258842155980840141000007580543c0100c1542c84010702c003400b2030f00d800007040240c004844404201c000541c1c040c500c81c2c44007040c00c01505c2e14032400150140034090390640400d0791404050b0000703200300312040f1b5070119402a060841c4101e41c200085a40c80e90b9601407066410b845401504182d50910381d0403a50b01d406401508d0045034001d00a10400003003552810352564250511886d42c080c40800480c0114204500414005108410889041c003030748054100e03011030316019012420500204444d03a004120504618894145140d031002a540128024031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 488038390 1250 488037140 488037191
    0x615060c010c09050913030905040515030105040b0114011d012d0305061503040b060103150513140721051e09010b09070315030f11060f03100f03080d 66
    0x40ca0082000840d60b4440240c3c000c03500c056680f1045502c448914482030021200054007042c50300404003c04e082039440321354045140c807224520b4600003000242519000d4900303480740000304006101d4011840000d160146003401c1a05000c951300b005603225140785103c003414000c141c107040d41c0381c0e121540000d0b0b00030140d40c107481206c0b22103c000f900411060f11387c2400364a070b07034140300c40c0c0e00c04c03010840780190740003c51030446550f108011806003540744020848000c21020000e020380710440403100c0c00d040ea01d0b000c0703180210801c0c6c41081d0000181124100070072071804420f0002000c00d060741d4160b00c5100403c05503146511a204e0f07000501002c0140742404c2e081200304a0198071034069818119490071041d00e46007021010340ba000050704000301442001000080c0c0107101500e40c0c1846600d0b0800002141000a01c494101c030b0100034040d80000100812a2192141c075005024801c40c0c052002d415510351101d1030048010142c40c15030781c0c030301d036221040040034901c0703400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 488039640 1250 488038390 488038393
    0x50c040605150f0c0f0607083103022109040e0114130305120c070309080102180420070b0f0702070b03061e03060a0c0210050606190e06070c080d02010b030615060c 72
    0x5d1504c9610303c0e5489800f1558100015104004185482d05620520032403070319084c00c1045019050f0071200c0040d030b03a01422000d5209104104c0c0303061080b22030681c1422103071200a03864142d0b80d0f040c003091351001410708006914000800800743d074100b040030707040f800d910141d0503142d150f1b18042c2c2e41d81c41800910000942840c00f00003000c02c4420062440c00d200396640d8050594480c0190300784d00032001910100e08542540829a060903800440e40c41501944000034400031040c1460f181d11442d4140c0341090705e40c080104134007504c61826003101d8144010200145000e2aa4020f800041d100610030a000075881c85582601d01442d94240401400e640c01d40c2070450103800102545100200903028075a01a01c030704400d4803d16215540c05821036251284507004261511508000034084c820424125015a10f69801806806105000301040b50f4148000c480c54003180807204411a030400d07100710401d4601281c46604178886500404440c2c4101e80040c10034000c484200d601d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 488040890 1250 488039640 488039653
    0x9060609050103030e1e101701080604021206100e090f2b030e060105060f130311090c1303110a0801090605070305010501090e010e060d050a0f050c040605150f0c 71
    0x30004690240e8120391180d10381c0c00c4640c1d08101413054a8034104040305207599003c502034220300309481d00c000b1820f003918003810801640c4030100c0c4007003020b030408071455001004020460030058603064801601c080241a2450022480c16009485014480d484206440420301d0b4203001c0080f543c42c51456020340781e07524010f0416011b9600b0044000c141150302c1122070b00018000e00ca102d881c07500607005440c950b070800c800d00c17a4a0b0310445160050302810401c0c0800d0030b40d091004d40181d481035021900740ca903418100825441e0103420410340e54010800003038114401441c260071203031301103448400c100380200018003041080d480b41589509040e044010490303d507000c6442041151070820050741ca80004441c010321074050000001070340c80052003c41c07206030620703070301507001420200294159a16a4200a02c112040340c2c181d050740c4000c03080000601c440c0c01e01881c252801c00600380740c90700040c005161800d01e40d05454001900d020326200070400c451104008600302c410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 488042140 1250 488040890 488040899
    0xd09170324041515020304030f0c08121903090c080d0e0414070206070507020f060d0c020c0306150f030106122001020d0509010e012d120209030a0b0a090606 69
    0x84a100c1140800034290030001801145014400d01c00324141840c401c0415900380f06090040507a40b00505041d0306c8144070010025410034410081c651203241c0c601c2c101c510b407445c1b5501e0b100c18004a0a4008400c1c06404242003d100c0f003070201d02028600840e00000300c0c100394880c5400ea4004034054051042c141141c96005400c85034916000e4404004030071210003410f00d80101952858010381242c00421582885000a4a5654001808194002241c10002e89c0940c0041c084020464540c1b0300c2500f4180c06000c5030b1002c500a0340640303564a0f0540001003085482c0a940703202e071140d0403040c945910258080805803559010310384000b4036504114402d540d44444c003519540da082d00301040c5500c0450000e92040640d110203040800150045d240071400c6c2d01403a0401c51906074170139084040c0303140a120b005080050b540c0c60300240e500108a81001002080d42900402c14243c3c1c64400043c4004065003060700da40302919410881c50140110300030250041d82019400b04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 488043390 1250 488042140 488042161
    0x108060d0212070b0405130506030c01140c0316030314040201140c070b04080304050a060c0b06060a02010b04050a0c0e150403140709020a02060f0f1306020d0e070f0303090602030f0d091703 83
    0x70648404035186c1c1c1d61f01d180541c010080d580b040796000d0f0141c204000307001c2194000e20240002c0000d8089440c01c2c0200307202c102e03241d60040c1011103034205c10000c981c81450b40510075214020a22959442c06280540020700319105a00140c807590b000002c01ca2040a000c0c0540360150a1500c0301969680eaa82642e5035070340c01c2070261501c41c91008600180260107000030705203640c0e2140881c0c190355a284204405500411180419035480c0d040c92586590b9502ca950301ca0100c10301d001400000017000140011369544000340140d290700d541c0035800502d001a141220340c0305880c0100c0c80d00c070070ba215050402030f034000e21030395001155004e0740c41d0300425228804e6840014030f01290b5940600018030100036142c0c40c00d10600401c0c05004941c45800824000c0d084240200794241100c0d682d5217081312685c00000c00301500041407007015480403804000f495188000c40c01d01844182ca030703c0305d1040100311080156151011070400582c200785c4804c840c0800c924540300d1500b1100031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 488044640 1250 488043390 488043397
    0x5010314010e030406020d0c1104051f0609030b04080903120a020703050c0103061d090106051305060301360201020a0b010315062103080417030c0a0e040207020108060d0212070b 78
    0x8100d107508016030601c0030400002070310100c1d04035900819441304041e8041da00740d03841c10425201040340d0035103004541c03190300449020304441310018a40d2007090502d03480b91006508440204050b090080011030510a555500282c0046409a864403d0300000780f9100e4900400c02d00391401191141d40c1d260082414001c8a0041c4181d402040f1460300450441c4d0f101c0c00744c10400c07800e110403004c00b42500c003051544508808000541140c48000091000300c031589091025605e0b01c1c1040003a0800380240e195035012881510140c0e484240c1880706080040000d5040c1d03040d02d5000004e580c820000709840c0d541112452155584a00701441da0010424500074414200703580001d410700004404416560100d0b00040b0001e29542c045514840252066503400304d290404005140403000441c046c13807245c01062b5842036408009460004507004140c81a8810311a401c050303600481a40c3d481a0129154405505030303100080e040c501c1d610f4500c900b8420013001160141482004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 488045890 1250 488044640 488044673
    0xc07060501080105010e04060f15092a23070206030c0304020f0d03140a032019110706050c190c17070b0a200d08010608090303091c0504030501050103 66
    0xd0060341e0300c80180b40d0a0310700130310540100046400001e00401d9480c0c0c803403d40c0b040244800b0a8006801d502c218408005400000750075070f40721300d24000000d00710580080500000c56401d04003111403409821000c0036a4210380302a24000340c2503030074856801712081c0c1035004080e15101c1c201118040074580040310100e01601c5020b081445a04e4589111300846905586d15081c0940d000d100ca0300780c3c0c0044001a007850b03110380c4c9061078180e0081010100c00d404481c82c41d168880822288000040c4030300c40000d002c0d00c85821805000086800300a880590400680d21200050000c0c58005080d4082050b050742d4031019040084070401c900840f107982c0d103510307010080030501c1a1192003500c90546580002c11407500c1050003800002e14095580e0104000503411154050402030700398014000a1754050051003101c0c4c01204058010b5964002182580742c1180d413503640c0d80e6042c8070302900f0040401c0d20000720f81300700c0450300503580c002e00034015940d42e46010128912030104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 488047140 1250 488045890 488045903
    0x15070b04061404050a111801080a0501060b04080c1e0d051e03090112090309030507090c080a0209010203090d06060f0b1c020c0a0b06031011090a06030209060405190e0c07 75
    0x8081070103061140100f0700031a0010050408401d103540d07103100e04851864615001049099043c0c60340c110344111a00811190b00034005880041c076105085841c40e170071643c10b03220140403d001c102c00000e5406003401b41030b1000d2000c024842e280e039000b5809058801c3c0d00100000c4000204035000c40c0c981e051203240a0810f62241c0141d14440d168041e11040d01d00180b04000c1028060315550482e40071180079007440d0000a880e62a901d0074840300e900201003982e29122070014081d0f120b0101e0741d0000400800310306045103880000c0d10b0340309800c03205109034500a819070a102c4540e00160080101e0b40b02d10300213566401200020b9003058442013000030820b619a409041d00d80221104c00d440440a89000700c51960b41c0f00703042e00d0181070107425110b41d4860710040c904900c600310258000d014055110002003081001c014101d03006402094014011400e158032541c0c1a641a580f040300c0c0c0c1c0c60500150391151500310031a070700c00c1e80324424072801d118182c0108401440311a00440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 488048390 1250 488047140 488047151
    0x61b0c090e0d090e01210807140d0806090705030a0e0715020f10090b07050f190c02030c0307060906050702010e06070305040e0a0903020703021003021615061707031115070b0406 78
    0x45160f50244c024400d9101c140c040e460004240700c035403052500307528071800703031a818040261103a2040c414010a0b0164942c0f1000c601c000a5820042c1d10760300110840301e280b12440c0601d0010307c2404090b09001c0171649901040c580c80f41c0a02005001d8410400c0000c14030040c40c40081d614941c3c0800240e01e4001c000328841c41c04e01d280601c15410b42c204008209644480c5802c64150348101407c007284ac0092241c2d01e40181110303400c08559409030350701220300c261801010b0400d140c603c90136100b50b10000e410000b00f40c003d02c800c000c480050500c1a219a0b480c00181c80c1c1d00045000740b0341c41200006c0b040f0425403c070020b8400d40d90b00210342c4006981c0c421056088540505001d8050380c0402d40410040c80c0034403a1b805040e1041c42c015080000030002c0e001444141c079000c44101c01c001c4501c500311480b5115078402000c074801040e0140b442807000b59160400340c08007138114000b503456007011781c4500c0d00c83c07190103070600b40a5070344201d142040308a144003a1004c0784c0c4942402c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 488049640 1250 488048390 488048399
    0xe01030e0f2a0609010e01020a06020d0c0f08090607081e0103050f0f1207060b04180605090d0203090a0b03040c171006050907020d030506030f07090203040204060906061b0c090e0d09 80
    0x300c000001c2d002d0040e01e80c1d49000c1c0c5400043d50380c41d4100d00b40038110b22031078444000007603103030000d06a96241100003007024161807202400707a203601c42030101040034200c2042816580056419004000e5041c10300040c0c940b10380500588a07224076150000c82488000010090b000841e58002c000703d01c00d80b800e204141e40c0d000d03256003040c0106030341458140202c00214115900000c0041d400820000d52031008210076852100198004d407900380d5241c0c208094101d0900a01290450310b101851500c0e00803000180c02010502445032915004030000b400c0200070b901c41000742400c0c00c42c0e120400c7c110aa055510145196000007070303401c0070740000d071134200007030498080c5445402500802e40007030780850084c10003e010650500c5020340501c4001414840300b0060a101403001d0b0380e914050041c00290742c003651003010b84910780041000b0560b4001421000785d400c0c440c0e9030651840500f40342e04a4080e507005000d21500d003019040c07400400140d0303400d06030510f80791800f400b580c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 488050890 1250 488049640 488049703
    0x110a0503090330130302130903020601060e0d0b0406020f0310080c0901031208041115130e04051f0b04060e01180c050d0905210c15010b09010e01030e0f 67
    0x8803120f00e106060903a5003c4004440902070180d000b02c140480b1071072030782c0f40c0002d00041c50388013142c003045136038034585800d066040c028240900a5030a0040d5107103c0107001c10401002d01102600c0d550f40c0074081000c02c1191b404450b07140000880030390312410045054115051584158800351160340724219079410540c1605040725040b0400c1080020020130545500d100100b044031764035a41101c00801b81d40b0f03002107054520354a001103441c0c105c42c203140591108035400c680c000310720020801000480000711000c0c181001101c9166075800d243c0c00c44050440b14407039a6005003031220100c0c01c0c00340400b80314122819074403c1402e0031b40f81c20781e600484150181c1000010001c000440d800107071500100a801e208900715a03804080308038610001610341500350035101c0004258100c0b500030403040c03140c00780c04c007a84041545048445412442060503035410b012200700340b1304250307000b075014000c404913040a40c0c400c105210f5035241c030b07011160800c501448925040d100320201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 488052140 1250 488050890 488050933
    0x180a090b010801030b0c130801061401110a06090f0501090803070e0108100e09070905090d030b0a0e04060b0a1203030b01080112030207090203270703060507050f0306090601110a05030903 82
    0x8042c1c5440c500c990a545500d511150000c0209800d08000c0100b91150000c0700e1282c0000c3c1b00010001841c0c0b401e0116500c0200c0881c0c0000d0704102d00a1608262500003051030329181d039100b8000101194140f42c11903000d400f403a00a00326503e40701000c070512181c9030007544107103426030b03400c40072518203801500d2240d41900d050700c60000001041c4002d5400e981036607040f2851808548030b9640e00c085410a4810031250001d40740c000040300f1030303081d030103001d62403000d1401c0b20043c0700300e428011400040c0d140180060b2000e61903661181141d15905910405404c8103110480c0600c0a0304014000d0702d0004006800a05160000240a40e16400300304110398182e0261070002d2070302d1055406504003410f40007184040c03500c50100c103215840d045c049011210050010240355007030031400c40e9070052850041c450208210613003101c1a50849502ca0300c100d6400b0750b2625000012618800100d0003104503125185d054414054008068641140c00720116152080c02c066170103648503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 488053390 1250 488052140 488052161
    0x1905040b070b040303020d020723063102060406020c09090309030a030c0c1e150f09120302011b03020c0f010c050f031503120d1424010c08180a09 64
    0x805100c0720340003541d41c1034225000740c00380c034000d030a00f010290b4040481e4050042284c221202061101d0300e803104800c0c41141c1c40104025011030704d0310701030804140b401e0062140403840503510111000459049115142e90007612507911140c41e600b0183d0385d948036842d020300c60102c00c0000340c0319100010840341881006005008880040c0d64141da4074050140c08603049092104042510038100b00601c014403140c108000365240380030300d445540015446001d00b000305070b05400340501e410a82c10012241c00c00551000741005040403801000f45000c050b8100d6103220329090b15079896000f512202e1000707000d07031b000700140f140903c0c22103606910080104800340a18078189003044051544035102603400440404c0560019092042c14201034400d15008500200c8a242c140f25001e900000c0c244034240314200b1803800001001c0c040f4140ca40110800c00001282e4858110a2400355209041e103843d92024081c588000c81c544413410300890b0610000103c40c2c000b4000c205402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 488054640 1250 488053390 488053409
    0x60509130903120f020409020f09011b0f080702120f030d0c0c1a0c1213060b0102060402280f0803070212060103080f03040201030209180f07020a17092202190504 71
    0xd404503000b5400b40010313040c22811142d00303200024104005000074003040411004440e03075099041d0000d401c01c0040d4864600010034600c1010000e10340340c12800e03005030000c14030f43d1596010300c0091031005010342003118034000c00d0715502d85554000058101c000342014140020654588101e41001c1201d0003c1c210039040e1004158459040c00072680054107484201c1c5030821800a41e5070584090310002e00c0c441801341c606081c0071084c81a1041c800003440074000d50708040c1c0000355040d48440103035810f04038400a0103800140542c004000b0804c0406280ca255564a001d680b660410704040e40106409480460b14107000f05a0505070b9034041c4920f0304087d0340d03603000c0030303a078200030404c0b41803607401c002c100000ea5484015844c80c4407940b9812401d450000074844071100058106025503005010840004503040100d07400c1d000c0165030103494801b2035000420400c0c51b02c1002030041c64622200b00a02d9254006205044d941c50385100c8699002004980900c02c6104240b0745 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 488055890 1250 488054640 488054657
    0x4053a0905030c120624030312060a050409081b030c1b04050f0c03011a0d060e09010b03030a050d021806040314062203052b021215100c03120501060509130903 70
    0x1002c003030318600200c9800d04800c0725106c081e00e0042440d651209291101c1501d160302001143d2500b041c070f00f80904001d4500340b2001d480ca60742e20b20035010300086c5041e5850b00e2520846404003c20503640740440340d0003150503103241101c03e5091100b00046d0360b0f0185080c00c0001c1c50212200d1411030003400910112455686808086249081000d0b14030036100c00422075540b40e00002c0c000e000c0500050130052005041200c003050840d0011240c8501a4005000c072020454102058805c00403003948056a119003508080d02d082d80380480d119400f8002107000310601012846070701c102d562440407240b06417502100300c003911090080c100081c402909484000901c68000350207250500410700f4030a20000d03404404228885800e1410303d40e010403c0c05010440a2400360001040c03074001c0c1c058080c103004103a882c0016036a680601c11001c411350101172064070f13105600d40c58007404020a58465000412540c08024040d03c42e4a40c8280c254070498584108414250302d034852004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 488057140 1250 488055890 488055901
    0x1b030406020715050706060906150e010504091104050306070201090c060c0507090903021e1c081312090b07030305011a2106031006030c1a0304053a0905030c1206 71
    0x3d43c41d0710194400400c102408a580060800e001d02005444d0441021038154108401c03204a401c220040100b0445010401e05071644c00c0412542691407000c80403d1003080c0790101d406520940d800b0a0b054400c28040111180d03040d841490307110310070303143c4c075011680e56200ac80b110707081c44001410b140c01c07014007040f2540e0650301c0720001038484e00596000114000140c0400301030001c54003510b41002c0c1071000c0440704070b0420404510103003080342c03141c2400e14248100e40547d01000381260708a0402c503050301d02900c0444020901c040805581e08103078940200504000e20840c0c0c1551b006900b0752081008100584e0f42040800c104407000542c01c0e03002040703001c009001d140d018050300b8110080200302c0c0c02200040c5010b400b010f000c0ca07182404007440d001111051404009050052100113600460f0303000000866810b4800308501c2e81050101c5c80780c2900c801a44440070240d15021590805d000c50129041101a1180002c0c610107200d00100018001e1040340c016600040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 488058390 1250 488057140 488057159
    0x1518060e01031515170c04081902011b1b1403190c120305030906060a0b0d0c030b04050f04050f0f100504081603122a0e0d020301020f1b0304060207 65
    0x66910500702c0c4000f08503581d402d0000c1002000c2e034018001035808003804584070341c2581d07417135080414104c003249000e18200d180e0742c842100700240d43c51510581120000c4d07a21030a011300403000b04001444502205150001c10512020480900030a01c90780c0000c0030402d0028031003100310040c01600009050000c440e0b01215030200485400c0c0314000301003906001c074032080111900c241c44265032400d141c0c03103440c0f401800030902c600c620340c400010702c4a0038142c015540001307c002c00210f85008041c2080c0d016003081c0070844d0f0840d1038481003295011a914209001c0c1e4000c0d0280c44642e55401c5403141c07207100d03010451100b50700c20b40010310700d13807082ea1200ea80580550915400c01c021011220154010842d00f0783c0019046a0030452030700087c0320704424002201c82030b02a01c1408080401050100001e000610420320440e40042c2c4504590004544e4020300031541ea0b0a60744100882e43c1180f900c1918024002c400b10704200300020841d01a0b070860b400600c2c00d5440c210326030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 488059640 1250 488058390 488058401
    0x30308040c091a01110607140a3509010b010806060d060b0c06070f0503090a081b15070210020403080405060906070b0703090b0c0a080711030c06011518060e0103 71
    0x444038400703280340000d258103803480344080d0380382184004031250a0304400106031304510b44091807070b074000200703111005410580322a241c414a00c1b4a60702d591030a482560313201194240d070500090680d9504200002c4074a004800aa5905a000b6151280705d0600c1c200c0707544600e01d03408512800c02040c0e4078134003c0d003d8801500343d0000800c00503100c2d08680701d203803c03010503c11141e020b03105000b100c9420015180e0030012078a031550451508182084d42c8070541500176119070350001c0d00200c015603050381405940461811030b2641030005280700c24142048440c00014082c0d40300c95011a040750003190304498105a07a40d0030301d030600e001c1110326440f040d01158820350030841880010b0380100014401d40681e24001802c1110303003003894a40f40300074568600b1010030840050030b150400c1881d0f41080382c034603046e5284000300441519611030b0b0a00c6a00520074940002242c03500c10018a26610055407400d0442442e41e0001c00908020300a60000c00d02400d0310f004c01d03502c03a5121 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 488060890 1250 488059640 488059643
    0x1d0a080d11130f060c050604030f140a0908070b0c07050f28030308070c080a1110112205010203031f03020a0806071d210708070e1506090a03030804 65
    0x284541c15041d0807110707900046081d0b20b849401e550030086608480080001040142800158126a580c0e541c0c7c40340c000900003014030448000b030000e004e01c14006d6500700c140c0114031650710107002501401100f024800c800292080c41d10120300500709509441c0c0c281412001080f1850401c1d04104c6a460745085a80e000302c0d602c002069510244040210142505500790050381e086040081c440800204180d00b4000c06d0301d520b03000100c0d220121074008080346440c12205911041890030300c0d15500c3e6600c090b03820028142c0c0034000c2900200541c4c100ea562800d6034580300c84a14140c20224414640981c000741300140200003040d50340c100c8410000c048403101c0f40c44c0d5002a001880700d0300f00e21206c4c0c0c4900204640545c1120140701500d070741808407040c0301160740000740113656101218043c00d03e04012140720100401c00c40c005440c03450140c0e4a580e840c0c100340048101e00701c5e540c0d00c915840b0b4500140340d0a0840480f02c0400c806816104030a055441c241e628081c090030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 488062140 1250 488060890 488060917
    0x30d050901260705120609070e040c0905060f040e250503090a0512090306071d010507020316120210030204080c10050712090518060a0e090a0f12031d0a08 68
    0xb80042c1090b441d00c03040c0c03140c0c007030707489090f1522002400c2d5940144014510b50080c502c80080c07109854003c80e14a420074001c45001c1180401c4504c101d60803000d551100340c0010340420100b02901444014006407005005034050a9413a00c161048446207000319000d03405070740200d40c0145103d0b00085521002000495800880d00d0b07685030f250503240041c0740d0006030041800291443d080c0000d0b0340003901d52030031040b840950004100c000c03040c80c0d840e60510100044074011074a0178410301105178102006000740c50355075907405c02c80c62040281280701d508502050f0700014000d10950b816108440c00814030a182c16080c410f0041c074080444050060074442440000d41c9080c800281503000c0d84da1012203880c0005218600103080c80010f6006007500400841e501e6a0745810b04a5404220780c210381d071a04c103c0c1904095a100018cc0000f00005408040c42810442d076003a520450350100510884d01c001400e0319014072900401c01d03041100540085403e400140407400c2e03102d00f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 488063390 1250 488062140 488062187
    0x303030402090a021b03030c04090b040b01140a2d02010e2b14180f040606080c030a09021c051018031404090c03051509280605040509030c010605030d050901 69
    0xa86506d141c1080f035226041e0400014248100c070001e00a5880031070f8140e0b01405046c071940d00203070105551003285580701c600401d4809841e803040c9100120000050b0318009a144003008400401400e144410050743c00d1407030411038804001200100c1041046800c02e03c00c2c0602c034400c0e10040c1c07440c552020040b5503541008102c80f882d0003000a01040b0030039219000f80300c1e061100e00000c2040c0302d84100d00c0e1810410030716030099281944251294009035032662a0180c90009085448001c2d40201200b003130030054042514201900f0360082c401c98035031000c0c04603100169020b03a03804150b40c1d110907a41d500060302a0104010700010050128285500c6000f07200c1103c006ca0448000643c81c1e13414000300c81114501c2c15111001030b16440e50502d403141200e060f8010800c0c83d000c0c0d440600001c82000045644003030064000180113000300d0400c60001d40d0303a43c010701c0d000401546071540004a6160025000c0202052500d50a007082080390041d42d2031000071740380d803103134024a5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 488064640 1250 488063390 488063437
    0xd0903030e010e0d210908160c0506040b070b18030f040905010b040b070809030f010c02070f0504060b04120309031a0a05090a1e08040509010f08070f0b0712050c2a0303030402090a02 80
    0x748064040318010000231400b090711802c0450743c81c80c0b6036024a008100402080c06551891800c80d041c1c141c202c2003c50b4107860b10700c04c4000502001008a0316400301240d00c002c51003c410040080300c0c1441800c2c0001c0e41ca81200030b41d107106a00c140904e0ba101009203000003044031015142300e88004003560f4060303180002850944440030f590800503008038400344001c0c41501001005040d007910108200d138104881040c55100d1409a00d440c0c00d00ca0304c0800c1018800e2002e4006194041500c45501e400b0010303020000a040d1400da4003581000f0002c3d1121400280d40e4400701d8103e6a52103204038009901403110036000d1050720350345420400403c0036200c96613400c0c02404800c0f00e0821b15454541500e05180040d0401000c036141124100801c1e48080b0548141580040b910003070500510b4055884d0300c44d016202d80c40e4040c20601c110354a9041301010422820003019413900041c0004040c1c0300d11003264000e5100003807070042524402154080e1030342600c0800700c0f42200740075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 488065890 1250 488064640 488064653
    0x70c06050a15030c08190c0603110f0a031b030902090402060f070b010e01030b0c0304120503070c150b12030717030a110c0c0f01030902090a0507050d0903030e010e0d2109 75
    0x10b03600f003900e98000003c0300b00107660041200c000c120840000da03d84007001c581d600f00f0004814411581019110391440c00c52100200464501c0c0c00c4802a150340d690364400054050042c110381c9042c61a154040c005009019006544070654014248400c0c2d560f50f81c01c010389a000001021030034101402240002815040765078064240103481c0140f940c0340d4508040ca40b100104121078020303003030040c08005000903160070940c0805091444d125901c200d02101c182626074406402c884e80084144140c107136a0703008a075440d01c20358184c0c0c10102c50800c1507550b44580c8500624008501214030b07c030042031405142c010580040200e00304019502090280c1c200b035864014079000349c0c10a048500c0c00301c0c49550203070000c0c2002c1c054281d05400080c0346078402001c603010360f91283d000440041c424012a81000d0101104004c1400c80b810014001c146c0c007800c01480d586004403440c00d2140000c2c07040c4004801e540d400310600344400e0f010780b20041920441c40102d4445c003490700010b26 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 488067140 1250 488065890 488065931
    0xa06050a0608010801050c07020915220e07050103020f0a11160806070816171306150512061012110d08070b1305060a09030e0a0305070e090105070c06050a 68
    0x1a190745000143d414010f0850860301c025001040e03001c0100312180058403018621507015916241c080c0100b14810081041078010240040004240c948003010300700c11540700701d03050030600080f40c1c81d2540300c1c0015401c134070500c0040010f001e410701c0319a030458481d030307400c2480b20f06210680f640300c1c00d070740794680c141d00c0903401c19103454020400300803e82e0303444040706a0202c0c0401183c2c0d0380b9280b40c44007030f04c1c0705080000b1401401c1d40000007001c01071180640004942d0040c170410080310150320780c0d888019607004003441041c1400860b011002c00040450160426082007600341d45032203001070005010200480d074608502078060010b9030b50480303641d10b41e40100812a07807000a403529503405000240000700d5421040300c0500481c200150140c2d0240c14080001069003550800303850382910503d0707460740300c01850008410400c004c105003049450700991180303e070322240e04407800e031541104c1303900006003c00c0845001c2001600925040112000300003100f505100364500030700e9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 488068390 1250 488067140 488067149
    0x402030721091208041a010303053f18070e0114040c08061201060f0b0c150408030f1801020703030e060109021303151b0309020406050108130b0a06050a 67
    0xe40855805601d14040000892140020081007120300350341d9a9414500194030b4048041080c06400202088800c451100c0b00c10880780340c0002c01d40c1c0d01d14008002e5406114500da0141c10501026603640f01e10b044c00c5d20300c4520103000900100105e81d65100319a00602030328501e4060320702149980710a20110f409480d0f1005144e00c15030501d403080c8114803039807156900552604500010031680002202c0c0c00140480d9040011030341d09101501609203070f0071080d01504a5407002800f4490b51004040c492155400d0741c4540600c440005c0800d107040780c3c0034040b8942040002c40d50440480340d143c0c894294a42090280741382d228460032a008048210007195030303403500d11031201e42041154010b00002d81e00354900501c04001202c0000c151100501040d00301044034072411903034100f01c007078074000740d4203000c20740000c200103002e440c0b50701d8140d000d5850001c01103041c4d4440c008a9104031080b880b0f000b444030301c9a071408031b0707130100402040750036a5824011030f09680c0c9003c1c2c1c20080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 488069640 1250 488068390 488068397
    0x513060e10110303130602040b0a020c0a0503032a1c111b0a061206050612041b030b0402060d060f06090e01170a020d0303060306020d0c030c02010e07090b010e04020307 74
    0x4241406100380c4901e401207140a0049022420b2501c0400100700d03980544410b0200307004081c50b2401c80040c0c0150780002d45a42e1001c10700d20f26007a8000707081c40510a04640c80c07034015030f40c1c90500d512072040755041460701100002902505d51030104c2140040c80c500126038403e0780c040385001e0408007091141002850100c07103a907421404201401c09200e41462614000140f400000c43d9800503100385014000c191a111100554517072000c8004c2002030b00303039070b1307541080c402d8107040040464040303c5d01000c0c44091141c1c50b451007541d034240e80d40040000d125840d0368080011a81101c4450b000f519100c2901040c0441e0403c4020018000d5440749035600381840300200710028140c118100d04111080e45103c0700000083e1041155010340d100e0f451001e2a040c1100540100d800c0034000c2400003800064400140c2d0260030541040c0d60200500350400c401203003a111103602d08007003544001000c0c0144003890b40b050303000c3e01e01410182d894142100102e0107980040340d011020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 488070890 1250 488069640 488069657
    0x2090f0c09060f0d0506030c0a1a120106021612021c050a050a0305090a050d0206041208040f1805060102030a080a0513060504050a03030b0a0f15140d0506010e0109121101051306 78
    0x41e000c107005c4c80341c021900f00d001e86413070142070700810054550380c4100d100c1c03103540180183c0401c5442007107a0384600c1400f07800d0460341c1c407014040e503508121101260f5401e9201e0000605101e8918802200b50340103010002d00403414046e00f40d180180b40054a003401424823217000264200480d80501d40b02e034607140d032118104410050146043e900407070180d4072203981300300182c0d20f03a41150191800e0b040700da208012603042003039250082c0c2c0c214101901c611540441c1001142203a145180118042071082703a459070300490700d0f402a1282c0c0c4000c0361804000c034103030320546e0300100d81c09200480e110300b0000d0350303466160a50304151000d0711244c01100e040028158540680a0b1391354040e1401e07040035180200d00c0e00345101a02c0381c0789100040c44c0ea60140e2904c904441c6012250302c11110707460703165418151004210680f64603012802c098800b44165000d428004100c4c0c40703091081124281036140c1d2140c822801101c1c40c1008000c00070107080c50409940080500038aa450981 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 488072140 1250 488070890 488070907
    0x2a01050310091b031107021f030e0714041109010210270b010302040c03140c0306010c290a06050d11030c0909030301030303140f2404020c1011040302090f0c09060f 72
    0x46a080505d802c68444007000624090703111004061031404294891100e20650164101d0060420050a0b000360003515000a1100040c100c92001c01c0700403902000f0200100c010b020303151041d800b42a001d0380112450300001510360b4805080a001c80400e40c2d80f404a50301c122805c0d0554035402c554076103000c001441981803500c200703100000941010007444000b14452506a030700244056111000000001c5090b48603d004441241e031006442d019101504504800c0021100302c0e49509600113001401d140d000e80912800c0700c0c80a0310090755051103850b144690165081c1148d0503100d41540030445440b04800144260103400c05107889506524004094a0700e20b00301d201d207400d0b01c100f4403c980310b034000800c1e0080c1c04000400c4580340503603240020741009034100c0f94000c0c0701092903100a41c0208141d202d00e17900c83d8041100e032195040d10103941c000c80c00040e42060644001501704c021194039240c0240311140f00900308514100001c0d400d070b12006003c110800c010031141d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 488073390 1250 488072140 488072147
    0x30c0f03030f0c020a15051e041110030b10140d150f0f05030f030f0f032703130e04050d0e030f0106180b060315060921060105032a01050310091b 64
    0x8070042c0d24020a100509040b003508100f90310005035490703000307208d501140c204402070810011030b80000c1c210801c1e65075082e001074024612456400d00407032103407410803c124460b8240d05c00304000350750b5081c2002d0800403046c0050030b5880c001c9010a038900c5c400f1842c5040880c40500401e00302001819250400c0241410000a07000c0c0500a40c820300c40401c0320109181501c1803182c01c000c00a072070b44c0d180d0038201e1401d0101c0801c041442c070203c466030340c000000b2004107065001c1344200320002c0c0e960b00c2503034140c000885000d0501d820840c0004090351080261001d1034400400b00c901501004105508450b141d03440300706d01125892143e00c52075200e0040c1500c41108480382c41c04c500d4501d04000c51a050290080c0c402d1340b001445055580d0b6a4102209000315208003030f00c01c00c40c0d071039490742d03030070080c040c0610900c120320300e00254081d10b584051403071082c0b60002021074410001522140c00c05401c0480790611000c000c50780350035502c221546000d1480e440c0200c07082000026 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 488074640 1250 488073390 488073413
    0xd140921150c1804060b13030b0c040602030d0f2403030801060509030309010c15090f020f0d0c09051b07060f052202060d0b03070f0e0a0504030c0f03030f0c020a 71
    0x30111203854810000da070002c0105990008400c40304881c0e034001a100090020440d42e00882c001110100340440300f2070301c81010106580c4a480f14a820781c0300c5400c0d08040c0c0c0078611403000182e10800c813525640107160800030410406a4000c60306980010340c400c1805881819502d404404a03002c000703242c0c1c0181014010202c50400928102030035004c41e440344136070b142c2181401a0018850100300e4151398010407524249001c0000415a1802046070403031728005900c20001020001c4581c6000b11000310026801000c18000620f0040c503100070b00001440e40304004d803c0c0392415010030209004002c2e16214403000513a41205081000450f100a0141c00840030221040340550b0340c0c08507101c0d0243d4048a01c2030b201c40039007420b08050424080350b02c1d0540030343c100014080c80c02e10104401d44a00303628041071643c2c0c0f466103030102c0740200e42c050000b6030711000c44400705440400b82c180c024020302e400f0035108190644841542c1c01d0520740030041c0d0200d080c00e0248004170040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 488075890 1250 488074640 488074663
    0xf0204150210061410170a0c030b040c050304240c050a17090303010902180a080d020607030b060307030b1305101701330e0112060f09050d140921 64
    0x41000702d040c021030b0001d00909810241c002c001d0b01703692034841d9004800000c5884026295501d030b610b40000c03803c0260445021110201e400d10740329a16601d4a806402030703069590f0340f4070307007959240d413a40c0740280703040686005c1c2d03c41c0f014559400150036004004a516143d02c910341d41303c07140c20000744488806444980d01c080d401c0e040c01484507010085904440144e00096141c0240308201000d61880b526820f52050022000152101e00860050600102038003501c045a8032681c083d02034551885080394003000c01c100048019004c1c2e0f111038015480a0290110314500f540103604a4000b42c541c41c0300c80c41554001c001c03040b11034480303d04c80c94010f00203200d1596038103c0070004c041d4034046100c52010482c080800200da00390b61800428800086d085e003940c1d9510340300d00b05224188195581403c103180350f0001c40850044400c80c070b501c10000d00105499410840e203018001c403903800902c0040008003040d5695415a031070031b030707d0791180c0d880f6070780310480d80740c909000d2914 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 488077140 1250 488075890 488075923
    0x10902070c2111030f151503070303050a030c0e180a1b0507061a0904140d0e09151309051506010e03070e06010302070b090f011109031b040f02041502 66
    0x202c20344030b40d41c40401891090b81c42038525801805410000703003428070811003610240705031001180070038010700c0100d004604081108180c8002c4c4014540c4410b0a80006070115004114826003540301c1e50020700030410030f1406801800111001071840590700b454002e581040784140706403010140b10380540341c00b003504070b295120b0234410701070001d0040d04405031410b40d132076a40c04092048086600c401d1400200200780c24602443c0c91a05100300e00c8007442d8500c9035001000341c0501034149028080c00041001e601a950391034240c1c07100011204c0d687c3c204500c100c85920b800c542d4040c0d44070b090312600103481c5a0402607203081034003100811140c10460b90b00e401341126200480c02d4419a46099002c040340d5480e40d005902034411014000c0c8806030f607508002085001080252050345034000038420300c02030a0f10f5007054001c65440c594103401c542200503c0c0f124842420006410180004c00d16160141d0203504a800503171102d800c05c2c120410311000303194148030b0540f04100114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 488078390 1250 488077140 488077169
    0x90f1a010203092211130801150509150f04020c0c010e04020f03041e050303040c03052413020d05060a05040308011205031603180623031302010c030c0b010902070c 72
    0x400280441d04c01902040342c0351200c07503005014441941020928201c65100390b6503821440030401d501e00c03098801d0401551810f0f13844001090540d030484206c5900800031602c2d03813101c4582c0d1044009848819a20024444043d0010744030303030018145016048002c0c000108207000090000032003022020304c80c0341b0400508a4544451040d00d81050f004001c504221014801540018210f0b480c040c11510000c410801000300788203041054902ca40d054984c0d81c4d40c0f4488110000e16031401800001144100081851130f000c400d0013217560001f06140e20062854966909169060b9a6084100e86800030402415005040d0f2030050001200c0180c4c04813590316101d0710f90180d140003c40241008001a061501c54504056983c50041c0c014110795134488014080c4042559034850010404940c0700c030006890003924450300c1c2003441030000804c140d004407215882c0c54000c0301800911206030f004111520b110a01030000c100c001a500c070654109119090155804248400c9400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 488079640 1250 488078390 488078407
    0x120f0a1b060306120809030307080d0605130e0703140709020d0c03061208040308031005060c06010812070c0e0403020a0c080609010f0c050d1d120d060f0f060513090f1a010203 77
    0x46030084c0001c0d0081d5115454003000d50010f402c6118222010746180700100d00c544100c0d10945c422070480d80100c4109400c051864110026222070740355031221030f003161108102003030403000c0301d40050102e1001d0f54549505d0317252840498005600b54488287e4441c20310440307542510400d40a40340f2100f1035401d20b55650365070702c0345206600009005403c0030012403081090703103d02402038103006080d251242c2c1c60849441d070342c3c50244100034403846036408041c030501c0c0e00c9089800c02d64100c0f013111000d03030600010f8555210b0144c0708404510590356043d000c1030010035140003400c11a0b01a000c54284441c4940c2980c082c02c9400f150b00b85040052600c0d15085400c40f0007007200303101d0108105201403c0420b00c9150400c15980b9070007406250340510000c080184104189000200606501c4a0080001d0312060207040302c0c10b82c48420500c9105d00034800f400d10030400d81c3d40700748119110307890b03181564000f5007010005600c864030b140713100902c2c03400341d0700041080c0700843c1001c002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 488080890 1250 488079640 488079659
    0x3031a0103091a1b21130b04150b041b0921020405090a0c03030f0905060415030903021c0909050a11070b04080d09080301051e0915030304030503131806030f02120f0a1b060306 77
    0x640024802035140050384055009a0441d4580860003402080b0710380e103001c05601d18800039038000000801d6024003080914280c142d00030320400540e0004280c03b07955003440000d180203000200300740302d048000d00004092070840d1018501c0303036944c60040c0b520304501514442e410742091748104401c2c001840b00080c08080603e020f2814030300802c5c11440c604040c1d0410800d0030351114a5240c03a082d0811458000c401c1008440301000e04100c540e5507000490226a0024015054240204601e02c04180c003100101c0e04a0f0240b04141d01c0c0822461200c0100c58901800300c81e4810040010090b40ca407003640f00c0e80c164201c2d5010049840300c4000a16030300001010110075044400012031651400c1041d42d000e07580c0030084131740c1c91030b140c400001040362520510b80940848017814865104e030740070b910112940b1950600d00e0301c4c490780c01c000301d001900203181013900c0b900210300b0013a9000c200480700c450044032112015000c8405508210710607030401000c0c542084400c00c400313580e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 488082140 1250 488080890 488080913
    0x9011b14120a0501060e03120706150b0d090b0604020c1e0a140106030212281e061401050d0b0c0c12040303031a0103091a1b2113 57
    0x80614003103a40e110348110444280c01003811082100720030000b042a580c42540c00a8180c50050300e540c085090340401b05662042d180f25080c4a80c1000d01080c00041d80c150007203a4941040d5038980400781c5c03a40070840040e000402c42e180556224842c1400303010002c03807410b400020aa8081d4907104e07020a003242c1d01d44454450310f0103211040092160a1002c0c4400c20801d54001900b01c12050300048041c00317000c56000903881541802402c07541c15200056a28090051800701200099120304c1016a0600020b0944015540011a05d0035021100c002c14840d07126003c0011503010138041405030041c140c0266000304580482c44001c104a8040140d00201c0d0f1608a5039078000d03d4601814061900b444156000d00894040300b0503815400c2081380510440c2c20003685044030700110140d440c4900c001d40202d0312104054242e90740c1091490b80148021100940f8503060355a102141d400240310010000b01d44490200d10b0ba0318068058000303002c0541e17080c500b6041e894920246e503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 488083390 1250 488082140 488082191
    0x20a0e010302031e280b0a0c091401030603020d0822140616020d0803070809120904150e01180f02070215030711030310030b0708090c040905070b0c01060302090901 72
    0x44e018001140404204a090300c0c00300e0944580b00304202a0719a8140c1100b145003c44400ca026800550013050a02c10310031012560b5036540c0c2010b143c4440c40e5844100c500c0501d0401d0b454000c0413000d41c58941400071928030070002255039660403550908170704d03070120900c0e80c4200c03031200802c0f81c60742448031a42c281d0000c1303841954881c0601300031304010100080c020740114900420800b8404c40c80081c510600c1c0300d8030703018031795620b00440c01c0c0c0b03e02ca003070103860848809204c040c00504040e405000c4c40c485030804a55015220904a803084500341d1004400b01620000c194400c4007600420322180c522440a60901019038006003180041781d5940ca007510300480000e022078443d989407400d2484480c10f0b2030366400e00c0c401c09401c003006400f003540e9082e0f03040045200076124a51507032045001704050460500c0c00780801020301000c1301e0a403124441d40c003010501110020080103080b52603000000c9661070f503c1031209007080100740302030691610700301c0310085024104014116 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 488084640 1250 488083390 488083423
    0x91a01120c050405030105040609020316121524050f0402030415020309100903050a030506012f0c041d010b010207060e090a091b030201021c20071203020109020a0e01030203 76
    0x407198030100316401d0143d41e2007140d266007030009100074885a40d11450845009505580e50100d910001c1496110f461140c0b00740c5080e19415100400c0403c0e80050070a59000340110701d04050603403c0016011000300380040101100c010415480c0c955040c1e01446426181035046d45002d465041c0024841d8024100e042d8000001501a800138440c00400c42d008001c104040c02d00b60030010038a40243c503003000803a141c0000300d810303580144981e482500400d080700519590194026905e6450344c0010081c611482407070040540d80d6005100e08240203801d1a0190b242c2c1c08401c6081d5800d0089e800c0c19500545014021690302500150b0f07020800d4400302400e0305c44038000c00060030300003400b400c282c0000d500c42a60900003207150302264000da00b1207001c02c2003402051000420074111401241150100c011485108004a84010301c000140c4039002d680d460400b8452440090840050350f44139606400c41c6807480074100904980c424041856041d64042641c0d4001210a500304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 488085890 1250 488084640 488084651
    0x2040504111906021c020705120304050f0405060904020d1407060804060c0306064404110604150e0a1a040801060b0301060f05030a0908040807060e030105060a06110c19091a0112 78
    0x81e070003080741e00010a8050100c4c414042427000c1540c40307400a00541d84280c24000966541c0c1c9040d024031405004010000d40580c0c0b981d500308403859407070750004c86944003d1003d0641c6072034140121001004c1c1d680b548601c0b40b600b840d0031000c0300d0003540b9035030515240000500826902240111a0b40c5074480d503440482414141d8100b034040c1d00c0104445005a0074124500c40300c03064025009610950040d90403070034040402c02d042c01a801107a1080030214040c401c1c8904c1041210120400501100400c80e00d6181c04006100020003a4046410005007007080100034401c6100500c1e1015849042d9414458018450038a06103100b08001c40800030a0703030414658098600035600c00403680d80c0340d030b59808031501d401c1c140c8550300100303200e0008240241018000c451084100410209215062010076240038444885250700d41c13051045100d9561242c140c880fa808290041e030041c031519000440f401d480008600c03101080034040c8001269801a4002212420f01c01000c900d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 488087140 1250 488085890 488085943
    0x3061311060d020d0c111509060c0d0207050105040609120c020102030a03021c0c110712020f0904050f151b0a020a110402090604090c0e06190f05070204050411190602 73
    0x29011321031252546a18010000f40713a990000080210450008145c07107102c0c0c0c2c00202c15075100022148601d29801c52800a03600303401040040c810142051001414082c02d9224182141d40031074044803051390310070305403082c041300300500041201c19180c4070700c4e141c2c00c581c0000c0d180c0c0210070b040024141c02017690100c10180310840c210009810328200030307845410030020454920485421598000c9410100d00860041d034080399050b00079001c2c0d0040b0b04070a0034001d440c00024820340303040c040d0280c05a062002070000c1000140c0b0342600382141d051014442c0074041e1514503075001901c0421003039007a103401264030902182c000c00d800320201140b00205010340316140702c132980324800080c00324203010140d00c6078005c002256140f41c0c410f8600014000d040c8243c0c0d0f02c035082650648000381d1072905c50008d4100390986072800904091103a80400d01b40c403c103841c105d8400714000280c95280c20300000710300c2d01d1107540c98214411407a03c41e01940394120159640c884071480b141892 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 488088390 1250 488087140 488087167
    0x1603050601170f19020405030309060702120d080405070f05011e0e0303070305030f060316031709040219031407050a2015011a18060d200403020306131106 68
    0x51408802d1041e040e86844803200403c00710846034841c200e02c5050380c22064003400d100342c5040d254054029803510b903040003045640d80080304126440038031001c1c100b0340d00400f404546607011240d211110076007070926240f0f0170840035800800c50708550300c50400c140c1e80c0c008807141d0001c000c0b006c0c8100b520b24640c0112450311007900019014400007860740201a8070200039445189049500c0015484280c10151984035048e030014802010710410300c041501d102c204005410142c4006107000090004581a83c01000d076507c0d074956038541d5026a40e4240c05904184a00c03505102a2454000c40141a138050214a503081020340095411240704c60841c0801202c400001c44148104020311160048024003544054242280c03000c1c4040c0d81010035110400403103002c0c501da855000007400001c0e0460a583c810f05912000c0c032210881896804806030380300e800031140c0c2c40381140149840c06001912448000f031101011001286019603102c88401d022104280e42c1c407100710012 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 488089640 1250 488088390 488088407
    0x10b070c0506041211040b2103120a09060507022a0d0501020309030c07060c20220b0102150108070501050304051f0c110f070b0a02070f0305010b010e03061603050601 73
    0x940024001401050100c0751440c84041130f8803403400c144085483d14180000e4451900c1459041172450b000e241000075840b0203900c0c410300072400c807070030080603902090a03240196000c1c02004d40c0c510340300c03061001d01d0165a030b0210007800284011011000c9459a04822820007401070901d08a003c2d1940c0d50300700b40b075904a030024000d54490401d07003c866101d501c0541946403c0c130520000180490049c04103014142d0010300e41808000c817402442c0300d020804901031382c0090810319035440a0031300401c00590707484014000603001c0012002a15140342c80701110040620100100810000020400252402883c000e0340300c3c1c80c2e6181c00c0d850100c441c035444904c41d000c441c1c0308100881d194005464841b0a40c1c81302c154111044d200c031b0720b03400b400f804000217800c2424140b1900e500320008003407605141c41120a1075544507a40d4032311109542040703d00da5115140c50700716680c04090203200d010103c001e407200b42400c0c40005c0c60743e103c0300200b40c10b060f29500022416030144010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 488090890 1250 488089640 488089649
    0xb1602060304150516080606130315050708061c06090204111b061602210d0e011508010c020303040b0601030902060f09130203070e06030c280f030212010b070c 70
    0x2800e07240d040902c0e1116180300000880b40c402440d0130b0000d0094088903402d00c1d40801e00e5243c0c0d115940f249020702460f60300c20303007650a42c4140f1100000c00a14151403a0904c40d014510008081c188404002c02201e0040e003020700c2008a00300100d41507070b00c1c018000c0c1d1a42d002c2d00006041c41c07d80f0205000d0b002640440119100100f80002c1c20800c1c055090543c00c1250155116a41c410005030b00602480d102a00140d200c2845c03240c524481c1c001d1140b91544080b002410b03c1513000e0341c0b0090b03c030000c0da805000c0c4d446034020314801d03e803201d450000e0703d12007000344130020281e10000e5507404000c001401d0040b440001c5000c0e640254401c1441a402404641d500d0303c9070114050036a100c1c9241c180148480504c02000400310b1007617902038501d5a443c2c126140c0082c5c00c100d0079800c0900700b820343c42c0c410800e501107982d1080f1104840305d201d80c1d42035100800c00b000680021080f5001909241c010400c0411082003440c000c7d054070151903002e51243d06904001d100042140c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 488092140 1250 488090890 488090899
    0x9061704060e03160c090504030c06020306031c1101050903070f12140703050c0c0901050319170c0609150f01261203010504060803180105161e0b1509010b1602 70
    0x610000c08004c82c20300c8580207016020302c0e6404ca9450400300121001114041e0000f0409242a0000341d2a50015600101c00a0807151505000e50400c92254140c00c01c160100e42000da00307084100007800b075158411240c00195041c041d440d00c94403080b509000009215060300701119140a0043c442c113681081000751845d2982e0041c43c018046134418444d0800c0b1b48600c41d202c0c0380c58900320341a01d043e10310103400740040d911812006071001c1505e0004851001d00925400c42100f507034005841404e06070b800070111340c140b1403034450400c070480c030100c60801d507180300708007005a0070210a8111100042e500300e10070182c6c602265041708240950107a1300032a401c4440502c00c074406075061b210b0454042020a540e4902e43e50340740b08000b19100c0102c1c040300c41d601d966025002610030b8030300490300c40f45078800682c0c403c200204210210b4030900980100f14003400701d070b12a40c5074419001e0030100c218005540c0000d20b000d105100b01103044000180001c0e07050182003c4482080d800340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 488093390 1250 488092140 488092147
    0x321032a0301032009041a0c160f020414071d0a03051014131115070b090a030216140f1f02010518010203010f090b0a12030215060109061704060e03 65
    0x50220541c80c2010300100340d4580720541342507a071406403c040d0149070301080300c1518003a42d00040f107a20307200038060b891030442401180baaa84060040c0101240f041844003a264040c0c810081121010680441d60280503810000140e0300408200054010000c15400c0c00900800041c2c459001d45c10080650003800c0d009080050f031a000420108140702009070300f03599079040341c0032407800c0075800b900035400314140f1005400d1298a40d0441614021154a013032056101c0c0044100305664140c46076202c008101705050741401a102100740c100c5002a1103442c095003040401d105651891061045140041c06c039a04c201c01c40300741150b0359409220840000c84003a0003080112940289010b2443c020348011a0600c2241c2c161514404494800e9040207501c40082104640c1c00e50460303411400465840c202d400810031907846580107101c0388010412455011001030b00180c1404001c0000380111608441c840520741020355030ba168030796a5040450203042440000b05140c000003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 488094640 1250 488093390 488093393
    0x6090d052212140c0f010c0321060b0c100612020603090f071d06151207030b06072901060807030e070f15020d02030c030414031c0503060321032a030103 67
    0x1c500386142e404501003904c0090b241181031001044184c4200b60000d00000030543c00240202400340040c04200c0031001a2025555038108a400e00d42240444503008039040c50118020041c5480b868400441840143c1c5002c12802699000800080c41203002000281e05101c007001048038512055040320080e6039140c400207074001c03802c01002d02a0800700e00140d281e040c0748a8045491111010340d071328140301128844080300010b0101400c054680d40019025030707032203003c0c11400340200032050700d08140000903006030100a0000071018a2803004000c043e41101d00594044018100031030000c00a88540781044410b80000e103080f011b820006c070340c140c211944503004108136003c50340d1050b020441a41d0300c3c01034000d29155070703103f00410301001090ba4045807155802a0450341c0255401611b540161614080e03000024008820024a80380400c20408002c100d040c0501600801c84a03e1f4007a11005103100c0025282a801e621000a040141030b4148803050515860396102e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 488095890 1250 488094640 488094653
    0x40902030307060615121814031c0516230a0c0605163b0103140a0504020114090a0b160803010e040c0e1504051009110403020306090d052212 62
    0x41a9949001030910020b070750000c0350910071f28565a495000e040210b07913143d618100320030101c0420b81428003080c00700d04c100484540000b02d0b0040c0b501d00100382440d200b46044411341c194400e00c07081000150b0514100749080c241c85031042c42c3c6884181c0d80c0e2403a44401d54030402c0c912002420134dc50708003000000c900c070310030808a118031075031009140050080350940d004030003c1410507071541880084601030840106e04070024040c1004243c40703624202c41441080225265598a504d810800c421076034002556403c407690001101d081400403408122107080501810114440c0019080d040c000785116803030305564812016075030381d81c4440083c44034007010303a01280d0074003017501c0101c5c5d80240c00158074411b02e40390110755821092142040302800b40500800c0328030001840108490341d442c081c04090341104100e0070b59035469031052500d0040024021107154101c1468900169401003c80b800141141341c0d0101200c21030b0031454000b444c0d40e00003403c148880200c0b5040065 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 488097140 1250 488095890 488095919
    0x60e1324150602030d0b010309051b0103090f200a0602031c020409090302071715040303020306130e030a110606010c1b0503030a120f0603050613051507020a0507060302090a050409020303070606 85
    0x40d4481701344001e198440041d4161041c0580c001e1041c0c03c0300031f616000c801103200701c20180c80705150116100c1060384a4011028260b001030700d542d00100780c030100c00c0e40806405104081d05590748001a490f05070003c1d16402600144c030741003210504156284066070f0140c0f409000c00d040c08003c00c12a41c600a942c46039507200701140c581c14000b4102500001086112a0f51100515041c25076119030313080700254070041400f42d0103846c41601c9444811b0a1141070035817a0040000c40d990302d180c10029000446003440c0002c598010b03004c01c80035990020b0400045a4030111040d41c81d400031000c040c044034640c02c5650148400b16211a0300c907401036040c0201c8050700000c102c6c500c2000d40043c02d482460001610700da1000d40450001e0f0355000180003080d000b8400d8a51082240d400340c11144401c1c0c0f1040016070112490f0024400b06000002c0100850300301145428565008521070307020342d02c5264407995076807400b4000c2d500e0174000c0f2204a03034000b0f410001d294030f4145210b01c0b101c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 488098390 1250 488097140 488097157
    0x20a06020105010608090a0b0105040506060d050c250507121a0a02030601030c0c0209040311070305070806060117010e07030207170c010905160302090a0b010302040513060e132415060203 82
    0x5c55400c003090b9001c402150304141a5045080440c2980c24a070a00c00070303003c090801900154104003400710051580725a078000c04183c203503242c2c4e4003014445090030a018403041d407151000b01641e01d00180000a00da402c4541842e0300b0031914100e030400d0020900d50410007040750680303500b00060310081d54002c5d440f40400340c03420000d0441600c011114a002c00342c0094020b5180c201240102e0b0061241c021915482021280010380301d81d6110308082e032640c0403010940c0301c002444176035a0040120506011071903083c078030701d41c944000003401103806041c0005241d40041c04009003c50303001001032401c605445d03182e0703e42076001800e000b40035100c41910a0b000d080b032003680400310041c0e10400c5a03002084c0081d80d07200c44100300000c24801c192541859070030000061191a0782c0b040684d030445d0070800144040c075240615500c2c0c0801081e200181c050b000e00140014100c201200103013401415600d0304070a0103030f04000400d03000842001c0740321900800203a0543c000300070940318 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 488099640 1250 488098390 488098397
    0x2209020603150a12120c050f0a0303090b0121080a0e0a03050c03010f02030702030a030b040f05010b040801060e0c12090c09090714060705120d0207020a090e010e1605040b0a03020a060201050106 85
    0x50f51480000e624480e6010700070040c0c010102d003174500610130200d002030341c0e0080040c6c0342ca0008001846240140c8044114080398541024000380700d0a034100c180104058100c0241ca505504030a041e000c050700b41c014240d4001003906000c1620031080340c0302c11080500242845074480c01d12035a80e00c0114070081c80707582400c12003500a8414000c0c3c0b80100c0c0103400a504010040b44142d000c5c2201100480d00640d4504802901c1601c0c0d0085500034820380820b155074608000743c2e282921543c0d0451702d000c0030520140400f8408900866030362042c85000018591140038415041c100c840355055402070100c018070100300804213080c8100d8445002102c8170b2203190003401040c1c007840001500c2d54200d4500c05401100c1c0b03d005001072240d005006244c15103a9001031400e94003034000c0300386151f85090b070340b00e14042403141c200d4035580e00000700038843c1401400c1840b4280c9004182c000d9440e680038800c86d031140e040900107184d0061944903115125200203000308403d2203205e000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 488100890 1250 488099640 488099659
    0x9220504140f2107060e01020a05031e012907061409010b1e09100e0403020705090105010806150c0a0f050a1101080702060c13260601050f220902060315 67
    0x3100005543c0b5078049032920800401c10201074003491642040b40c0a80b0540e0322884880000c5800384000c1c494640c858031416100d04021102200f041c00c034001c10925111103030300610104941e08504c401641d4400564601c07007000e8502c3c00b001b8098190002c01080c01c0103010700004120070102d502c07444c0c40c00001c020482e1147c04001e6100c05000c416a20b02c860080d4409180c104980215440640c040c40301920030740c0e9641c0b5080c00d640403901940160818002030129250a4644038014174003403a10743c0f16410300380c0c00140440305a80d20405115400a200d40041310140a0b166043c1d801ca00c4008102595061041d1138035a4840100c400e00c42e503011500c0298000d0120714051010b543c000c20f0f2640e01c8542c0c42549521400c0540042e112018001030003842c0403410b203000164100c4140d4001010303909a62520740180c00107807259a005001e070600e5214040c541c00d007400e4002d05e0182260000d00d0000042c41c200700c019400010000400c07d99000c00c021030304960000751359034017a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 488102140 1250 488100890 488100913
    0x109030e19050105120703020c0d08010302090f010627180518030c100216020909010c0e010e01020a030813061805190803070c031202130807050a0b0922050414 70
    0x200051a80503083c0820020b00101d00082007030b22204d5406609810014a0049104080c03881c0c070030440392000c006940030f030041c41142803140c4402d410140c400d060038003550618002410110b0b01b90640d0324113208092031111052200d40b101802094114031102100c0801c054090251504542000b03d9141551690841460020441d554642294044c0030b15492310810070019605c810041c2840381410b03030011025a44845c80540074044010000400c070a0300d800c080d20310404000e905040c490b00541511659030007040c03007201030781e06280c002c00f59035034448544641020b01d000502241d00d01103100035280d2802c041e41c81800c0c01034044414049244aa881845410040060100c0c0f002d00c041803400b40140501c2403801c0c0b09050150103812086013100480e0022220110310403c0c1034000c0101c4c0005208000240c001a10008445400c010442d00141701d607420341c6028400c00d43d60103845400710170201245501851041c0860704180c00c2003c0e040c40100202c10740780c0124441d009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 488103390 1250 488102140 488102179
    0x90905010b09010b0301030201120f051303110c100c06020f0403050d17220201170f18030c07060806190603020d0f05041a0c0d05010e0115080f24030109030e 69
    0x43c12120039000d02850340c1e0a517030044070340c0500c1e1070100c20220b40ba011607078043d0120b4051107100e07040c03040140d425011507080c020082d6004007940700031030300501d039901c801d62a1060004800303003660400743d130b0320703452032904100a00c1004501442d42401090100410601260081ca1702c90642e8440c680741c1e070741129940d601d002c180d03002c0c003444040c0b036030360312196100c040b8646030503005040800e80041c28031004468920112078015800e07107000c04112300a4405100d00910811980c01942824065500240d40301000c1c00f03241d00f0b111740880010b805a039551000c005203650400b858203415039a1700050701030340141e401444007500f403000070341d100320480c0700e114800e070340209004001c004803c10000700a80054024408030400300091418500180141402841824142c41e510361504040303019a13080880d484e4104a0803c00740661000206180b682100b8130841540c45c5824041e0300f4181d01108480c1140c055080080c40f00c18150004c415440c1c98200b42c6072a40c208138940d04c0f80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 488104640 1250 488103390 488103409
    0xc110f0f0d1707030c0309050a110a0603060509130c18090302060a0b0117040312020f0301050a05030d021011040f180b0406060f0e040e010504200105090901150c0b01090905010b 78
    0x42d00c442540c240040d06840c40307900300000030740c2a8100040d10804030344519040407900c0d601075a4400c1c0c1940f40b058181440302a08000f00000e180801c102810440010042c201c050701c900c0c1f0500c0b40d080b0040911401140c614001c2000200f81200014041d4660000d410440020760144c004d140001e61899050f004005c12218160340c1d120f41001682502050120f018001f9001c005407648030100780f9408e0b10007049420b0030907804503100e40c501001c00681c42d40340d03000b01d4000d8006400d007481480e00000e050760b40c0e854010b4007090200048140b0003090003140c0c000c03810b91041c041d0018656a4401c8c2c600700806142c40284082c16901b41448207a540b14070810b000281c8110b803105403140709025400308032000500c00309154120b80052825140e0956054548201d43d241c841c03550000c003103600406070800c0c2002401d2565440010300a850148100201c00d00111460090b25102d000c1d540d84643d0300040c586900d58448070382d400123003d020000c51381586404d002c01000e18101800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 488105890 1250 488104640 488104667
    0x15010806040317070e1c0501050c07021f0c05120405040c091a090307051e131107030e0402092e03150504021303380f0a0c110f0f0d 58
    0x30f4a0941401c5248000e0420005108100b0000801c0b99035802c0d84c0c0b180604400b40d181e2942c984000101c4d42480c6084030400b070720751000e09004110350342c0162100060060400880c035007a1000401e221003d8030500e4143d80000c00034052507100419500d01d410103417040d01e40035101080b400b015818184c034451554003907141002c0940160b00400d0078601c00800729444054140c46410b81c0d200040f845032045180c0c00b4101098865425042c1d0511044911501721100b07024000104d0b801c81a4090380b03c0c40300041c080001d009102c810586503a011210541740107090344110505207261005001005d07500080844480007944079600d03c0703405542d075000e0034200301200d81440c1c903003040000e50003c0e12460700c2045c0024000040390000c3da00301114071000c0c0c0030056032484003200e28122506820745804540d40c2d402400855801101401d900480000c0c2c0081d1107412280241c0315640d01580800451140100003118100003040034050400e007034080301c074044902c1e030b4207a43c0020340c6d818 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 488107140 1250 488105890 488105897
    0x90821060906061b070e01031703040816030306181406040b09011202010903050a03050903010507050412060507032723060c09061e090114031608150909150108060403 73
    0x418041d242072070082c40380304c50f070b0740407041c043c201c1d00d424070700780b5160b030340580241402c1500400610420100d44000009904205840d61500e85c3d42d40040f4003c1440313410541c6084208082051b00a51150000c0d01d00c0400d118504010030003044046e010b014004070840300100c01060003410540110409140014a5500e03180c1c00c0500780d4850144200e000d90400107148170000200300d0901821407614003983c0c070203982e0f07006841814295007019014200f0044108070400150341a130584400c142e41c891008903c1d070f1641c41c800c601419803a20300e9100100404820080050000040c443c0700c0c1c802d0841b60212007010010030581041156501f1a40d041440040c00c26507040d001050619002080c07507081c05011120b040300305031200c1c600b40101c000000d00641c5581c2000000d10300703c1c1c06d1016540f5500e807104060543d00200502c50052201c0031700400c00302d0802d50b4000c1151040a01401818909609056694335249a9081c007903901c1400104640d400401c0c820300c5a034040d00e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 488108390 1250 488107140 488107159
    0x52a0d02060c1e0609150606030c030a1514190b03131e060e1510120303020903011b140306210c03010528020414060f040909082106 58
    0x30244032141d4040220000c8900944490f0500525011142d607074404890006090034903290000c58035100441240100030007140c81001800d603103040442c0e6110846003009038a9440e1440d08401800071800005a14845035002280c5492900540065680c04817449180071a6910049001d01d03000c3c012455080350410015240040c914092040310744901051100304000c0c44517400401285e003811150a916031a00e48456078003002680320050103d14000300394200f010005040008910400c60300440e04208441414000d6040c1c50000c0700c00b40003480402400f200c0455031803140801e103800700314000700819440360201d09603441108040c010860080d100484c0e009607401c0d11555072600d1040fa0314000041d00d0a0041c10701648607401104034009806e406900c0440b074029407460064070510041194030074042000726410000c0d9030040d5203165400c0807418602c110f400682203e400c3c4203c2c007042140071802446014212104014074126488002440b000151045076000343c150 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 488109640 1250 488108390 488108393
    0x70906142b0203010e0414241506040803043003120209060d1a0301180b130c15021c020c0910120803091902030607110712052a0d 57
    0x80200c1c003030354890410350500e0001200c080c1e9000f6000300c0d0952440c40c2c24030040105a06028405019404c09050030034198202041c84658040021070721410003408540255400301c0c0800340498081c281c2c40e40c894403845941c2d9179030700c60b120f203101030508448a680070096160300024486010300c2c030703080e9515054608941010b18101091800c1d5420012007450741c2d210ba00400721080610004100c0c00003d04280324403841c40c40c90b8500903410040000c0320601071350f110344102503021134402d81c2c2307440707000f2842c011400500004280b101709010110300164480810150111542d080f607640480401021003044a810000b0015034482d504402e82882c2c14221158898610f1034002c1304907940c0c080d04592400300074020f490744c4500005225a40100b0710166a41c00c020a0130130880301c405c0d501090b680c1c2170007000c0001300450300025009070482401660001d0501004c800d80c18061400d120391103001d00d44e046150412402054542070515250f11808403000514083e2410420f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 488110890 1250 488109640 488109667
    0x3030601140c1f0902010f302c06070201020f09130f230f0c1e09091008010e070e01260d09050a0b090d08070311060703020307090614 59
    0x4000d102c1d80c24042c003a08002c0d0745140303440300682107011003800f0501e0030785400050843e50b42c0c0a0140200903079144500059a401c81c1d1044040c0ca1510342105201000c900c10030080200244ea40704100b4144a00c200e0300700301402000c034401482c0107840d00d980303449509900700e22400500f0340350404140500342301031501c0250b00030b00c4c0f1344407000404c1c2030b14400e170b40008681301e0350b0389096080c0602507500413000b1031100c015800780c1c000c032580c10385060400030340003036000300010b85044403210602039500034244003c0da480744401904407c05814100840580101a800303003500c99881c0401202c81c80100050365012500310329129801030b404c080750100c030309001d5021140a0240400116506d00080004841e240c1003a07403007108003400d01c5d04001c0c1010540c0c1c41114561000e00481da40790382c42d000744401071540181900c1d983c000619080d58040024002914035020368000c005015030541c004610030790460382c40d001c406480b0041503501024101e40403000d004280030f9903030400322 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 488112140 1250 488110890 488110897
    0x610050702012a0f03020f0f0a08040b0f04170c1309200301021c05010618030b0f04020f040915050a0e070b0f0909010303030f0b010302281b0c0f06020303060114 71
    0x11503d501180428541c0b80d5203404403d1030700440041e4405041e4014041d0103000c014209548403002c0c0046c000c1c5611020100d01503030141c04594a00059106840860b0f40d00b00e500034180105031050702c001d4822110380b21b003200c1081501901818015a091a101e4868036411650040b031900c0103054401040314118031180307066402d0765080003000c441056425080d00034040d2044c02040642c10154004c003d446a407100d40000b0030b03149000d00008000c04e8072654881c044254603081c5948034000a0400c0050500c01c0750020701c0d20342401c0620075142e1110481d000d0501d030078865922020380100031544000060078040d041110140400110b0300010603030440340d07400c0f00b41480c1e01c038000611900b00c2070b413045010a56440034a201254607000701c184100c003d080031030609036900c1003400d8201228003402d034503100340c40b000c44100f40591009000305162440341e0000851514080b41e0700181d60092102e10104881c000400074400001c6a100c1e11041c1e40b0181190032065000440e0340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 488113390 1250 488112140 488112197
    0x1005060310270611070c051503070f1110050403030f060806012303151314010209090105060d091e0b0c0414120f100c120b03070501121d0303061005070201 68
    0x43e2a0300c1341d0140005400c01401005016503000e040c1e243c904401c00c050a00900d00188a0000c103004000e12240c002103410381d44a101c1c282009280e07140340d981d030b0a0042c3c00c64154141c600d02000d1105150f410b91041d407451036502d0041000c203441d01760300d41e503904003440741000d1400701000c002448095035514070124407020301280d00c1c007001c1440401e03002c0c030304581c85000414105164003d2213801d03d0130901c0022a40021490002d004001c11a108414014280180c4001400d07c1d42c16006500080e1010342244039074081c40710404102a240510310070a1b60070a400c403000c03801204011048500b12861001e4031843c104020301440413414221100a105002c1e8032188a01c1501c2400707145104040c5090024000c0c40c03000d0b010708540d00340003c0180b00c518051410b0740740e0b1800103a080588a09003841e1115180e82003240c80030b092042204030109811214003035041100002842c000d5500711030601100c2d42070b103c101c405004501c0082d00141554080c5418611003510720728005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 488114640 1250 488113390 488113403
    0x3041503020d06030b0f0a063b0916140303070f05030d020c0d0f0c0c2907080a0807140301050603040c030210091a09150912100506031027 61
    0x11000721010b4046402660007601d01d000300000300b01480c1c0d00c0100a0764410040b00c2d00b08080c1382041e1004801e41300d0aa144981c802d801c458012001c180c03580321440c2c00f554101d13890920b10b8800d01d8240c50356128602c0c03524644501e040410407030800020700d4800840a00154100003554982c11007298000d0402c0c0d417640010404a211442c0368002004964480700c014507559080071401000551040c40300740800010020040000ea0402d040c001200e610031044042c2c4160101040e00c0d1569030070141540043c001611400c120001018050101440e02c1d05041030761642801e41e21000400007640003403030104014040c40c40d210300030b1074002c1c1c082e01403109031944130790110b10444102c42490005c51a081720130059000faa01140d2281c200040810f401d04002c1404200f000441c110100082c190109200b0070540f19644000d0700c00c3c84880407500d5151090904000070f00040d22014042d0151901010b00110309000b00910700c0c1442c0507408003810080704424042004000842e0704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 488115890 1250 488114640 488114647
    0x151605090d06090c0902120c0901300903080103260f0c070504020d050a1d0307060e0c0907211a06030601230c0f060907150c06060e22050304150302 65
    0xb0542401301000600a04000141c0d104804105091240c40c01000c1e950107100c10824000140d90019108122180d40d2421140c22030100302580d50712922038004032485803410740503406040d841410681203e000301fa021040c090403c41b03109002240005906165030308210a8a00e0220b50004100220385041a10769003500c400014040e40e0100c41c0d4000b240e504c5d5828040c10807954403501d083e44281c107a114503c1844002015100d00900380040c00d0141e6800ca00b490301c1005021450b05510024010002e516090320060300ea03200b00c00d600e00d8042c0704403080910400c2c46219402d280920141c440010035021030411240b980024101c80c1084480c4600d0708103041d48000c510100a03000e49916100d600c20070220746401d00c040001e9000da4400030a008504401141e68000d0380c941840a030360104541000f07039042c60103890010140c86c900000080d420074003911a40c09010b0030f030514082265500b03214031007500021000303410781e0410081003001144a1188403000d481c00c0c1400f509 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 488117140 1250 488115890 488115893
    0xa0b0a090c09050103060c020109051b06070b070c0b09010501031109070e19080f030301030f080306012a0201142a010b031014010b040806010303050921151605090d0609 74
    0x754240c181e840003407503a4840c00103000300001401280b001d004144000c0000c0c4a03192109540c03000304080e42a68032039488452605038407848200c07107074190050040595400c241200500d0060307000750654417400100e0104810000600130603040701d4000d64a030304040c80c20410403810980c0034002c4801d00c0004c126510aa403100b6001c03c58103440506a40c0a040c0b8010781d060400003012003107500c642080005000040170030380641039054000a00c0e035100e603515030069907410040c550300042c0c424410100203001c0c10000300420218400c0e80e41c00640d8807800c550019074021010550f440b440510301503600c0009500250503409032000c0040b03034060401d4046400d00402c0b803e051801902c554480080c3d01d41d242405004210421f4800d1a00d45030094a5442d498180002402c10030005030500300760b03071000340000100907a5030f2450310099030710000d907a43d1010319111000d119100e1000804c40003e800b030322890700015840e0145000702c007004001701c6e2404103004a6855589600000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 488118390 1250 488117140 488117153
    0x30b06040605031b0a080f100213120c05040b010c0803060f0f0607050303010e0903190507050c090c0310211e1a0106030f0b10030209010c150c031d0a0b0a09 69
    0x2c110680e40380c0e4001001150005021560000d0b8100346c00684c07029000074404400016210641c004400c001a1540e11240381c90070050410791205503e0b440d82c0640400780003a402060f42110801c4504004144a94005440726500b2003005002018180000b6902e800e01011500c192480241180040c000c00d00000f02a03070891202a0f0311540b0120050090400107485c1da900400401c0080d4104400901c49680c107646c10039040f0300300240170a42d482004010004203468000040150302c141c50494150300715904102c600c0307404601d241d140021501c1a00380c00715201d4805488a0700023038081c0d110100414480301100c0c141000c0140c8500101319001100b50003d904115880d40075450060004d040d507450481c00f003046842e1803001c0c102c944e19945a000030422900b00581c4070203088006860b942e203650b2007d0b0400c540000c030102c2e915926071000702c52007002d44081148070449600300c003100e40600c046d00e4040d481900d0360742c08207440c071070042c2d8480132139613010580110590360030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 488119640 1250 488118390 488118403
    0x20c0c03071719050a03050f040e011202132a050c03070b090d02161a0c0a080301050301111903090807060911102318030708250609030b0604060503 65
    0x28000440d00e80640120880e050203249611140440003403030303c0721036450b07481c0c0300d8400403002030900c83c002804118840203101610020324100b1440c0b070056948404484000f40d440300b04901c0f5440d89038800e60b00107000d104010032510000380e1105031161640302c422489901d01c00080c00d000080c0107001280c00d08200400c1c2c400c1c813584e0400003034103005505034035280f03502c02c0c03900941d04441c10101241c0700905058085421412035a00c403c9810303ca50380b094031481e50314550a015202d0b0300410f1010f4040154100c420a8000700b01c0c0d0304014000d464a4014120510300c0b0140320103050034828070030b030401c94440b070103040b02500c0c08911341d4a070011070b05100380468034880c89d4524a0064a84042072000001160070100b540d0074406042502c84041400307404248007000c240c0300c83c0201c406000b02c10b41400a4101c603502515400c155646080ca000030b0709120320f844100140d403510070417010701210b6598481a4107681541d540b040b1200e030060070b803a001640c40d81300003a83d0782c04001d035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 488120890 1250 488119640 488119649
    0x1a0f011103030a1d03040e0406180812090d0203070c050402030a0605090f07091505070209150612010e0709030b0f0402060d0603110108100f03021504420801050103020c0c0307 77
    0x2e040c9003085070645000080340e07070039013580d0000e00082000180d0142c802c2d51290b840b10340040c1d1203140b28840d254907803e40b04050010b140204066040c1c01d00c803803440c1d000d861000c1c202c0b5030000c805c0000f20f030790f07104007000200070f011900300401990816030003640d0410401c1034041007060310341000c0347c8560340031a942e00080d0b15607800c1c82112a0000c3d400c5004d8010800160ba0020201e00c01074928801c1100007030281e03103014000b03400c0f0901c41d00c01c0e60a161004254070303900c0d02035008041c1082030038050b401d003289020004c541c1c00c5014001031021240d00400c25091a910150403442c0030000400580c1c0140d0204400c090b00a940d10602000d10300c50700c44034180c4000b10b40018080d8100500c000016184e83c40d00f400100d00040c2010201d0354111a144103802500031206001d0007140e00100c403a2140741e413001e403105504a0000ca0740f03082540c121207040c0750508440340b40c041d03103280200800c40510051005510035002454080c03213120403070345450609404249041d080d80e00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 488122140 1250 488120890 488120911
    0xb0d0f020c0a03030605041404240f0603060e07030210080a02040312082a09060c0f010501140126070309111002011a0a0e011502150709181a0f01110303 67
    0x2d25100300b50f05445200081c0400741c904001215100510481c0d40f11301500c06081c0042010f10f0f001c1e145601d08008501c61440c5c1c00c14040c041050f003000000c0e2010340001ca41407070070045200d5049400044001c1282c0c0c00030550301c1440e01c1c184041d10401d20280984485540810000c00440c4250150503802d45150380c5001042c50450622900280740410000100c0c04969001540500ca02d065072152102200d16a65503401038071000d2500d090005102c440d54200070000070300c03103484858201264001c1c0c03031344010b00c0c42883d4000c0b21021112450300c00c241e001c130013051034588a80d1246d28027501c500603000c0001d1900c0001600d01000c075402c074005039100c1005100c4c170260345602411044056802c80344850400c03074840d01d20401405000010040d079909000315610030000a1140c0c00100540c103070700d0070900c400400418983c068040440c0d0030301c52160000d01a8400e07540103114117666480f2800000041242d0310b013a12000e541040034918240000c98410310055018000e07044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 488123390 1250 488122140 488122153
    0x30507060207060905032d210408010b06072604030602030a0c03060602071d0a021213030806010903030f0e04061a0c10050103150207080d0608030909010e0606040b0d0f020c 76
    0x10011310415841c0c2085000e43c01040422402440580c1d001c090707510580d50340c502203ca0511010300e032a0007030300c0c14105a420005c448110034030340d1000313000356031903500288240307001c050910056200d01070004184142c0326142401d01110011017032411f081c580c2c0098681541d90700c2d484260f0f00f080e120859504ea03182550103005030075202e980c0090841e400580101460986e40890220303440d066880305170000c0001880c20440d070b034100ca01464401480040383c5c204025070400301c1140c9101100419000008070f45191b014013010000c90385d15607901003040000c290b00b00c403d031042281054000b9101c040100e0180310013080c0e0490890140205c54840b4002000c0300c0c91b08418a400c01015403515005202007a00c1980c800c40c01c02c007080b00540d4884080c0740c00b006034130404407004c40841c600100441c00030b0001c401043d031000d0442d01030310103980f5400b854245140c02e980320755100f9003c000420101140310064034000150b0000042c040640180c180103903888114803501580244 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 488124640 1250 488123390 488123399
    0x40512011a0f03100b15040b07060b04060f030602070f02120d120e06061210060308070b240411040807030311060906010e0402040209041b05090319020603130c030507060207 76
    0x3000200031881e400c0342e02d0760214000030046501c400d1504004c044240e1280b0382680d568443c0446412403981071512140d0b0740390b88142500040c0c01150003200e940d400c0582400442c9082d01940f4291160701134580c07029465680d84c0720081d0301182040f80c85562505041d00565a04031f08a1071008100002d09100e183c0100c0040c4404400c0c650045070528003450b2102c00400062000d074011300940f143c0301a20350003a4181c1c80d000c220110136000340d04012000c07082040700005445410300c41c009000881d19108070301e90070840325140c01d45842d01554503039043c0b460700e504882020200011002d2800c5d03112340c4880d05094268200f41c01060381654515210390042003134030744c008108000703032407a54100b8032b5040b925500030344041c0c890398000c1800e01c4140d850740e12124450a43c068010030702444480d0241c03d9402c4882d0407031180c0140c16402d00082c00030303202c02c9010fa5001700b016185541f40c01d03a03042081c503e007100355602c0c0c40c46400400000c0781008800054030b000e400400c1110b00c0e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 488125890 1250 488124640 488124671
    0x15080606100815011803080304122a020f010c0507080a03020f0a120c08190f020106050a1413020c0307050303040210030b032a030d120b030105131704051201 69
    0x201480c07081009000710400500e8035025a04240d1008240f81468031034001840004005c00d080c0c002419240002040c80308101400c6e007464026003203030301c8025082e6460701b0050108500c12641154042c0003068881c01440c0c003055101da207400504003050031044507101d01d4a00442d54104010580c085001d01d01450307010403800ca00709400000030725022290f40d0350711006121001c82101403000749006030302000040f03019600c03034070051911810308654807038005110051220b1280c0255292550200b81420400f103198250b500511401b0094140c440600c400b0303884540b0030400c4030b42e081c880741c0c007904014002061300034054030040d6100e0500d4010030083c3e100546084041c90f11300094402d09407000310310450402005004450310122136112100c1da84080c5164a501d40a0007030000d401940140c0b41d5038421018200800645584500f410300700c0e40282c910b020300110341e015080018024000c81400031400f1000c0c03070300b0a035481c0049036100e500d221880c01248d440f061a5100c4804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 488127140 1250 488125890 488125909
    0x110301050124030c0e180414010501081513050a0b07030f0615120603020909100f110f0c1006060903020f090402010527130905060112050c010f020115080606 69
    0xa815400b040c040c1041e0001a0100703907907040c040c2407540300c2044ca445540030f0301d84102c1280e0302500105400a1022a104142c50b044030100d890342d0003000d404402003814440c05044c0d4004000038401c507514002d6000300c072031000b00307611038080030b00ac0c000340043c1c0140a0304280d0741c8101d0301d2041078100814080c0654849402940d00c480c54420104200d898041d0150b26940740350800301c0e101c50082c04014068001ca40000c0c0d001599a4240110000c001032030103515600d00c9030400c210046180030754207079864110b0b0004c030790002344113048003500107030000d210307940303402048800908203c6d140c08162240f9510500124039280803c105600b44030700071741d018007401c4a444c60145010750000c2c1181c0501001c01d01180c0d6074001501416007815158104400300038901c01c1c0c403d107140c61280142842810031991409120300014907094900500f91801d644900901039200281004541d2001343d03000d003100b10364890707412915100f4048180c101074051100500000d15280d81070000d56013 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 488128390 1250 488127140 488127149
    0x14060f0d0c09080d0c020d060b03011a030c0603010312050a0909110a17060306041104060b0d0509071e06080c0f0a0c020f0a03080f0a020f10060801060b03062110091103010501 77
    0x3004540302e00c0484d0390210000440036812650b4030322028003800c008000f000e45194007034040d0301c1c0541e401d00d0341200900700b140e1003c045003154250503d40c0180a00743c0001c0c0720051884049042c01c03203165004d1009002d210b0303054504410240d1b0b54244010039100d03516040d400e1500d00058911416500044003461a081c50714401c5c2d860402401090303907104000d00c09031003025a1110f03c80303546d40d103400100007007001034a000e440e20f1030455400001c040c1070b10030000a128001000502807a010521045000d518400342c03001407500030159100d403402001d0880d01c6004100c00c42140d010900a44070812075582d400d006403125105208001a420001521465048400b000020780341c104540e1001d41840c0016103ca04640042e403030b106030242d00030914021881454003a0007a68008812110200700a004065403001c5c0d840d08c030702c401e581e1301da0800080d80e201070b20004441150305804800108480440c00d101070082c007100c40045080354000302000103040c5a180c240206405030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 488129496 1106 488128390 488128393
    0x50a09050a0e060103050619060302040603030e010809061308070c080102030711070e0106121a120d0809030307210908030421021614060f0d0c0908 65
    0xd11044800c0700c0140d01e407081e9820b004000241050407260844080d01c2145c80b03c42d2009070380b001c80403803801c0300742d00d41c0070020060312a40304140055029598007600c00e030740d050005200c2c120240440e0020f034448030511021454819450030866840202e41f55111040c0c507105a04640651001101d54400f00c00c1048468002500c40b2800f0907607400e0f00c01c15074a4015022464400b030040c800060011098000215000d40c88441204c1c1c0003100c0201140c2d81200042401e000e404d0b46070640e812260515120300c0d0098501500108170310040c50861505010042c01c4011030400f842c2c120904d041d4138000c0c0b611540c0030440d4950040812562450b00d42400c441d815412a0242c0c400303402d0400c80c012151002c03929507001180d40310801c2500380b034007118000a01d100103030a54811020401e565107060481b00800403e8001800815000c0d5086800380070101c280d484030030700b03 = true := by decide +kernel

theorem cover : BRFrame.Cov 487949640 488129496 := by
  have h0 := BRFrame.cov_init 487949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 487949640 ≤ n) (h2 : n < 488129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
