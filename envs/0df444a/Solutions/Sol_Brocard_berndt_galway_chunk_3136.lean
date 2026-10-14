-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3136
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:45:43.487819+00:00
-- url     : https://prove2.me/submissions/f556036e-20fe-4fc7-998c-4315ced7e90a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 563848920 ≤ n < 564028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 563850170 1250 563848920 563848939
    0x60105030f15010308091201060e06010e22050c070b0109020d050106110d030c02150c090a0e040305031603020d090c05030d0c05030301031205070c0306021c0e0a0f030e030f0a11 78
    0x142c0c9001d03280381140e6100694a841c0c401500001d08000c1e01d150042600e50300e440da0000d09981c1048045000c2c440030780312070280082c281c0902000303c0c0d030810048000700c045000c040d62610282d00055004200401c02d50510b075541d51081d040340020f0384400012a00801da8010411261042c01e0041c844d0b41020010244001405515504809251400e2503503030f00b80300210341d0003030201d00100701c0040031003489890050f004c0034032604204d101c2d03402a0603448004c188250b503146500e0142c0c0d010388800e421690b03409080140342c084007901c0f8003050f4080c030004c00d24200343d01408140303d00c102ea82c000010304007010300d403034400480b00110800200c00c180d0b130f010580100859040da0382290a840c01c20140320b10982c0d080c45008002481150621000014410240c0c0074280324040e4045d0b004052001400345001c0e144020045001600501d0440001550680170300050501c242403005803006031b140001e0800c240000700084503000340c0560420030480e8500e055503d03408035140c515 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 563851420 1250 563850170 563850193
    0x2010203101d041113060f08010c14220e01091a090c09010e1c0b0412080106140310050909010b0102010b0603090d08090a02130f18020603070302090105070c08060105030f 75
    0x403402c4040c002415602440002c00100d403030380c01c0c41e220807140806040c0000d55482042c03040b880058801c3c410954a040e000c07001ca41c0c40f9840140c030200101e500103062a1800340c04220900001d200c0300741142e030050b03000a07000103480300a80200100c01000071b410b000300343c0c1900e54040411906104a005000300460101c0d0801074604011082ca05285009040c00102d043d11529103041048003842d4600c07a030400c0490516181301e00c0c0b054002d5203d01d00d000c0003d80d619103080c0600300214076141c4500c1100314410020790381c05501e0000e4984040c0d07998021507102d0760282d0b010350345c0f65107601e202c41c22540c09018041000740d0a07a5010f245107401c000c015114410b2034440400c1043c2100460030004040081c280090340007000c0340c03401041500c40e4801044814100114181000003031040d00b6007052401d813105401900c0c50341341d551045400c0b8001d6101e809854140201840346c000401c460002c514098032524000b03000650400082503d022180e80c0701814540c8521201307035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 563852670 1250 563851420 563851469
    0x130e220309140a0b03090a05150105030604150b0d110f031f180b0c04031e030f080c13030c030b0f10031e021c15060303021e0316030201020310 63
    0x4086604482c100d1040c40b4100c1c00041510030164485405504040144031700350802181c0b140c0018031440490300c6601e000c0840c81e401c01024418290b16800680c00200483c0210b030302c0c84c0540040c006c0001e40d4859860002d003445083d004141c610341a4020a0b0f0071504151001d2883c15004500408050941c01d020480a0510444100d0020f4442005140808505242c21542d075031140f100c400c030f482c010102d40000d400c1880199602d200c03c000c007400c109000d841c065416509540c1c0e07809442c1061206a514110280c8401c0458108000311310741c074507a27040400302451040d80c5c00d0000c1c602d982006000c0d440d01805d001d6a20540000380030148021107110350403039a00a0718001c12150448844484e01010840a5004103189019500c112141210460746920906030301038401540350000c8111252400000e015a11442e54404c1c41107281d150404040c2d40c400c00c1703034940920f0070300d17614541c031488400f00c0140c0c0d0084140400342d030746110404042c00c122920078039400f00844504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 563853920 1250 563852670 563852687
    0x1c02040c081b0405130f09080d0b1c05100c27030b06060c0d271503320c040801020f041503140703021c020310050f0f011e0203130e2203 60
    0x2030f00d00b03031b03444c110407104a820390070140c102500107491a480b204500090f102525446c02603c2c811000d11209000100030883c3c1219a95008070060107449011100c010041c48080700304018002d44566406098480c4e801c0d00b4844500c00f085c0c203030028a91320b030403a070940707010340243d01c21401400b620000705070014481c0020045843c04984268503181c20489132502803540c14541010b4083c01715000c6c580c44014005200903a41c2081080555503811100025108607400f584c0304c40c4050804e041c103644103894000d011240c440703103055580c884080c01c9a00c00144200c1c80369001c01d0801225281c40341c0c0c0940c110700785c203040c0410f12031010b00ca2a840c01c02440c0200385940442c11842c0d91030013050707150b20f04506200440d80c90904e00c51402c40c2c01440e1107014030a400039020f03a02281403c00745000307034000603115885208100e890f5048031082c80003600c0e08600c028011411260301c40d03c000ca0041000310f00c0c1451904080c0102c14581d11400f01202110307910b00c5000d0b0002c1e5200c8082c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 563855170 1250 563853920 563853949
    0x509040626011802030c090a140a0c1b170703020c0402070609051c170c09031e010b040e0604020103200d0b090a090c09050603010f02040b1305030d0e1c02040c081b0405 74
    0x11f24110396103c2c0b10020080c080404100e403440c040404008502807680d22088540d0740503103841c0b010505004072400769001c4400000e2840b0000100d5503600e4460101402c1c0d4140301f80107903294825010082340032a08120015100e071070315803000e6024020280000b2043c0040540c2c00e0384030440311580030701003469125a00c1003c035002c6001940c031840141c00c1e03990b02400141030751450000030f010012030f92510010369406510300655900e0b00c4c038251088854003080100a403c1e6a5240c1d0015801404030741c1121001e9051368130810103604d400e800034331840d407400200160b648048018031002200003032000040354134000401d00441e20f0381b80480125600c0e03a0780400d090b0340f2000802c0c054902200070070f402c1c034008038000c138401405002500051811031186804075595000300f559a00c0c4c03c2c030f083c4010541c0040c0c01c0701c144c10701f850080300c001104840c1140360300307090740410115440703044200001400c0500348040d12515524954031011030482240c207181c04c00d00042d460700d580000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 563856420 1250 563855170 563855179
    0x41a03220204090f050706120207050a0b060d0b0a140105150717190801050319080f0307091508041505090c060309010f0e0d0e041401060509040626011802030c 70
    0x21018119552500700b83d109a5000c4841c16802e107041c90019541d40d50b074001d00300482c0000c100c00b02c405440b07200f130790300d466000402440c51700015140e603004e89070050701290300061807403100404100c603200c3c40c902030f0854001c0003652400c500e00740e0a0003001a00441c0c820058016111400c81900055076003841d00300001d809540c4075074a14017003511412004442d9040805000d07210070f9044940d25040318029001d40d041007656281d041d04030340341c085005048441c14410300458200d0301c009035500c01c0d102d080c0000803e071a0726882d1048900c421103d000a6200001c100801031401010918140d40101c20711443c00c249607060703142c51603019554000c0102000052025100f50800501d181c2d00245c108841c040c00d61080d81c0350a0500107400100b601060301d03c0040c1050f01c10700080110141c0b10b0b0f8403503420808100c1c0c1c0c5a200700c0200d907225440303060115076141d401489850b4405400d0095400178642d002c6982990460758862440703110025aa001603107000c2801c0700000012107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 563857670 1250 563856420 563856481
    0x5070c0b15030c030d02010603030e0a05010f050d0608100504021810091802040c0306030506071d010e0315010803040911130501030e03070b0702030304151505010f050d050c041a03 79
    0x1011902e0180f032041c80960602c19011401580b54040d808141900e0082c4d44041040010303509000c1215641c0c07103900d000a200840b40980344e44100f01a0a00818105011880d55941c1032250710707010251500d040e84555a2040c030045241500d102d46007200060300c00340700391130030074072251010009100724444030b40c0750400c1c2100c540000401d40c5400768000c200b0041e40780840c078020024041804215180c0c0320719804148044d00619891381c4c9046441450040b444a102c01100c24a2103105060340501c103100f100721a4070304013040103029000e80b40055850300d02d048202016501411060801d9410400014803031441c03030144001502c100b03080108025105d01e00d005e103036104000b0003404c00c02c0700c5c42c2440242c0e90b0200045028601031141c08a00c00e506074901d1045401120303d4240000302180d00b0400b950150046c0300034003515040050a080c0e19602070030594078202c41400b02070400280900c06620710b62600407020321050310075403d603d4886070354100900c420040480c152180c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 563858920 1250 563857670 563857711
    0xf042c151032041a0a120b010b1306030c120e2a060315010905100509150c0a0f0c150207030212010c020304090e01062d05040506100305090c040603140105070c0b 71
    0x84c40020250780203041c4070201a90303650160181c4951b1481203d10322001d1000040784490b4800365403003120032016a0341c801d45486030940c000c100d412041000c1c070403c408080e144507118440c050843c00c5031006031100000c20114104422200c10951440d080e12240c0c01106440d04426203034800c00c150070007605c015440c0010b0b5016891a40a507512401c3d125851724035951090240071101001d66a0641051410b081c00603140176000d003101855002841c200007040d60440c0361500d40b8003c101c084a6030b40c4641c8880a1900f0402640300580d00c514410000c60070701140401e034141c00000204042201d08034000e481703200350702c52460281d0300ca02944071206000e50020740103290b07003006c0310441140c2890741d103d50071900740c4031032801001600c0041e00303003040e000e028442c4070028040080340e0814003047d0011b002c00782050100344191030344e50600c0d49484c81044055400b40502581da142c00d0040700703013940c000900c000b081081e4503447c0d00c0064000442c550304007500216240380805c0c113 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 563860170 1250 563858920 563858951
    0x806060904062d03020d02130902090702010c17041703040c08030313020111060c0d11070c03110307060311090d111503060f042c15103204 61
    0x805180c60350281c40d102001900e0800326079195401d00101e1a000c0036a80c0c0300f5a10300c0a0455444040e40004440c03074100e0052030480d40203681010902ca0009018a440d000705807403a0f400c692a40140c7c3d5504500034240c0e4003d5810304000c03144200e10a4a440c1035901c0c00c506c2d1031002521070041b0400300105003000b0300109003901801400003220749034502170408a500b07046512042e40070030480798991001000c04182c076441043e4441d00c1c6e83c50188410301c00002044203004169107a5401e2005030001611140a040294003401c2c04280c4036048000305414100c1661004090610748918038903c41400c02c25648103034000c840c4e00a00030410304052806080c01101c2c1a13109410944481801c5142d0b005140184416030354410304003c14024441150810510700607120554103404c0420030100c01d80404c0d0103400019504401281210100301c18070075a4100300de85030001045c0080c5148541180b45504850043c60400c2003100039030f841280804003150040d80c403079480b5102e6090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 563861420 1250 563860170 563860177
    0x3031605070905040506061005120c0a03020c0a0b04050f060106080610050d0f0504050118050601170f0f011b080415091704030305300f1308071b0602060115080606 72
    0x500e104144128135240c50b006440d10320444000b4402c40440e40c00d0b040da140300e10191401414202c601c0030311034039026546d524036003080c8078800805800708080405000c06000c034104841c4180c400c00101d0401d0300c2e00a0408041409103005a441800100512075004031312a800040640c0d8205c40384115441c2110140306840d4000e030918141150404107003603aa102500c101d00440007008100e01d0400100c181031120750020740951f0081e8010701104642e4404140841e9036081101e10000d0070350340f194200a910345000825943d1800a0007805120000020808000f1701d0702d4520b9107071696607110000c02c407041207500300e030340e80e100714040042a04294510070389102c0c1098841c0d54a01e401000c1c5e40c00301114038501c40e0140511954905001609081d60b1014030701910203540329481c4000b000d000600d0b850b8008006900203010501040c018050103014004450071031051072800e50351803c1503400b80d411948071030010032882c4400b5600b106503141780c0c40d19000944800d40041c00900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 563862670 1250 563861420 563861429
    0x3030f0c0307020d050a0c09050c0d0e010f0509030d11040320040e01150f082817070606050315160e2b12080702070b0c190b060109050f0303160507 65
    0x41e030a486800e200e00007032141c000710307c1500c40407001601c0d11080015280d060300e0500044105000038050b2641c1504005045d913a040c00018006403c8a500d60550720241c802c01c641d0b4100140c140039419182c060101e60456152810b8505841c6503540e00c842d400c5600c40a1910046150107001b43c0d580d41c11008000305428000e0080c0c1c242e03514411110181171280e214400d0b02c5402c00181c1c8440440d042c1c1c401440304400c503001e04c03508040d0740007201c0810011201800803001c00c410070951540641034440c05010005142801d1400307044c40e115058115807400c10030142006820000c0c1103111020319005d10f03068800350080d8000c94003504003560444601c3c0c0c03030b01200c114002d00034081c03d024140600e43d25040203480202c1581c50200c1510b07070b5401078011071010b100700b410074002401030036000d2044400c140c0b410001d1204801c00c800c01220f0b00c2030b982017403040c15a400210000034004c201c42d41c5403002c0c3c1c1c1800007542c9100d881d4151003c0410842261309004090120308001d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 563863920 1250 563862670 563862679
    0x605100c12080c0c070e2202090402090415020d06210b06011409130203070306060801080a120909020309011a0f0d0b07170f010504150605030f0a0b1521040203030f0c030702 76
    0x2151100006c070b454080440310865080c030034240301e246a000c00080301c42120b401030f00c801d80949450b020702140500c01001070361180303018040056880b40c28801805002c41800d000944a07050020349540340b8914075400b0604031880e00340130085005450b010b40c00900c2401c1004108541c2441107015000b8101500c0d440700c546c40e441c0a413031030031b41c0055201e110a550708002e40d0b51103080c103450b048400e0080c14510b0b4004265000010850281c2d2591011181006104103a42e00d0400d001d90f0700496040070565141c250b1060b0f42d80301c404141d4000b03813040f10000540c0c0c0210001c1040b2490405010300100044400702c0e551600820340c04a8120080f44000c0032481c0c41c02040000d401c080c4501c60195292828000611040d00d402e01c040c2c0d456035071110724688501030202d242880207030056550070780c0c07456030050b941c2d905260100a1100a0040758541c182d243cdc04407944007114095800110101080200681c5c0100484408541e00701c0b0241c0c0711801a12202e145010b400c82c000d400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 563865170 1250 563863920 563863933
    0x50315011107060e0901090504030207030627050d200c210618070801110a03020901031b02010e070b0c030f0705030909010f05091b0405010c050309130605100c12080c0c 74
    0xf25404840700000190948038001640d1b80d6175413030400c403201214080e00580200e81c09100181c240c0c4c02000240c000c0c0b0244008402d04094801c802645601c81121254424104020f0b02508031050b01000c4c00403a0a1500c40c0c0500c0c0c1c40c0603151740c00b03851a0303445500d40d0501e0b030b404071402200703401ca0f034541c0740300b25901417521100f0710281d50092103034490b02c0c0c13180c0c00c800100320005028032007d1b000300c4c007082800c0c50440b42094000e90404100349040c1610345001c040030300400423881c100340304258000700d00f507050080c095080c00500d07040525402402c02443c0e60fa00b400004840301c111500941564582c02400c019080d4003942003076a500920b01c2000082001004020310181c2c0c80c12a4141030949911524200c800180100d06002072410b200401c05507004035001480c042c001e00c1620b1a107050800003038a5801c21090074185540d030784209101d00c0c1800300040c01c400029050402020945480300c201404034140312008210080d800512100b002105591250a50004840c2c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 563866420 1250 563865170 563865179
    0x6030c212e05070f0e0d0515150f030a0f0c090222140a03020411041206270803040813080d020f10110d0905030c06070309170a050315011107 62
    0x2103005000761440c064281c118a4a503409407940709031800f40c44162140380c101c81584100b034419100380b400169122000000a00100c4d20500401020801c06407030f60409150000ca521b0214100c4083c19016440f6030940c404030b80c40000b1510500c50700055110070340c0b40380c3e18200c0d007400408c0d001001c49034000324600d1541c6086440b0048420600380545c1380094070342c02d0107071000c00403504249d48940b0810b010405401c01c0e03401038400f0800d00c0000e40c0b500c0c2d01c405240b803541e807604400321129651100b00c13003038011015140004224840d5100321126440303444078039070382c00060806016031b0800030308002d0281025150000502e51102502c0311101c00c1803002e07465141d0000400039500540c0c80c201040252031003105100c00314210300340c1c04e02c1b0110b443da1009080e005411202d42c03000b0080c1401070401000b00502c6040b490350041007100d03051070301401c0d0340f8110300d80381c01c13840c4180101208142c0003070a4980c0311000d0325240750132002d04001210304003028820500a40503002b00404c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 563867670 1250 563866420 563866453
    0x50a02090a080d02061e0711070902040e0405060109091a0901180b19020306060a110a0204021914090603070e0f0603190506060708031311090c07060c0806030c21 71
    0x43c20b000b070300d0302610056910103050306802881c101d1a0b468500603100022004c9006020300d440f0841c0d0301040320381d10b94440c00f00b03c0881c0c0c0035030421231a0141890410080240420403a405020143d105009800940c4e654032500c41910440d400c11145000008440e680254000301d0040345051000402609600701031010641c00d54550045003604e1040050a40300c0c0d000302ca0180c0d20107420b1034540010345004030359075031011a00511380d01400c18900090303a81c40c00070b464412180e0b03e081e02c81701100000a8040c2400016542d4485000d01001e00b10b55600d8040c0c030307405059424004403210240c0c0002c3e4140740064590f691000380031040c09000c030342220802c0690162901e041002e51109030401440740205c1c40018a5518200005480b88100300550800c07103118540c03a064076221035000814444040302c0b81d00d0f50842c089140c0040c01018010001441418100000e0303608241020130303260000c0d0722005004854802e2203080039040c0b5040c03001d400c3d074440b0948a200c00100c01c01e6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 563868920 1250 563867670 563867683
    0x30a0b063907050409050309030604061b08060109050907050c0d090609060203031b1b0706050d180c17120d060608090303010f0e0408070506040b010501030f0b060d050a02090a08 78
    0x110301c02620410001d960207000304400c140010440010000103140104003c00381c410070204a840e0302091190544a45081206500881c480c450104e003042d4002514000e00c0d0070403480004002141c020f006150b41c101c11000f094030300c140c408802d030381d403456015602803241001440c000e12824a80184c803651050010060382c4580d9035011105a40e002e003241e0b40e002c140ca01c000270040e07020002002c240301000500600740307815241484920100b41d02030401a40354840404075600081405101d5080d204103010020b00c114070540510300d80d1242d04600880e40103161118904c2400e51407019420001081303100c489a14060b600c1b90000c0c140070140c15207110340000f04400102080c001d4001000792410b8807141020390050a103403d280000009001e007007035520580c1002603c000c07403414040b1900c00da0249030403804652600000500701e56030025a080c00328517081644401d45d4601044030200f041d044000b1503941c442ca0505030003440f401e00c90980c80460700314001111400407414 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 563870170 1250 563868920 563868967
    0xc12031d010c02060f1305060c030c070902030121020a33030507082212361e0503010c110c0d1a1e0703090c0807120305030a0b06 57
    0x1400410a031100065807982d900d06070003075000000f0300960000400c410060702d80301000c03003502808a0742d5080803610940c451068585c01d0b420014003020299000c000480007080c0c0d80780c04529640c0f400302c180d088480a10780c212a99403500082c0010741d510203303440003404a10304500d0404e94280c6600494803881c0491407010f51010003480207072400307071007001c2c426a02a100c071605641c9850345280318030981c0a8041c00c1c0041c4802003000705200151090007030742c0544503403240d84048007484096008446041030b20b1840032036040442d1040b00302c40c2048031242c1d0482c00011223822107044000c0003d4200c0d070740640c0b0f041b02c0030260f2540441800301011148007a1400000c0c20001c0c420310404112001e03000c0541101c1d0003c0c8682c00c080d801c0c1e4810117071004900c0e098006112558008415035041002a803a400a681030012401c0a5401030000d580180140307858080028091101c00c103000d028403d02000291441e1030f40d07040360031010401030007160313204211502c1054080c0c01010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 563871420 1250 563870170 563870207
    0x207021206131514100302030f0d02120906040902160209070c0b0c071a010f0f1205060c090a180f060b181201090506040506060102060c12040f0c1203 66
    0x980c00010380c40807a016026401e842d0b04540d0798500d64a410400c0c0c00c010a441c44010b036690304031518448642c00303050003054510100341c906891030041520303040482d204620240c10500c04c4181c91500011020000624070112941325203503140090b910340a142e210a075124000500c030310000085c000d41c0e2b11818801c48000109403111002250650b1040300010400b0b504900459000e80d0300307901404506100d0441c1000360a2051154908807000380c2c0003000d00000200f00740301242c070707034040240640140d015003415a0159110075990b0381e00a0058100310034002450840c43d00c4180086d000380486500d61281540300d40307207c0340105200d244011209281c4540400c6e0b001c059000c80e001d001d403080281c80c070040200c0801031103540a008410f8a9980c600320500002c07000d01807984204d000700060500d07403502e48000782c00c00100411050000358200580010080c9241c41c0641154125140b01c0c188540362600200d0f864594002e000483d407003012100402da88842600041c54a410303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 563872670 1250 563871420 563871439
    0xc031903020d05031e1b070b04030f02010b010e12030c070b04180603020f012d020703020f030a0201211104120c05060414060d0603060c05030f060d0b1305160801020702 74
    0x41292030b80816202800944030405c0c40c020460341258010390031a400600004298441000d01c171025800312004480840300e1208000c14141c100049241980d018002402005406400202004540d10f403da00c00c1d210810b4500c01a1001c2060382c185480d40c1e0304903040b2035140d40200e19140c1103031064203130313004414682404003c594000c8a003181d81c0a05000040c00a42c001503402e10342001d0f0402480e03036a0074911801440007500c10403c0030f019000b62202904600611211200300d8400a0103a44000c80060050f68000750000000c031507254000b42c440c9203804003001030211607088242841020802182c449003440c00e00307920034494a00401615901e000b0f0050a02540c440c07024020102070301284c0380d0620800030801140d0f41203000400c0d50703c80c6d483c0d0702126680b9221800080380801080300d91810490a03030340003c4212030008075485250350301c001107140201010000085071400d501081401c105038440580150762424a007516402e10390f000b03400000041e84210301c7c03036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 563873920 1250 563872670 563872693
    0x13120810050105040e0408030a1e09050114011a0a021603120e0414130c090f0c08250e0607020405010b031f051c0201091a030a0e150601110c03190302 66
    0xc0044130200c64882c00145144d65a50f00c0304100c83d04001e1400001940f60040c145501c2c125180b08a4400c00614001642109600300b0070300710341441007080c0e4209009801840805005940c5150709414041320315661030300004101d040c1000b41141d12090110044007108100b100c904030404114650740c0c03203070f400c0c2e415000c000a40d808601d1940095100c03901242c603c1801d0100c8900d2503000d03003045004a643c611015049a20b5140351004580d59000b140c0312440d4805c03800e94000c00d08108c0088200c1242c04110440c85c3d004400105010000385080c0e015100c52050320f40032500200308212541c3d69047d191036903801100c01d0720b01c0e4020750243c002c0d42e000c04c040c000140e520140407400002d40280780341610745400d800a074148041c2c06c02c0012a4000760400c1c001c0000c01c108810340320704107170b140304060351403006042210390404140c00d1106100515a541d001c10246020102d0801e0740d070009082002c00400300350140542c3c140b8103580505c00c03004010b00c034480c0d0f0072a0310b0007008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 563875170 1250 563873920 563873927
    0xf1d0102180f010203130f2603040506090d08070302071e0608041401140109021818040308280504021c05070308070501150303020c130203060d0803131208100501 71
    0x12440d0815016240e07144407140c80c281600d019030003a2040c01100d2900e015001400b48000380c5038070211070b603c0606c100b484202c0c0c00e070845c4925804a0003444a1140c01c902d0110f0701d0340141d019207401b458010802038003a5584a00000f034194000c01040c1e90340585040081d11140c0b01d0042c4603081d11059081a4030105010240707040351803959075603a03241c4460346c42d5115500401c0c9240c03110340d2508244600481210509030082c42000001030383d590700726620f40441e9100003c00c9201e4490300c2038045107224042e00d0103900c941d144c0380031045030390386440112906544448440c2d2501419501c00a010240e42c002130140d4002c070791074102103040c1c103030b0043ca4000041008059401610042000840341c0000c0d0403040e109a0000c900301200726170b002501c006941c0181d0050340841c0c2d144169050440c10b142a008110800350b103140703004004180d0b042c400210080c403601000001a500151405504080e05da00200000707180d80710880080421005848103007402001120002d40c5601 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 563876420 1250 563875170 563875177
    0x6050d140d0905030309010c060e0d0c17040e130303090c080d110a020604030f03030e0a080901080a0506030309010e0402090402040f0f060207150305090123180313120c090f1d0102 79
    0x90045d0318200c400d00c01103070714040c00041268047c0e02d5000507862075600b80700004170b00c94542d44202c2100c100f8140611281d000102c54562210308000c140b00c0300d04205001540101d40801c100d62a00440c42c04a0060070804005460b4507012100441c2c42e030300120f1102d045094035507541d488a0030420b0210745580301c20714020360041d0100010030000c0c4003c64071080240c02410001000d00001c2101402c0071601c40c011200355078000b03001c944540c0c000d00c5030390300540982c0c1c00300100e10304070011a58920421a0b030324140600007101c18141d0b0b071160121189154082c20564440381c0d120404d106007481405100c00c2c4000300031002c00c2880c0700080c07020440d00c2c60764686205020200064000308400b401e410301554841642c2038130700c000307580c1d0226032210300b444c030030f040303140040c40d0301d0509001c00380c02d1020307800801000d1801c0c28007080314000d4600d503110720300e840100c17442c0c00f010340b06045e400781c8400c6041070618000900c641e440701403002c1e09a05101d10101103142490300702e22 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 563877670 1250 563876420 563876429
    0x10c210e010f0504052b050d02060609090d08010513020d0e07030203120c0d140403020301180b150d02060a03150305070f060306061d030309210c100c030e030106050d140d09 76
    0xd0180194080101e285c442500042080c035a0100c0f407101c541c0303d040c03c2002d50720b85023026910503007c2c010f080c10800d111702d902002400141114040c0c04000038a002e00612410384509928140300f186464940d04403411400200e07020000700030019001512346046c2d2005a1203401000850304c41e4031007050417903810100c0c08011300108101d1110680c0ca00660300c0e400c585403102404080f0060f2402d10030203d21590b80082440c1d903a07443d1918202195004001c008151080c3d24600d41640b50019400717107a81d411903130591210b244180031801800c001c0320600f107015441c0707400814000040303031510640300d08000c00841c00b615903100380c05994103031054000254200e00200388044044d0070002503d8001010342c0e151403021800501c207042e41c20884800028951203c02c0702003410404100d44030804d40e45c0000707a4607021405041844140b1018090201d5035400001ca0b590070350240e40680740042840001c4e8580741860312013004450302c42071031482031000d40c410340c5015041413000c85 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 563878920 1250 563877670 563877679
    0x10204030b010e04150f151a040b031e01030b090f07050607020616021003020909101208130e010b0c10050603031e041703250c0302010c210e010f050405 67
    0x142d00c0c000c0420a0000014020b0392107059030704580307004005d10300a44000002c010300c081a030704c0c111071800300181903da000d45002442c884500c1191070b4404140c40455807211182c640360354501d1524420842c80c1229405501d0700c41001100f0420305c841202e0240043e20201c44c82000e20803011581c0b001a4040d49a2051040c8007041c0145010300060081120501203078514600ba0380c08030300d0b006041e0354043d000c00d8000c40c051107182041660070350300403085403401c003105d841c0004180400c5040782000c4c00c08500013500744a6001f01c080364500821070022260340301d6a543c21014100e40107000e40c071815001e8107440c20f1200180d80602405404000c01442c640080260303640040c1c00708202402c1803070000c2c840000c205c0c1050182c4103081c1032200265036548001d8520105201802c2c1080c960007e02c0305c00320000c519540090f0b426070b41c0c282440790703182e800703400c0c01c000307501e07039416a600e94001000c0b81c1d011040d07020f20b002441034420b884140844c1e050b0001030714a030159003da103801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 563880170 1250 563878920 563878943
    0x2130203250c051504062316021c030e0a08190914100f02070512010b18040b0406110403060207030e0f0604061403060402190203090a240f050d1a030f01020403 70
    0x181307003070508401c0d0094401c52002902445007090004800e1514849a90a403031076000c000b40b08601c05440c0100c0ca0300781c03020300010582c0c1d00031102003005c10906a400c150381d400c0b030200ba2540800c4110030407508891055212840500f800c2445404c1003c1240041e51020001400c044519202484250000c080420034504030000302c13912020340c03030101300314459408001180d40b180c0001d00302d0100c0d00c80002c03400100c5e6809001c0c088884281015100b07102c10204400310b9200b80500b60016030107100410184081d10480b1001d020300d41014000303500c0003500303104042e00000030000e8558292405a86862100100580c1d03000750707c517a101044031640103001001460300155400000100010704149002e000040b02e8205003c2c00005a4030000b00041503250075500800106070041d108800c44292444044142010300c000d242801031500f810701216010b102900d41c85640d180e000c1100c045140090700c187e2581152081c0240160f2090010040e418000c80b01a641c00c0b0051500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 563881420 1250 563880170 563880193
    0x140403020a02131b05040801050c0c030f07020406031a06030d02010204080c060d090c12060b0604060509040504050a170706050c0a170c070b0a0b09060409050d0c02130203250c05 78
    0x158183e1080164880380d40d03508008102c10001a010382021120303610180c0b104d083c0900a403c50f41c010740440c1d02c1041c1072208003c6a107000080300c42c6c1200781000c50792180e0321403001c5005003c690b0001003801a40d0840880e000c0010f801003440f0b544124111040b00750040c0062f4201d20907802480415001201d1120490a0980c020078076104540b20001d440da201d034580a13103641c659000070250400864404051290601418002840856003075250038500703031000c1c00d144903005880e0300030b988a4000500b480b40c240000d00d0050380040c0740c03d6000e5807108130240349070300142084400b1440c1c200820054840700b425100c840f84551a1102c0210320010714062a10300202036046900c0b08000600c005510329400d1401009414404110010200104509c0c10f500600f550300481c41c11400001150001480f10400c034220b09040c0302511250000c15081e40d4003660700c07031189000105024210545c11820a141d540445420020301442807085507528423000f006011503110460b440d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 563882670 1250 563881420 563881429
    0x10c120e130614030708010b0916211e090c1a1e0307080c0702010903060b0a170601081e060a0c0c050109030f0e040e070b07050c09040b0109140403020a02 68
    0x1241203500038126012650300425070303415902990000f03500001074101000d4281420090140030304000c0c0000d0020589103c04500d42c01c1004112900995142d41070b40001c0f400b8105031f800c51803c40b202c1d42128207807900368402601da44401c034084000f46000c501e2000e021889106249507010f9070720700c001460609113003148070514115004001082000100b01c3d0448009071410407840d508268407440c01c1003001e0400e01c0014401c1e91104001c10409d001031380c0c82032400090b42d920640c001008100203000c1000c41941e07070070602ea5501c8000c0b1210903c1d000160460494079003130103c0d05e6951849181190700c1e100c4c004441c01070380c489802b041c800170654220395101d940c40e207051440c482c03258980381e003940d0f84500c0030307030110f171316110261150341c0c0c8581302c00d010a000b6030f4180140c80c0d50080882c0c0c0c4038079601c900c1c81d41c088003194050400400f03011017815650000d2604d8900d051500b4424181c220a124001d041d6240005000c413001c1c084200e00c0c840c580540180c03071025019000d10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 563883920 1250 563882670 563882687
    0x11030c030714010b0303030708190207050309040e07180501290a0c05100f0b03062d0603120406170a09030e1c02040510061b0c060f021f020d0b010c12 66
    0x1000c3d500c540c80760b085a10204003562240c0060f0b41d0305101c0d41408403d01110003541e1541000c10380c01003001c0800700c5e600104851a101003510f000440418603041d0300d040458a0304048010003142c0601c1341e031101c168004038182c41c0104580c04078401c00d00c1a1890020600f181203800c0c88050103c800c01c68052000d200d001802482a5050b080b590304102089800c00403440211300d030b842d041d603511341c10100002503008040c3c61000e19119000d8810030a00b6901c0050340d60040d5220300080e8007510284007021007603c40c0900c41d611951648005001d214860642101444d810030002d26140118011003c410303401d51540c084501c031410034483e5410841030314025104044280600584a502c200751044100c40c2654500d5802c00d2001011001072001c0d082200d4110340945c0e005c0f40c649018182100c5040c100a9900c4010b0034050f800e04844850066514035251080b28000e0301680041a1405c1011810490381540c5c03401507404070b02503480a0440810079216180362130040061 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 563885170 1250 563883920 563883953
    0xc05040c0e0607110901030602040923130203070b0d0b01022518180501050a0b180c1e0304050106060e1002072603040807030b10060503070c1a040c0611030c0307 71
    0x130603105801e00125003890001e030700c00c9400d60740c005020020b9507003910800c550644c42885001013068005c610b602c402801070039501b1074040801c80b90b01103503010031076500100015040780c6d858440d50449940100028804503015000d130003211030f07001c3c0e002c4400c11941420215404402801d01051002501c0300c2c10590000a986a4800900000342a6110803181c0b00d00004511307840c1004210b01035898801016009086011941d0303055034444a8890713110714441f408640303074600d01d20980c1e018802d0b011581041d903000024041440019082502560500e440d00405002c010040c01200301d941403903000107030004031040c046a078100c1d003844188040160444030421056186a0859126501c050002d40c03102000b00104160040714581c424411806000e80614000024003148001060706c2e007000842c910840401c4103503071202ca081c03000300d08601481e10f860301d4283e02c600d08030701130003010132a07100c800d4050b50000000c85144c140e13110080c3d802c00e44141d84248000d054001c0e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 563886420 1250 563885170 563885183
    0x7180209041e0507020c1c0807030302070f0c03210e10050c25080a0b01121a07080402040e0102090a0314071703030a150e01060e1f03090c05040c0e0607 67
    0x210058107150581510886440b40140018070f41010200070713140001c0800344c24040c00c514404c4402c1d0004020413500819041880d0b2651520249400c40c02071040e214000c0203416070391007e00900c00e448a01009a074803c0d1070a0141d46040c9844004440c2a0110b00b0002081c441980c00d0380d00f04517105001c00f40742410f046040c44141d0700301038141b6100c6540341e980089041850503500144000b039100038103489029005505442c0c0b542c02c418001401200c01158a1041990801c4160b2500b03805407600c4032076030542c50520f540d00504141c016203059200b1814150300b926840303010701c2100d42c4070800806000714246981c0c0d5001c1c42e20807145440310715004691000540720343c04010300c1d0800d050403000c0e690b00d1428010401c100c55224a540c600f4181e90300003400880139840350941582c40d9800c10300f00d4002c82d407000581000009d401503030307007520b411b4403065016019080070030396521030000c160f00991108217000840300c0d854440c0c00014030740d1505001a0034407d0041051900070758 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 563887670 1250 563886420 563886431
    0xf120709020c01150f0302010c080a020c0a0902040e1f0612230f0a020c072304063b040602070221061b0901020c10050c0a0804080f0718020904 63
    0x400c0c40049070050329000d051a5111507111103c9110f108107000501082580400c10034110b400090a030500c09c0c130000c0003134100140c40f07072a05008008030b0564020040c011001aa111105100a90014481c0500304410300c00800c6003c070350200c0440301ca6603280c40103d08545001c1d001c032580081c06a01d0314030b141c2d5541d40d1503030881d001c11040000b02025031081d24207040c519510030030350100070b24507020740f44140510601181c012a01104850810402c0e441c103c01c95452520b0740f150b5400034960092814900046101c9110b95080c680072289803588200242e12100000654600140c01c00b110032036130000d40050300c942c0c0681030b41070014103030440c40c0403480311030860400319600704ca0041d442a0100501164501c07411030b91402d203840314905080c0ca100002c3d5075800070480480c41040700c440702c0080c00b446035041c0d0301030f401103c044401d0700d100b6040441c40eaa01078000c0203c240100c1741d18015402c00003c0140486a0076000c0c0c80707039001e142240304025007056415561040d01d96 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 563888920 1250 563887670 563887679
    0x110a1104180c030c171f05040201050d050a0f06050f0105030a180507171002070f112b0210090302060304060504020f060307031508061603090503041a07050c03010203060f1207 77
    0x1031654001552181440e44002400c01c0f18207502c80348170f07100001c1e03039520243c0c41ca0300c3c902814200b050f141488030380115880d1103510050310103006062801c4407075852300c000c108040c00c25811026400c4080241008095203d000340141c60000107070343c41c0810b500b000404c001840541c4040c0a6040c8031440200d02816071ba01c1e18200740d42507004500c9c510104d8842c1007520028010700b9101a20820110f01e84070030365072071190501da4444081e041444044070303480141c880144400c00b0008508010602c3c5810071041c0c1c03161000141c3c2a07000c3d180001e0580409409043c6a1044c0e035001003003142159280d50310030029100c014030403a0494888110005070b9103451002e180103000d20b0f10041503250140c140c2c1d034034284041d44402401d900000a11840ca1812800b41070a28101d150202d01110207090072442c51040b6170014002c1101c5404819004540001804489204800b42d54840011400300750a03404140c03047c980c458501c50110a580c40c0a0030314640030901c0d48c2c2980da2140d40c2d03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 563890170 1250 563888920 563888933
    0xc07050304030c0303090506090a03331508060702061902070c03121b02100f0c0c0b0901080115020d0e011707091a07080f031e0115110a110418 63
    0x10342e00c2101c1000380007900340101034001c003441c006040260303200380c10b040e12100010401e1465100280641741c000c0a480da08603008901c5c1540c0328055008002c030144203044803c000c12400d1140c48500c02c02c50310206a1820204d203017800351400d90300601c0c0e030342c8441a1034145004103184da5640140c0c200a07450004503100501c0000f540a078440c00080e20380caa002030f100006168070000303543d900084030f000584e02e2450010040100e4901080813110740070058507103d05a0360013070146200880b00040c14034600000b421802c1e000ea030380d40c0c00e41c1da03590b2540558101c188800d0015070400302c4503046442c42075500c01240c920501d060a0070180042003c0441142941c00704002403020000740300740700600403120740d820070b942c04c00392901c0c4643d01c400f07150740180101901001d6000012a250004140302880011001c54113075100c2c0d6518442c4a0f4103990740c0c0803000102c1d0988000000c1410049841d40007280c10070450103280000400700030041c01c601c1c0780b442c50000801a0140414031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 563891420 1250 563890170 563890177
    0x604180f03050901082a030709030501060308030a182013290109140409051e010f05070e0637030e150601120203060406050907030b01030b10090b030c070503 69
    0xc0e1552540d900043c4001001404000c128500d0703030080b02e0108480202d03145001d0304490a503541c3c5612529940c404640c07403c120362001c0c20399802c180c2d0200030300407518021406141c1c0e9800811183c021495a111000e0000c1e0002d410541c0240380030040700765209851102c034000414490001d820300e04080701f21001c44c8419140345482c0325100c0500b4216400403500c0038001d00b45024458600726840c4940c55240700c20600035601d594403a02009410010b4000402010300000180c1d2001e244203402892410103c0400300d0908000c150082c5c01180c0d000042d0b80013526461802403000303410900c680810316103140d6066160002c03c0c0c0d621017680707041d00c80542a90007058a404000700e05143c0000350f2800c1801314060001d014070b0380c0c2c000e1900704405101c6240035842c2d540e00d800040003000560300c51030b041014502008915503043e400340c469820242c9007040109620300034003201c2c0007403600c3c400100f002a101480003030300650145034440c241030f070b00503d001c00668881e4116007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 563892670 1250 563891420 563891423
    0x1d0a020912150604290402040306050f0f060405010303080c1303141015051f020c0306040c05100e090c161208221e06140c0c010f0e060604180f 63
    0x2080b220095020030052101c2542100048900b40074100d0402e204d011340c03051012500301204c21310f0341504026241d07074060b6001941c00c0a41003050b89003e03521148403200440d17038010304149950008100703161920a2905803a0580d8171059241e658010903a100c0c2c0c0110f0f0640303800038411000000040718900d0b5080d000b0914006003000c7c440310009032055400c55001ca5103010900706062000e5200c08052100000310035070600350507200103000742d062a14107000e86800d40a01c2003000148544c6603400c10495600b030f1032a22101803900c0d800c071032050340040a25030000422002c034481c40c1c9194043e0611400007222000e0382e0010350b80352019081e40313500060219203400d04105441c0f04c46150b401c552122284845111320300ca03038589089105045daa0211121450700322000d00680707a11111414180d00c401c011319003080c4209401540104184e400c141d03003030000b042c0a440f0980124811500c03044024881e0303403035107401c000c06488030240765441c0c1c0d0704000800c0d001c181e01ca000e01c14000e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 563893920 1250 563892670 563892673
    0x5040b07141c020d0c0b13020a08030d0204150203130308031005030a11190303020606270711070504020702130518030d020a17010e040b06010203090a0b0d151d0a020912 74
    0x4002520060f0810380014502410305c40c8044070300c8082074150120a91012014000000c0d040551001a040c8602c0341c002c22014400800d44407003940e01d070b40c0240144c9812480d161481900000202d80e24400c40e21107071040c1c04824420000907014001039900020100f038480149620340000c82e01c1c04003402c10540e2025440440c0f01c00d141010181800a00854888200224119100079603104405044503000c0e248150795a0011440c8000c803940d8042ca0307441001d0340b810b001c2002000c515985109252030701a84500090320311340f610031503148a0703000d4454402c04c2d4910000800506009101c00b80c100030f45045070082c01c80610041881c180c04010044e1603040741c00c03000b803001039502404080c0e04550701c01804142000b05a10340e1060388000644020b549450040742140240180075410000c01680440d000d05e001001d0045040400820443e1060114076401c00070390310311034008420054540700c2507648145203229409043d0788405403030204c0d00720101d240360500408403c00d9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 563895170 1250 563893920 563893963
    0x903030703050d0b04202a0c0301050a02040501020a02060d020c15040b1608040609140f0703050f010203064903021e3007030203121605040b0714 64
    0x80405610810580c8002550204141c16112102ca00c3c110110309002d1000d1002003030341c0b687e0319007018008100c1240c0d8140008960007440a1594803010403149034402c2d42028001400d02c041032080e1411508142d0003424001c0d01502404820b40c00a0182c1c1d4446408000c0c11550750707403c000c01542c60700d0b41020f8410074a4103081800c0c004801a20840d001c02c0103500b500425648031102c10380042c0c002c000040d0325045890000443c000082c0200c020b0300448080310030302032000c200202168016000e660b01020382640f194200d11007190041c1d030048142c2c01d000f28044c11254500600482c101140350011035242949210742c0781e00601901d05038420407070700304160741404031040c20264040e80d5010810f0104015031260005403102c00d812510f0f02c18101303126000160758a600c0050075203155284d040f420002e481e503000303001c5c502c101d40c0c0b55008100030200e14000711140130410b0b600c59040a0038075100301880c1e03120301e81c00d851040582000743c0c1d80080502480c0c09008404601100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 563896420 1250 563895170 563895187
    0x1e05090a080616020d170402040e0102090a0311240a0809031216120b0916170a02030103050c06070c03060c05040308180a06030608060f33011b0323090303070305 71
    0x9400c1120079905c0800820700c00c5201194034075807080784c1007a81200c4c04905070140d06001802402000890781e404400c059000051100050350914001800d03a8542e00d018242400d0b03001c1c00c000c03a0505071720100300700104007000d40700c0c02d89503801c1201071040d00c0c034117a804500c0950900341900c3d80d019103e003102d0f440003d5508280717020610002d1510034808030b0342200000780000710007003041140c920705400a506040c0724001e05240410070a010b00840d080c0b120a0000235082400300b1585441004a03100035850800f099524440c1e1200440701d075581540d0b95400a004a02a040701b404000c4c071010000480f11030103070920684002c0d034069038404200c10015800c40310392000052601c1d00c50280b00c020804a107032033b40482205025000c0d52190951264110141d000d06d40351304420920000141c00c0c0005a905c000c10241d80764840c40c0c1c8509035030030f14180c88440003400300d640000c075040ca1018a1600403d01e80180c071805090803140b070003007400c1d0741c0116030440c0042e10000d030054 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 563897670 1250 563896420 563896423
    0x110a0f05031b031009110a06170612060a0f0b0901030609030816020304030206070c0905040f17090109090533010305100b0901050d0219080f071e05090a08061602 71
    0x8000000c2e4400451840b04100119884200041043c1541c645500854046c00240c016403082c04a01a0070304040c107541d00b20050044070f100c1d8425181d1419080401c40c01d01c0c0400321311045010790700282400c1d80307400311020f0007400345050260b0342a8850712241d00036aa100356040c025400f071000880c61012603d00140044401000c0a00b641d2000b0745840d441680001620b0070380e541900c2d05135a030700301c509000d1200826a4011280a404d24041200700701d00f44000f2124544104c0c4c101c080b407854140c09038410300664400e0350001c2e8a06001700412900b0750031150b001541c4901071540c0c035820007214000004c09004001100001280500980d41e040c45403a610207949001c81c4034a606082215050f4031031140e0890402001064603007421113140d044520400c03100342e00c100910101c800180950760b00b00c5034040d20003d41c10000c1c200e2809243c0702c808030583d0044010070300e6420724007501d0750741002e01d844d60021078080300801c5104007000f8250140c1c10f9208142150500d948009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 563898920 1250 563897670 563897683
    0x30a0b18070308040b0f090616140a1e030c050d0503090c0603010509070806120a050c0a050d050c041d070e1b070b15040209100906080a060e060d110a0f0503 69
    0x14030035034000c01e820404143e0100654081c2e441580100c3c0d07482005441c0d000c1140140886c5542c07104001070688041306003040c24040301f92081c5242c3c0002400040700c0da46030310740150b004c0c000c440c04021946a00d10108105080c40340700f0304140a404450f9103d803032401d0502890a00800c100005004180904220100c0d19540450300f052940d810329003c182a2417000c4c264000f0b2041c440040340680e03a880c50316034462540002200c01401c1141440c690303c501080d03003103008182210000c1040d0074868110f0000907003000042403040041d00c1030100a05080ca004140c030300004c0841c02417030f181481460010151400064200c1c102103040c1c00200301ca92400c0041a4020480c400c00198080b0307845503c40503012681000004000104019200c1e02150310341c030002c0030805031603003900030440c24140c03481992400e086603944407030041181c400e070113841c001172810800980646030862680020700d101300210869a80704002041040314160000402201400c07010b012904082003003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 563900170 1250 563898920 563898961
    0x80c16080d0e25050604030f0f030c020d03030501030b060a081f060f03050a05060c210702070314010516031112150405010b041401050a1d01021c03060801061502030405061602030a0b 80
    0x41c10b18280c6992380703800b8800d014400c02855220351a140d0300515024007842400d654001c0c0c001c03004c150341894000c004120074001242c0c04100700000c40e0307040c01c10011960640d440c00005182d41446600c284084142c0d0341186104940c56800104484800c0380520303004510400c020610b1441d1450b109080441c000c2050040840030300c03922440f0640441c0c20103c0511080942185403100c20f001c03404e143c4150005886580107211100c9806015841a44540b00c80c0c884075519010741c000850642d60703a640340032700200007480714408091001d25882d800c10402905004040c811802050507144240d20507241c0702d901040c104044d00182640c0512104d091902914020100001901d030410201c8150040801c0301000d140c140d0003004802c001403d400010101c0a9a0000c01005056180035040030395080c540c0003d01040e1405815a900980b60090360401c2e04020038032156800c00f41102d940e45910b0506800981c4041c4198403209020781c00064052518880c1d03d900c000d4200700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 563901420 1250 563900170 563900179
    0x3050c120105120c04020f0a030c02060c19090512070614340f060e0c030f03040608060307090f0203060108060d030c080a02030d110307080c16080d0e2505 68
    0x221001905a4880c1074550403107103110207102c12003425282c4903202c21300c031350428070000d01c2150410300755000d0003070342c3d40d02e42d414044070b104068100e03211002174881501008083c00101010380b46500c0500194415180210825654400040103140d42c4081c08129401ca070b0303018010540c1c0280070160b0a2a072900c002e180205484034105024014001440444001c41203000b1100101021000350317a0040f0b90317251251000e09001e4001c10310020070b6901442010b84032107070343c240800c0c124030841c805005107080070326141050700c4c402e50040465034036009010300403a103c0c1c903d10840b1101075510703d00580382d02d0000009011b410303001c0c001a105001c02400d4500080d400391100410b20703800b082058a560f4030210503803440c013031402c0480b0414186681d483c0f003201c0c10000b4500c40d54860b69082ca050700c0301c1501d0304651050301445070401c100341d00104081034801c030040000a441c1c0740c1c006072105030001064104101035959035600200c400201c9200c5c2050100c800c00b4120407103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 563902670 1250 563901420 563901427
    0x7030c170a120e040b12010c03290f0a080d02032203150f02190c120503010501170408041703090a060201020306241216021903090611100e03090103050c 67
    0x444440a004040d0b5115003040340030604007020f9255038202d40307181c0c8400340400344613642c50380c0340030f010f048010410310020f0325104040b00c4030406002a42e0f804d02448045144100505c1c0034086400511440260845250280010701843c05c00c4000380030040380d8050b540321100d039001c0e40f4040e891010500d500741c0d5641002c1c008a000e06030f1900d101c59441c070000607400000500d48001c0c1c02041d030016081f4201d60200040c09400503649161944110b284500c03040f89041e0a6840d400f0070301429000a401c82c0040d0b408001e950142900f05000f5986207051654542502410304080d46485406070004600e100840c02c0940402c030242030b65000a50440c0f42141c04641507070108040c03040105110501d00202d410305808540c1001c00b0300201080303505e81505144080540c8545000c0107100b14000c040c05d51800101003c0016490303502c035060305203410011500d000e517018090404d809240300c807500ba5281c510550010804d42400345845100b080f002404a40d0014141d03c0001402c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 563903920 1250 563902670 563902673
    0x13b040b07111c2003160606090216030c050309040c0c03081e070c170403030e011103130b09030f0604030908070e09030403080f040e040c050405070e0d140f07030c170a 74
    0x81110f40c02c40b800d6160004040c640c811607942101d050300d01104441c000061480080c40b0080d001c6884980180030a10125680e200074004911555403a00b610341d2203030381c07040c0000c6d00c1076100360925801141200d00b040d40340f500080480d00f000c444100400c451200c10000c0640140030035a01c401e4510310107800303040c540f15210001900a002d4010081c0f03e031490400c01c00b000b410340d40172000c9800201c1d12143c980c50050705103d0302e1420315005c600d020500b0400071400004440c2001c0c0000c0c00015210315008003050240c00481401d54107018496803c1c00b4045c003008214880c5000e0b945000b0003a00c1c08540c10300f002401c0e00076140041d0320604200f2450400000c0b202201c0d40902100e903103040190410150380140d0b004244100030220500007801201803a041c269241124100265100c21005079003a4040c40c9000f0f800010a50701c5802044404501201c041162400c1c2d0710b4000d20400524209181030b08104c030301c07040c3d1010501c15184200c04110840200c800103280081d2603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 563905170 1250 563903920 563903953
    0x31009050c0a091a04080f0c030f07150813081305270c0a0201021903050601020705010804020904060b0a050d03080411030120030a110d0b0f030303013b040b0711 71
    0x49004040c00054003c00e850404c00c108000c55004159400a850039071003000b440584440109100500c244034450000600da080418000204ca0008101c080c400341000e0040d07031201e50086c0148000c45c4079051080101d000c813801000e00b4851502d417600302a06080401601c41302d0301040c4540c8031011060301401c8205280c0c650740000c01d00700120317250402864224068410081200b100f061551800110b858154000d580101026000e8405170303520781004491260003114042d502007109030100c1d01149580e40031800011024101c441c2841d19200451007a2a10101c124001000b030410401809282c0c1314110712444110001e0180081024449858a5203840c4001005800001059180350760f03500c00c00004032001c00030354132000d0020902008004106a0b1030103403e007150741100a19003c400c40b8140c40840188d114025060b0b0010740c542012004070107070aa90307100c01ca0710a8681c01005038030623446003d402102d8507141400502179028540c0c14043c6034050003004100040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 563906420 1250 563905170 563905187
    0x90a0b13090b0f01030e0c18012904050607020d12050d0f0501030c0b130801060b03060315010807120602070605010b070c090608060a0e160902030703060b0f040303030b15031009050c0a 81
    0x3c0c2403038045540d8a8680000d400e1035500181c581e0301080d450010152502c6c034500150480c5d8880305800d842404a024000c101c403510580d1400755075003007105103e64513001010700009400942030464000d050b41e5a601d444040c111030b0004110082a03181a841481c001c10074880c558103418003055246942c0c2e5100740030140581d0f90701010114008200c01d6900700280018019180280103059a03000c4001c000d43c01078030090700a0141010f915064100140a07a04a4081c1c3c0f005021251601c2c0a281101c8a103002c2225011b80812501e00416594000c04d03010380203500c01c8036511003c2c0d10b0900f010a510340d00c12000541810401c000c00880031071041da010704122000b02d110b403500c96401d4100100b07110441008510050041a19051640034610410803502d0401056031260341303c4096001d07080207007080b80300401050000034401c0d000035104000240c603d50061024100c104d0340d0b608100c4000044000b003410401480407940a003903001150b83d0705140ca81040000300030800c44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 563907670 1250 563906420 563906449
    0x40c110a020402031807060f080f0601200109060609020315100203090114090d0501050a1503020607080d02040e0411011404030f023a05060610080403030c05090a0b13090b 75
    0x40d800704c0003c82c084100c65240442214800c261001147ca8030000341410001801e49070000e03423094009120448001d6105005900507115201e40000204000710012000410398100355203c041d2500018100e02030b0744041c0c440c0d0800580c1341d1805915450380e507501d86070164414070182d299080d0f225004021121a040c0030310f080d40030b9102d4600741901900c9507100c400d8215410345e0201e4103002040d030040303005420110003400544103044686c1d050081501010398002010411031b00040e00d0707600104280458800090300f010313510724400610200480e0240d400c0d08804040d441d656034480071101e00b0001c680021810282552101e8040300b54140c0001d010303c00201c8204900c0032000c20301012074000508100034000d20640c81200c40c03100340070072626803207240d0108001746081c030f40d2044201000d03941c0301b00990716a00c08030043d0100350344070401d1100400245034641c1314202d0302d001400d2180f4010360f442d0700601e80303d950f11b5103d61101d41480d203030440b200d03050380d51102e41c40c0058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 563908920 1250 563907670 563907679
    0x240306060f030e0a0b01090f050a0e031804090605180f060112031d090703091b0b072303071a090c0307060e040b060d06030b0a0b01020c101707020705040c110a02 71
    0x114410f00452404455000241c03420a00400000382c14103181c0011303603802e010000600c07050302d514031844180e0342c0c18401058142c0007840041d00880b6040d0103800d071001d00500104001c03800343c549604464050310101c4046080180c0c510052508100703140c280d900c91001042158500700390102042c03031464009040051580807145039140c1d10301032400c0000004c040e03109074149a0009001007900080855900301c41100280011030a241c405c0c5c106d807000c0f0080c501c1c4c402d0381e54a090341000e0070351040030351160645c04055521820006030000d01e1103580c1c25203601c0345c40d8101b203407030940081c40c0318250b5000c101c0c1c480ca50f49000c42c082c8200d44450521345040c21803400020007611048851680000000c12440310640058000c40300301c1713000300c444110300c0d12255207030030aa5036a20f032580d002d40c4c4001a024054105071101d91000c0c239007490300842c4011410360000c0c1811095034078100503441b020b414409488c051140311034902e21810580e2845e4012040c17a074030f402e06404040d108 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 563910170 1250 563908920 563908931
    0x804020d0501090605070203130509010806012601110a270b1e030411100c172505010608010e0f07091109031c030609050408030a0504060213240306060f03 68
    0x3004825040f4440d0103034450390034051460300c01c900075aa5000740d800d0b5844e0916060001500b07046c29207056059076030820203880b15a003850031107110200750501000c03d103031800d8a0038440100a12a030410702c5030503281d80740d0b2000d480b08018550351a1001100c0707000224181c4120041c80d440300003041f104035808071070716004400d021f0804699072031600011910000100030400280343c0541c595104111109003070b81522020441c0c0d04080e1090081c5940d12441040700b840c1c6000c0050401c0c8842c45101d14480071100314014200c1c96840001c84840e07459031390038412103c081c0038404965507148001d100817510403041b145d440c41035108015019a540440240e070001c5082150480300b000750458241c0c0300d240c60350b00c0310101e075000c001c03000910b032410218800140d4003980d03006580003000d480c1981c8034580c2c003600034000548112100c590800c260310b1138034889106180144140412606206409501e009081d810380310301004252400700305019042d00002c08804540c000d1400041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 563911420 1250 563910170 563910173
    0xf06090405251e0206090607050906090a06030911060918060406050a08061f0b19200706081605030f040503041a04050f03150631090201021501060804020d 68
    0x1c8200d003405540d00c078000030090702d030041d00092042c1d458003042c200c1da10301c440c4494040b03813202c90685524646821082c0460709841c030403009020021001800fa9140c10b05003400520340743c10507801000442e885d01542810704c09020b90188481c1e030181c441a20702550b480004803034008611484d9100c89000c8003240d2140c0355940f02101912000d80412016600c0340400e540d500001c07034000003048280c03103040060241c24544001110070030f2440f24280003d114081d188108500201c0c02000140d89800c16962509022520038100040243c1100c60828030001c11030040203000700d003210240c88980b8041c56000313044907848000d11002c55032680780da1800c0c80c01d510440d8025020208400c10982e03020354241c00074411198103e80c40c0d000c0d4802d4509064403a096241c50b0540c58003180c000030001d060407403004040051441d40b02030f0f0009103550400e0b0224107408000d4440750745259403021541c041013608502d10800000081561400c0401080d07140002c0001740a031100700704040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 563912670 1250 563911420 563911441
    0x3010e041b0303230c24010602070302090103021018060f1404030b060405101203020c0405010815041202010e0f0d0306051c08070f0b36060a1104081b01030b0f06090405 74
    0x6114074419800e032592030418a10707513903621001d9031b8048402070038136000064240c000901c550859074041c00d001c40b9a0318580030451405401c040341001d01541c244a900098075485404010f03001940340c61005a95520b0020650b00143c04001a0880100010b00c041500e0440700fa600c980110f40202c0c2d5540d1301d01031030301c071804181e10403051001124006410540c000c1955054441c0c1980d041049a80ea444001d40da00780000000c5002c622546c04980491210741c00781240b200c00d4000030500c003a4511400345481c3d8031640c0c98445800900070100f00580c180613410040c14110f032034000e0800901c3c1c80c29000c0c9802c400007807a480300040d08500700304000e4548001c5a070000110780c1545044a140400c20010090020401004206280c5030060002d2040d59100c6820010321040d82e8021420303004150b150030280c0c41003810711001071303a0700382045030f62035003000e4042010b000710b80040054103583c442070b402c52260304034964442075a1112400e88074442e030101c0e008076564494076000e4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 563913920 1250 563912670 563912677
    0x40e100e0a021c0f0e0304060e0306070f120509070f0303120b040504020312070f080f03070801080d090501180509091e15040b04030e090108030403170405010816050d0203010e041b030323 82
    0x1700c1d05000200d00003c0440d0884101c00c071000040c0c043d80c0e420381e1840011100000010302072008504d02c0c2e4625042580c042e03000c2075003c0c00365001c68601c0341d04c51358061481c40301a801100003070b0b1010a4800c04420381d0081c0043c0700d0094600b8040303400c156002035220400244008030304100404e50b10140302c401d8100240035600108032580c2c0300d040c2c80250348141d00c01c6071020085490f180000822000c00200e04800100740c3d83d40180c1541800011036407030780041d40001c0404e45211000c602c5a51310700605002c0c004920080c090700900200103501504c3e110003000c91a04603608905a19176104c4107a0b07400781d40302c80c8070b0000c4e81d55441d05403106400b201800b500300325403d0002c1136035880040100f06580c05039201c51000e0340d00c6004034500b40b08600540d0b00107545070021500c1030f08006010310020703189061079070034112600d0034103040341c1099002c00108400b01081c0000e100303c00d07a550f412a0305540d008078149095440280400c0710300440e000344c18427102054400f121070007003036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 563915170 1250 563913920 563913941
    0x5060a1403011412070501120c02010b0415081b031002030a020d0603060609201801050f13060906110c060c0705030a08030615031005090c040e100e0a021c0f 69
    0x8140c8950b1107040056110303c03e40010760052424554a00182000161100c100c4a0580d1624070300b01400d800340000c0c102c0ca0311503600750742d03c6400d41c400f25501c234001e000c1011001c81d20f090720706140104103031030884c0d0090740758128840078466003081c1d20b0100b103022043d083d1640140c2e881d10740031035000003440b0f4004001c0b074251030801d0200420000da0880c2044851a000c28800341000300045051003100c0b02d01c11640722010000348140d22030b10b0610000960b01410003608144180030500803035071040302441d030324110003242808140d810140c158040c1840d4600000c1c4c540c02e10a0099540300354603003451148001080c415038400082140310003800d0060141e510b00c5283d4680000150400d4860903c00e4181c07040074641c0d0b040d05410b40c2e05c211203a80068030282d12f03190a202018001500e40c0101101c1040045040c444113404079010b0fa0100c0312203103403e4074000d00d01c0400d40f00680740c0c1103d98010082c5220450f2914404a92111191400174000310492a004002c1c0040c148 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 563916420 1250 563915170 563915207
    0xb0c18030316110406060e0d0507121115030411240d15050f0a030b040c0e040503070203062d0a06150207030c060801051c020a030c1404060e0403050405060a 69
    0x46095804403079189200b1072602c154400e1420304079800c10003058401c1c9020f0700c3d001800328a41d115803441c00e03071029083c00e4043c1c010703940030315110b884040310069254010399040c0102a00590207080c10381c50052440c0440c40000d0960515a9840c2446401c101035203200f034582c148489004186240c015006d042201151582ca00c15074456101a02c0103200340600448908800a994141008041d01f613680041000d501c80d401d681c0c0b004200d980203401a900090094008540c0d12541640980214052001503403030344400d10403d86840d00050011440e460f101c3d040d000403031111040c6014103011083c002101d6030b1031811030801443c8942c05070000d440d901c0b002462554020580b031060b02d01500b0801074050703c5100c151840710080c4103203a080b0303283c42e007032080c04441424240b10030381c802042e00104075520780f218141c070507081d04480c41c18580c1c06840007113484c181c03207400000e008a0003e01c42514090710040c24034000c0380320701c501620001400301c400e2446000c0c103007600c103005072 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 563917670 1250 563916420 563916427
    0x3090e0603100f0e010e0304120b0c0f072f030d11190b01030215270d06050108070513060302030703080a1b0b06090a1a0f0109031703060a050a030b0c180303 69
    0x3c0030b007006424401818800e9519141c48045507080101c1200e066a0b4030785006020310000d43e58030804a0801440328503020070074095114884800c0d4020840c80d0700130044400d0440300204009a034075107a200440014001080f4045a0344006c079040411413404d0070821840080c3e2010740e0304080e0001d85401c203160703528082c4010014418401030599000351450003d0b01041222045075204007008000b040d00314140030046098000d0180f4084174001d054007011102a41c3d554050300c1c001e802000003900028428030081c02c0024a02d0703080308404005210140c5160081303500e4039001d02000d00b1402c00007900313099082c003c00340d440081083c0164070082681700d0400b08a180e03000e0310302a00c174040780d0012889040050142e2010072200d2200c044540d441d5200300900e00321503a0360345041c03240120703001001c640901000f4031142c503074802c1d00783d40345458000c025140f070441c1c224511070144d18030300b80045820700750740d00d51200359021050340d91000140b1000b80360210061450740f612002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 563918920 1250 563917670 563917691
    0x110102070f0f11010507110405061206250906210e0307060b03010b0126190e030c160605070b04050a170705010e06010b0d09150c020708150403090e060310 68
    0x4080040c01405100d008240e1107443c0011075491046400c042e103e54030f0090348070040e1400e90b00c003a8005000a140d158003040740c405c2c0758100442101c01207041102001c00042c00c2d18003501d4251241c442d440c02820769400c00ca0050070310f01d081c0c640783d00d400e40940e0009103004c2d0164480c2030703e11240b0f822203880790003610303106014100350504240a03508003103540c900ba5000f01300b00a002c800802000103200c10700310802c0c22441c0001c00c045d248040001c4400843c1c0150311948007140b014130051540d0b001c0842103246004481c1d59151007850305007004000032640b03c4252910540d1001d100403040c0c485044ca41e10301816a24082c1480840851014651182700d00400040d4410b00081c4000716000ca66580c03205e109206001503600c0c1003085c540c030b40340399a001031446403244440340f6003135900340700e001c08032402c0c52901400f42e03102d860107201444041100070640e000c6400310710040c0c0307040d41c0d00405001607032107aa03e0045d2801c02250702a80d0074050b032169005041400c10900850313 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 563920170 1250 563918920 563918933
    0x603010503030d1e0204030c06021002090a15122c0d0807050d060b0f070b0609010e0114030a0b0705040f14010c060b01231c0e190203070f060302040f0b0316110102070f 74
    0x81e03200c0c0201500c54540d20bc1c1c9540e410340281d0300000001000c6a03c00740ca1700b0884441c900e890134044c020015020712030001d450700c80c85040c180e2249140141624000c4880c0c92102c00228405039096521041400ca4015400240d04e0f07440062032400702c0e00c80d01100d0320f503805094543c100c0c0c40d840001081c3d600700364014000ac2c25205004202c10016505d842080c400045428054003209854400040c000c0c0314400d01080c0c0800b03000740888a04c581c0c65241e500b4102015202080041c1c40003e042240c0781d8000f071810040c20b0f0103504203880e9105800040c1c21000740100080901e511484982416800791a0030303001414000c2c0c0182c0004403e0382164455070080c0241c1140d0140d0010030400941c080c460408141180c000070101246400240140340324102800c9070305214840002c14180d4940011400038401da45000d40c4460a0014507a50150341340c0003186100b00910401410102a40309044840c11b581030101501c5c410742a0380740a8824050042c001d00200441001007110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 563921420 1250 563920170 563920193
    0x21050c0a06020a030b0d0201120209190311030606190501120609150320010e060d02070c0b07060506040902010e01030510050d29071d03100908180603010503030d1e020403 75
    0xa44e010040340c0603107410001d00c0740f1403000190004014408010641f4182c1d4000c0130b10748c03801050000420b800c81044090007199400403501e000308030501e108542410400c3e10740003802103070501d81c2500c20b221401040d032031900c01c0c2410000603910001441e1080d6001c40050040c01509000d40c025461001141064030f210484c1c2c0344240c2545800c068840c2d00710211880e030160740350007115046c00308102913504091986100b1580c00c00032200000e102d0400640141800c078102621104070b400c040d001c42e44020401c41c0a941441074180050782e028919403065282424001590b032108100d03110f0001543c5c102d40d8006c480100040306110044440302c0c044001080c4055001214041400009005450500100b129024401000000101480b03160700b005400c445510000c00d05441c2aa10a80002c1d82c180800140c01400d410074183d01540504040e510540307154540000b19a49100d43c40c61400441d50714081b40c040e06680c80c1d138415000d4030076542036444640700d0510340c1c1500d9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 563922670 1250 563921420 563921437
    0x110409060e070f0f0b03061507050a0c08010b0f06030a061509030c092c030c010207140105070e0f061b030403240c120b1306030c06030c0201050421050c0a0602 70
    0x2140c694002803120f64602440c090303a00c10a0030510341441e0040b010901e42000e8641c6d94040e280c0070845164a07051006010898003680003001c1c0c6c45c5281c14403105404054000288503418100c940015894020304040401d906842469483d501c0c000400010600e9401281c038500d44500d81c0791040368440c891400f500d000b0310003000016910549541240c0324210181075070041109202d41d40c00c2c0e4058000c00441c1824140c03440c2c90428850542241c0c0400000c41d1160004441c0b1030046800b4822203501c40003a0506079070624a440006814082400b4050702ca444e001030740d508417030000803d003c03402e030b000004c9a40340c035228509085000d0008405074025241b010085040f441e50b4042c0c1d402146440e00d420004400d105403107005001069501034006221141d03902d8244444d00c40c04009500400d08070b020a400c00c403005054a81d41901101103a043c0400d0001003541c85038103503072211340c244c203145049800a100b0b8500e40260304000303296000d0124a2024040079400801e40e86 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 563923920 1250 563922670 563922673
    0x8070c021801140f0306010806010b031f060201061703070b06041a04060b0901110a12120b1e0906040213050607020a080303090a060621031107050d05010609050604020c0604060504110409060e 84
    0x260392130000d041e40c8140c01d200c0c0a1031a0301c00c4004114907020380300110340005680400c0815401c040030344804400c401e600c42c00060795102e03800c0208519039610808101204405145041c009843c0c003000c202028004601c110790300c7c1c414a01c941c414003440b1a44240c0a001030001996505503a02150004207500d8045080c101c2c0002d5031484c089010f461580c1d10941d54410308101070701c2111380c0c81340d5401c2414055603c5a000c0003d5855024903036031481c0b0081580402c0030740c413007403051519014051600980c0140710035903900030084185400c0d0b81c0151a482e494100c40d000040d1442c2055000c1c091500002040c0900510007045010701c03140591018440c0c6a580c003007104603542401c5601c8045024026410000b032b210304a110343c3e203008001222400c946910015a44148a841c2100d40360356031902007085040d2130081540c840360803241142030015007280b05442d080f004100400650340c5e040007404001e10780d210080c00c0540a8410480c210240c41d0000041ca4082130300802ca = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 563925170 1250 563923920 563923939
    0x130501050406080105040b01060c08160f0510150308070602041d1012081902010e0d0203070b0105030607050702102c0f0d020609011107090c020c100e0108070c02180114 74
    0x31500500171503000c3ca5121400303002607841d00808903240203000e54125907030441000701082d15180380d06031880b40c50041c2240001c1c00f0161818518014140400c40f44140c10000f03070f864600092024401125007042d191a0782c0c040c0b51a107003009200d1a0040d00b50100c180003103200d0351074040001072003425246012403240352200c0312a40201c40d540ca0052007100c0410411940c101040c0031118010114000030a00609400c4414180202c050002d001030303201141007024000926601401080241e001c0c00715402c1482d8020114031a281c0c02078061480905a1484c0a10400060200256010080c2e28114040c00c01d10182d980707450a080c40780b2980101d82c03a0a1901020443c4841d40c018101791600c9e0042005403145e0703000340d1b0f402c2e4043c02844400145081c036030051400310006640501018100c9508211a13102104407090070401d00450070322142e44c00039544c030780114080c18649020511480000c14a41c03c080b180d0510308111000010350741810302c0200794040c8100c07541074a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 563926420 1250 563925170 563925179
    0x50901020c070618061b0b0a0b01020c190b130f03030c0209280f0b0d12081807090f020405100903050607180b0901020c0904030e030c101d0609130501050406 69
    0x10741101034003402c200304400d00340805c80c0c00e00506450a2049840440202e44851610f4031403003400e044a1141c0b102c0e840319940b5203e907a0510403002815400c9801c1d00a5036080c0c94401d6010040d40218000c55400042c40e001c901441000b51006094a030384090601d51640707401040d001902104034010800000800c1508410403003a41c4c445e80b400b000410303a0948104503001071300403c0030082d48503640e04801ca00c00c2d222941c0c95802c80c0e00485540e8143d80c6483e4008140c0040104505c800c1d03c110b503102c0c0036002001c14003808442d101880800e04111042010000748219130005a1000e0342c100c010240d9a00001280700300c030f00a4044e1881c556a0b0801a07441354940c0700c0c45c2035038445028080c40400303c008050281c043c010301c1150038050400d004a6020001a10241c0102d0009810200303645810841c6168034401a1008001101040d030080c026100300540341c61600d603000940461511040c00340c0c1c0d00000001c1001101c40f000000c1c500042100380961030169081410210707 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 563927670 1250 563926420 563926427
    0x90510031404030e13060b07120c02031009020411070b07140a02150a06030b13060506030307020d020405090c030106091d0a02060a200607081e090601180609050901020c0706 76
    0x80030582114074100340d50720340c0e6040312841003e0811076400303c150100b40c0307080b1069105100c003a207828001039035585900c0c2450006406600c1c2400100101b49134903400607140800c100c074104442c05008030b90300e01144000360140000c4030900c0d0340580089540018400c0ba0810703a40244080c0d100c01000070402901c140300c03440f46130a00c00140c0e00044002540c0c4104000305a4090302c60100026215126510101390840580380546981c441402d8281030003820310131980c116900710019440d084007640400c3c00d80100c1c03400a4410380d03031040050001c1406000305160540010020410b00b0b840703080200040034100d03503030ba403284030050074802490800191009000e07001007aa5042c40040303a0121070712041d1110504c030200c1c076034003201210304081000741e00900403500c442c0c045103081d40714901510302c003940c004948900c3d001440742c10703203010501606484242402004140041c000342010f403a003030b800840107605e4682004503941d0198041c05640500d101900c001a5a601084 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 563928920 1250 563927670 563927681
    0x80a15030b0112030504051e01120c0801090b1807020615010e3d050711011b020103050c070b01033801120618050a06050a0903050904020307030207020d0309051003 72
    0x81c00e0510080041c044461458414005a071003071411610b8141c60b0700124540c0c81d02c1c01503000380c4032014080b00e8038544c5c000e1001a803402120300c04100c415402c1000825a420612450002c0c603501c802400c91a00d6111210100d2a000000150182840400207503150421100b514030030f61420818101584a081c6100c00600000c0c0003d809100c00da05140101d005c10071b030b2040b1814100c03500c050300400004000345140894441c640c0b03885540c00c10f522012400300c003080c1000814440c030000e2240380144007000301c0c0c080c0303000106a50340c0510005030b44520342d005416aa90f81c000003082227125040030030344a0b6000e410000f100310504002140c000c0c0000b80c003114078081c0006004100440300180c00d1540260800b1a5603035811181807000c00c11150140c881350000003143d0b090003104d001e0560030481341c0b8030800410700e00c1d4a00410a000391007443c0c0c03056400201081c20310b440ba4040c0c61166400404104a000140c603000d000e0454501c03030140501040400c90703c03614082d2258 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 563930170 1250 563928920 563928923
    0x80601140d020405071b0b090d1b150f06080309030d0305070f110c210d0e06040e06190e01080f0607091e08030c071412071a070210080a1503 62
    0x40810800c10ba400c00002d090010700020401c55000e003584480590400c2e09403040340208103541307050600c030719041d090400d183c410704248000d02e00e1020401c0c1140d851b81d42c1c000d03000b1444400142c2a40c501c04058448441000503003400c1110200d420300c0c0120080180c1c1e81c0407011a40324504084050f425204211100300100d84804040e0401501952104420444403016202100c050f200000c001400f01945109101501040491010410040082542ea40303003032200030440301c240011107900c218041c0c010341400d080c001c01d1403074455843c0c0000d000c400c10a08401c0b1601d42e12075260302c403000d101d20350051084055000980501081040c042c440a80d6842840ca0030011001024032411400713a14803c8001000600c00e5410300280502104038000340041c28604020b2521440007045081c3c4128662001107001441c0042c2ea2412100c60510114281e510b264900d045800351900280d008050340c48000c407e158003002e00351095602030020002480c4a0181c0020540507000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 563931420 1250 563930170 563930179
    0x5150d0f0501050904140a06020f210906150312040603240f0b09180f190e0312180303100303111b0909030d110a0f0203030702190c08010203070908060114 68
    0x10401094888a803106c15401c400111004910380d90703103c3e0100d0780049071408104e800400d068000c0d10040308494400f03040c02c005072109081c800103450f112600502000c0e9450b000e010300302c00c60307141807005801102d44081425141c9a0701d034070103009001141803180f003101901c02041e07090101504000142c40600e102e070b511301030030108001174030b6000042d03295024030b605100e40c240b20300d00c00c43c1500c10525030f8515002c0d402c0905101c0c0800310801d030041d5181d0300b004a480c546603000019100303002c1c401c0c030141c2e10315280c0e1981c0c0c868080890400041602000040100e039280481078141224802d07900c0c072189103d01408961100c41c0c100029000c141040b0004d94580351040056800c18404001d0760b141141c8c54041c40c0480d11502141040d05501042010706d581c2c0080c000f140c5000c160016500e91303d8001380094980003511444849440c80e440800e003840000d510000240c0344a2000310b60328100030b64040d105105070302c1441094405c0c440086000d01c0d100d00d0a0a99800182 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 563932670 1250 563931420 563931439
    0xf0a060b060421021c060b010210020f09091f0801050f06010f0e011d0a0815070302070f0b040f08040618060e0f01030e01150b0c06090703081b0705150d0f050105 71
    0x3580048851040710180da10014038903010300151a41c1752403050300c0307100d0880001c4000480c4006400c1014174813800001620500c02800703400c2d2014102d03880d000307088851480300d59a4565400016035082400e4080701d600e51030209041c041503200c203014035042d034100d500a035503600c01100c1001ea07282c4240000f07010100f0100036940a010800d004d0310340b400904684540c4440807c050009550042c041a80482c0d201c458400b0031106994025100c1d160652800d041507c0b0300185201400c8000d051881060015050090181d00b0300c00c0c1c103501c205860356655541400403d951a420100e410080c500750300040c00c90700503002c511890b03402800048203003860b07100540050940c0c2001016a540b104c08040d6140b006500c00c03c003809141c001540c0701d07484290060315040c4000c203a684964022641400030400610070b03900801c0307103045481c1440107020900c81c1040120381c00a500300c100342c9002c15510300d0002c00f90503100160700003001442000c1206805954081c45010380105994 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 563933920 1250 563932670 563932709
    0x8030a2d0f0b060d020409050c090306010e0c09041514122d0a0303021c0522030522050111060c040303031d070e0a0e0a1502090406080f0a060b0604 65
    0xe030801c00040318440070001c1c4451008020501c1680000141c80080e50700090902608240c2d128154010754003030710040c202403520010030782d5040e06004040c02d24400c032000524554024003243d4403070030080c0003407050900b84c0010403c001241d000c0c0000680f1030071f0345406542080c0c0c006410044035880204194030090760204000b003401c0300d034000c4c12004201d05200c00ca00c100440c034006442980c006075621048110054031240c0107080c4489281004240410b440c90345440c0140d00c0c401440c13076856003040d881c06483c240302d904040300410840c024480f407410502d942500c122031080e00d82840c1d0640d8101e00c0ca464183c2111022002e1340103020500102e0301c20760014400710391604004010410100708a480e01c0c070241e001040c4044540c0c01c000d4030144038010852540c90b07500082010700318540c1c139810f030950b880e03c5500c036596000c02d500c6142c1c0e80c2d60b0440d40c01001110b081c0d5076214400e01c0c650303458912001d42070f104581002000300035400c01c0f4003100d0841301d051740c0311600385048 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 563935170 1250 563933920 563934011
    0x180d05072102030109081e0a0507020105160605180f01140415060b0c06040507121e06060b07060b0a0807150f020c120f01050114330708030a 62
    0x12103071180ca09541100c00040180c40034071030464480e005100070f540741d080303402102011a540150340d08070410300740040d03a1480c0d0044251101d290342400d0564640381080e40540f0001d460a1000c0c0040d800c100501840002c07011170a4051000e40381506d40c44102032502030b00b66840c156074500e20204e041c0c001402300f10720300c45541182c251070002140113603590344102c030f5036005040c0070301041d0070280521080040400081e001400007400100d81c040e07140d00c806492180a14800d0400c4040600103010482182e00440140ca0604002a20b40583d820800010300c0b48c0d549a0f40114054000450311070300c0001e03480f0881d01c842a41c04c080c03130b94010048540e490444d5004c01584203a0745604031507550403050300c0f034400812009161034840c0000b41429900c0690000c003000b40a248404e00c1600c0e07403c0400214040c02603006102d0908a40800010007024114107401802140d60b100300544007004500455a04406110440c803500301c000012421500c2c4900c1244005d4814040814 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 563936420 1250 563935170 563935199
    0x11203030207050c0301090b010e06013b04020a0c141203011503020903070e041b0803090103090503070c1413180b0a14070203190c17031b0708180d0507 67
    0x468025a00e81e20800d1022034251011f083d011a0700328010310061105a4000644a503c1002481c140c8031460b55400d0402000d0711242c40d40d51a0300391480011101d03c01103000342c3e0b5424015000b15994506646c0040c42140c07070603800c41c0d0814451307000e581c00b0480020038254102c01701e40303004d15591901440e00e01d10710a90341d10304240340d021b2185100ba940c090203840000c0c06100c1c2000c55a181528040c040c1e02039070045c1c2203100344052405c2c069100001b051384d85108081c2000105c1c0161400c21500d14010f4000c010301d25009100081000000405901c807490010303580d18005140c842064029a400c5141d060104e801c1d40c0c5004010810b03101686411110f0110001940c03080c090b4448101c0100302c07546030159100140309400e0300c42a8035564004040380c40c00b210b0090145e601d0030b025003118450124080b0003c00860110907a80c202c108012145807600b540e120207524000080360031640560b403070090b5000785440035051407101c42030000c0d8810301034481c0c542040354a1781d5451 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 563937670 1250 563936420 563936423
    0x1061a090a03051c1e0c12110f030a0306080a0f02130b0405090c0a23100302040b072402040e0f280b030705061c050705070c06030507021203011203030207 68
    0x80c038040000021500c00c0c451004c0c510804400242c240d0150140a0701c0083e0710a83c1c0d41818841c2d8040020056101c400c074010740d42d0002900c0f500350340039401101c4c0311600d00d0310310321640500080c0005490b00000103140d0400c440d1000e008196548a6140c1c407001040c2018004c1b0049988001c0145000c2e02180509403510f80005104140ba101250071154202e9920b40c03254410f03e01e40720715207058a514402008802050340d40382e0800380700501c031107020070591070040d00d641383c00d0340c02503010b07405642c0a01035860001b0384a00c0a41081c0c03820711b02c0442c003480104402d00c40782c07070010424000c440035100e01100420040d107a2100005d5030040050071503a000100045090744200c0e02c54030352030b072400036113000304140051804040c2001d4607544024800d8604202d852090540601582e090554510001405980748030302903510b446000c0d4004e1044054100104006406503c824010101303642150030103052010800b405100070b016a444100002c0c010f00000380c402e80090444a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 563938920 1250 563937670 563937679
    0xd050310030c03030f0818030d1d010e032d030c070203010609060b27010f1b15020a12050910020a0314010e190b06030a09031e080106020d0201061a09 66
    0x996903500c415111400c240c10443c00602c5c61400704014075404103403079400c01c654082e100000d4041030000c40d5648075050320060515211120881d17082244e91300480d1400150000340700d80030b002040c42e80ca07580114141204bc540c584100d0340205441204502504004480c05145448114100c410b03900044c0040340d0540d00c445010504601d140200d0b8024221222280d407688004004208940901704600500ca0080c403280209603901c0b002e507601d42d5000f400c1c502006c0a0303101c94000c40200b0200c01406110f02d09902c500c91a1403507004000000382907032040c0c1c40308a00c0e004141500c00540300b03407030550b211200b101c1c9100816401031004d5081401d00003054802c0755207140f1181000d81c4818074402c1c840b41003000603d480c064603c035808000780c0400c80c0355061b200040241c08090300900b0566964654001018010043d11001d18000c1c1d40d0011070345507911000303181c481c0074040c10b0010300403007540300794003401400b8000030f07205200c021a032040c1048040800c9a0020150300358030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 563940170 1250 563938920 563938951
    0x907030b04080c100b010f0203090a090b130c020c0103050610020606010807020c1f08100f181e09063803070513090b0c03161101020f12060a090903020d0503 69
    0x150820445001800c1e0110380c0400ca1041403c0050301c2034002d9417447e42950010406e1401542d151150034041e911101400261070540e5008038291500303501c4212101d61809109862a030340001d04407003120002d07a014001c41d07580c0c60500c41a03801c00902400560322040c04a0034560080d0409030340030500d48101c4880c1c00c50840090301201405609004464052540c0c02c0b171903600600c80340d80b010712440581205460003202c14182002c901c80c003900a204a9441c1d20500b450b9002143e110041c2000c0c0100e203402c05140720020004490f086441a01c0c5c41e6500308013544621810400b120318120240c00c9026200d00205180320909190354540100c4802044941e01c0c003155501d4a0301c0c86a001501c0000ea00e8440400340d0040d0800001c18414001c006500740c92403030700b000e450f00c00c3c901011a002c95500d46400b90180041000d501400410310401c032081c3c44080da441440111000400b19a61342103120840f00a60700190040c1c00c40c0d55210700d05400340001f96004010100e02d24107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 563941420 1250 563940170 563940187
    0x10021e0c1005041b291606020906161a07031a270705030103060f0506060403140a02060c0c040b06120105011407020d030e030f070b04231e010809060907030b0408 71
    0x208200030f4000c150410060950178661900800c2c41054400000f81c0042c681000b82d07280c00340707194582800508040d0001003031403481c3c03946c50948116080c8031f1213880036800a4038020000009821440141548050020385074a1080c01903c440608100c9007080c174155003030030b10122007500e02005104403190390703607491110b807030304002441200701c0d6442940380c2d4110f2521100395141d501c010002e441c2008184030301c1d56106011a01100c1e0312155400462501140c51401e00d109503c000e9800440810345d50406a00030995003810702c002c80703003040f00d5041ea0007082001e000d060818408a01000c00510055020303082000c541c900f4085010b080c00c0d415400142c0030501803104600161500f5208012420100300f0710b4211003080c0c020380307105400e000302c01c1880d01940c45480498426030803481d001c000094003845100034003034150703500c4070040c03000c0011030404540d0050005105400203072403450041142d03805a90740001405003d4910b071034000107481c2c054000d80303168408000300341 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 563942670 1250 563941420 563941463
    0x6090d0606210507060c080904050910050a1a18010b0912060c070b0717071803170a0212070c051012090302011a04091110030b0310021e0c100504 64
    0x3180b2120100203200314940b407810ba801c1c119503500207400d108462401c1000100703200b0541d4462203082d0341c001420358401002500d810f4440c9804814103240000b1300451003940d42045650791f0b92404001428101b50301440383ca5506150740c07200003c07415006000405021009140c1142c00420030030200100c80110b41c00c21106503000c1c0024040001d0442c100503521104c6640030700d80d420240c080a8040880b00103c4030028031070400c00c02c10740d01c041d00c6154025810f201440e00803c20156116010040c12601d5200b1413850000d03100c0c4c000194900d103174580445884030391121104d80726524010a0154140d81d00711100c0521041c2217080740d0184131885014001e90080d4004500c0e2204106940d0140600c0c0002031300941c00c2c0302000c03003c29804c21030707903001c443c040d00e1220040000040480c024203800c1071090b4980140c0114280c03050321500a02401180c101e200c54a048141280d520a0301c0740b29038541b004d07002001e241c0341c44d0b203072980706651160003250644800e200418420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 563943920 1250 563942670 563942699
    0x70503030708040b010501030908032a0703050409060b03160e0a090203090a062a0e1309080a080105030d14160c0807081905070519180b031b06090d0606 67
    0xc00011040c2e0104400c0c401c1d144c1849004200030b0800300001550790b140c0700d1240c030009144520304403641c03071140c1008020040d8014402c2c44032440f6516031410f45001066a401841100e0a071801d1000105000078240201ea005441000420095200c07000c82038030364071a43d0820310745c0b00c04054000143d2800d140011403054810002510154815207001d40864001b040c84104400d5603035400038540d071102c00c0d084d14035216820712250075280b403000500606044101d00072403905200b40c01302000700780c101904e05200c09884480f0700e40c0e00c907018180d840c5511210000000c0301150440340300816100100004020104008211a050b4482c581d1680b280d40c8481510713440300c2c00820143c801400b9510041c840c0c001d0f005611030b110b031a03c1e0381e5000c4500850344908420300c82c1c210401c040c500100c000301102055404001c0c4d003030302e00c00028407040001c40c0c001e00a0016041c1d2003543c0b00310900c08110020141d9050459800c00c1c048640f60340007040b01c0c01c0384d0b90034001c0b42c40300708003801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 563945170 1250 563943920 563943931
    0xc010929040609030618110409060207020303070c24050d020306030a0c030b24130c020a121e03151502010b061303141519270512040b07061107050303 66
    0x1400700c0240355142a030226402410034400310031100c6c452800240700c0403100c00100d00c2c12079010070100b0300303070414800074415201e000f541488002054010400e843c501a41181c003050611100000800208040108200e01103c0002c90820446220b00c840d603000d140c00c000040c0444042c25010795034601910219001550b20042d250708120f045540440804420307120812450303000681c802c08280021410800440c2d1140c84034801d0306100e108120384400560004c450070072558140d54007410580c042e8400c041c401c41400ac642034420b020f401843c0041c0e1000c1c2480340c40740e18008290541c84845020101107540312510905641e480901400e600960240310580c010700e549401a8080c40050900121342c1050341e0000700e00b0704040112382d00c40007941129002a00c44041e06009148441c0042000542c0d192960450300c201080700b2903840c460011038525459104c020003540c0128420015452800c0100c0360005d1032030b4000b01d0344200480c0096003400c0440e52520300310f8104a46 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 563946420 1250 563945170 563945177
    0x304030c02030f101508030d050603190605060103110702060306010311041a0301080d02150c07030903020d080c1b030c060c0102040f271404032105160305090c0109290406 75
    0x803503802082e020b00c5481c2031003403001d42d43c680451800e240980c0b01c2c0181c011045623580e90701c000512944041c0108a6210cc5c803065180303807184249002002804140d0704980080d151616100c3c0318070949080310348070b640040a407411b5680b041c004402030181191215140d40050000080c0300c2c01d504030030062040244c030b50350b85030760404141c60302c0e0540b4800300c0401c5500c040e100c0340207040565102500402c40c25006a41c48055003030650b0090080d6000a400c4441030403032105001054001d0f00189141c0d03001e40300f42c02000c0b2420b081c84bc00d1050301d039034143c00c00c40300c03841c161500d040140f0b0300e10401c900140c101640d0b60340d5120b0900855100140c1840700d5070000c0e105c44a60300001d096200c032900f08200828048403540d0801c000203000070280b0005240152030806050041045410900d03401d01092034800d80800404100101cbd5001090415000c0b500c0c5030808a048540300c038060355654110781c503141c81164030269070540d20103140d0b01c00ea00600c807208000010301c054001601c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 563947670 1250 563946420 563946433
    0x6050907050901020c062b0b0307060906020615060a051c05040c080d02030a0e060c030d0c051b060613110d06121a070c020f03070513061a041a0304030c02030f 70
    0x8006401d0441708140d1601c10308082140440800300140d03001341d440954495140003400c03040550300244203400185605120b9030034000b03035282d8087c0c0c10350191075465090300c00f2074440d148a0580d074a55601d110760b0049050194400a80c400c401034440d02d5000f58800c50300380c007011880011500c0c1a1001d031400102100d003032000170020441103020010501c015031406400e10001442450000c0d9424441c880001d9150b104200400c1512107a000c040303010016124010000f816690110f00042c490b019441000040860040781440c07007040c0c09006181c20714588030000c001408061094511200f0038001005c0490491041c03002425008250707149007a294107100d5609152401c1406c0300342d80c1d800400011561040c44081d106505640309031100d0701403c0004d0902d081d94006079040b809a82400042c88615004402100d250408400002410301c00c80951803185004180025030800f105031044002c1c4002181d1203030080c9419a80002140d002901705a899540c035489540f004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 563948920 1250 563947670 563947687
    0x140102070602060411152106010219030203040b03041e0f0302011104050f090702031b011b0203030f01230a0b0a0306090605010c020d06020c0619050106020304030f02090a0605090705 80
    0x41042034040d101c0d90005002a181c04c0c0d0300c85d261010540040c0f4042c0a070b40245501503040d00068516809000f000c0503600c1440360400c0c0e00d15442201c0f05030051240c040c09004100903044040513098165000e540741900b01200b840f510390010b0004c0380e80002c502c14201036001e86101500000344542c8405143c90400e080090035120b8250106020b4001080200080e540d09820540b8450040e00d903844180d50b914400d0703083d07008034100c544004403401071402c0c0c1002e066000c3d11b5003114480394032040c0c1c48240022a40e9010460302d040305282840014800c09000c000c214501c1055003031050518100d03680840d0845c5040c1e8024941d94801256040c1515054000d10000d0a21000200141c1d0702d0140001d02551a42d41e0203400348600001da003060024a03011681071203480d40c1120700c1c0d030805541101c2d80d90355a03084040b01629200c00800d8140c0b0100403102120303001403001e02d003e90b56808000380d00e0005001c0c24503d0b69075440000d1a034441660f00c134810146c50b155140c40d01d40c80c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 563950170 1250 563948920 563948923
    0x80a020a060b091e04021807090305150106090e090a1b210209060f01120c0503101a0d0c1205010603060f05060403021e280f170a0b0a0b040501140102 66
    0x5001c0c41d80d220311000c000304130004109142c001c0020041150345001500d450020690f490007060108144909200400c460703142c100480104a910502c201c0b04565401c9000140d000c400380074000010314565010031084e10488501500048a041552144c0b00c590f5104000c0300540700f100b444100f8640410403002003c462180301c10450b11104000300d462543c0004c4075807500a0106102e40d1004d143c095540c1d20400418548001c049010440b5101344100540640c000316001c42043c015544042143c0000d608000100b4480202c814105044404240f02034600c407220f8408100c0940c1c2403010f064454006c45008140648000900b941411212543c00a081d040a40170308401c000c2000107844400401b100c0900382d1058599480c20758000461101d00648105590089004000b00b43e94030111110b04595544102c02a517a80e12400c5110b201560b120386030a84c1c1014444c079012410201e100307a4081740d824000210404c0360000a41110300a0304800016034210888003030760b580 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 563951420 1250 563950170 563950181
    0x7090e06010c051203130c030c03020306060a06020a0305070206070b0708060f0103020a020714060903060708090606010f0f12061a040f060e0d0f0f0204021c14010f0306020c0a080a020a06 82
    0xd00786854080c80007036807125a615080e20b1103001c02c01400000151008101140c00c08146900c0310b05440c0c07860740d80c10140e0780020640400c3c0d01c68041d40001c2160b0380b41040304002100c841d50080e0100d241181c40a85460300f00d01000d982114042124000050152400301e00c6401d158860b00c1c0107080c51400e00412070b0308000600d051520420031074071001d4002900b10200c13100c86211640c0c1c0c644400208405010341c085d6250948600800c1c025441d030812401441202400c040340c445545410046030013a058000420101d54180c92a412451081e40c40402d02200c000001c41d0041e503550700c071110351010134001d500280b404102401640c18840d030b072000500349440d2118060740442c000988000e00048010103000441040000f004140240c0440c0350303070020021074a604400010078402001d101300341c40c00034036100c03103803510043d50310505068642007800802001e0441c1d0302e52001754020f404445446c441d40c0090000912703000300504100032154040c1031580c1d800d141c81c2080d80d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 563952670 1250 563951420 563951431
    0xa05090f07260705040501080d11060103030503010e250c0516080607201b1009140d1b12031e02192405070f02030c030706150e07090e 59
    0x81040308104928852040350b084041464400c410002103280030140c90400c3c00d034480f5410600b024000503000c400420084041c0c207140d19101c404c40d001900a580360802400020003048050006001004207c00d41590041051501510814071107800060301030b00070030010009800e881c0c681081110074084507a12080050900000780d00384081e094584034010b140c4003c03c08182d0940c10803100000460742c1040107141922040e000c200c0034454071840c801c1c92103010703041d241801a8003034458140071080303981c00340300402110441030412001e040343c0601526241c0741104000d0001c0f00e82c03022000185040b100c1c20000525a04e400f600d00310501c0d2201e4151100c80c82c07007005c00c0d500031450702d888000d808084410008140f9115140ca24180c1f04070707100d040e0100e15034400c1c40c100d03030105000d000285c0720102c2841c0209012aaa481008500342c001d030010f02000d80003451035000f0100d141c090fa6031007144bc5032101d400300b0035003504546504c002a070307405040194850082c039103078010f07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 563953920 1250 563952670 563952673
    0xd2610090e062523031006050304050705061803060a0203070314010b1e0409020703020705090603010c090302040b0604080d030b0f0f0102030304170405100c0204050a02120c091302030a05090f 84
    0x2c3c900b9035844041c44203070999850211075401100c1007114400e4220052490384059103698108541c0361842c41c030703001241c880c060414a02c601140e1280640152403049901000602c4102d042106001d0fa5422503490b0200e0034070981203141050750103002282c41608002e800503121700c2c01180007130940b14002c00d0341c811403115400510401a00c6d1084440e10510414a1000034603064101702c0c49108680c84080740300e2001c103803d0308140e4041400e00454000310ba40300700e103480b01e80806007240c0d211762822021178941d020400060915412007046050700605241c10181c2c0d4031069411f01c0903281900e00081d80c0c43c2c40380520f034038144c1c052098650050305ca0350b03690201140040e540344000341c0041c0c03400074048140e6807600c144000319800b400d4043c10341c0030b0110391140301804405000c0022807080f030900700010b22820075071003035440030304403100c03100c4a503201c0c1850040194448038841c1c0e00000300250360034880c5400e00046002e102d69501c00150b9241201c2c0c1c8a040c00b00341c1d682050319 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 563955170 1250 563953920 563953933
    0xa0b0307050a09270b0403080403050910020a0611030108030405040e010912120516050f09150c16080307050307081c06030b0103060b03011104061d1206060907050c0d2610090e 77
    0x10030175000600d580a61306080c02415926541000d891078000c00100a910a9a404084850681c00301d80341d0100780c86000700384444584000303c0740813070009008040d05507006210411280c9083d81000020001d080b00004d01d040b00ca49031070540d0040005007401180100d80e00540c400340754401d4541c030910407525210030746580303074004225111b1402c0010a00c4000718016045503251079444080080854851b036581c1c001400391500c07641483d02a6507440543c0d0000039540901004030707816582d11401840c03501c0415519040650885000000841c86031280e6a8001e05030b4440c51002d14051090044c26625501d412020382d14458500b42c013036414008440401c45060013514244c842034180201880c02d20103844451049403d0110f90220000350f030700c142020041039080c021402500c1d0003200b1b680d215800d03922842115211030490744000c0340b00001c644a10461090b00600b1094070f400841c145404414048082c0c55501107804504001c0009005500c1811071070701959014001c07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 563956420 1250 563955170 563955173
    0x10f050603071e0504021803070608270d230703032a092603030f01051804080f0a09080d0801060909060503100c022a010801050a030b0a0b0307050a0927 67
    0x228103c203106403070050390041403141140e8030240d561440c9500103003c9420383d070380c0c2cac020052100d40292822030401c0d60203514032141c2480001103031440f020f4003005041d11040b200301203c0030030046403d0252507420041000c42d000c0381d2170080802d00d00a50b8080f6000d8015182c800d10403946d0175500310154602c0c14030641140d08800c0307400c121200d03043c000c10740d04007100ca1540d01d00b050640305c00b102d00002080100e11034904180f0f905a86040d2042c940c42c05c3d101d0900024184252005850b05001340001400c000b404401810b02c21f1007403920304001070b92052821700d0701c1421030300c0c1004119400c0050001544c0068500c0080c0b04810007800700c81c0ca09808a030710380d215414408252a19405c04175040380c000c01403000d405000030b8030513001c085141540780d0b4846c00c910a450014500e5000080c0c280f401d681c014050340d030414002200c58540c18201402450220071841d05070040500018555403510400740c01002c00c400041004094021940440044040083d104e060383d0740c44c000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 563957670 1250 563956420 563956469
    0x111150a060608060108070c06020d0c050c010506030c061902120d020c0c0a06050d0e24011a0909010e040f0204020d06180e0d120e0a0c051c03141308010f05060307 72
    0x741c2084450074002c01448180c00e02002a0bc1080500452035060081c0088010b80c003800820b42c0a0b1154020403064840100301342e251922001002d900040c10300071121844117528a04200c1d500d240100c03003800610182d0041250814022640000d03804640803800800a1003030a20981088400d007943c103081c200e02900034011084080c0c6e8140d9108064400070008200c0c035450001440340d1100c941c1c8040c0008000f102342402050468650702045d0070140d007000050b00d0b51800c2c0205102c481d6801c0504c0101c00c04001082030f40c0e09002084400b001d80c40300c4c8024004d07261003104c0400c1140c00e04400fa52400020030f010480d1034545400303030420070340100c0c4503084200c05190081884007481d2212018040c1000060a54007402142d00c080090b280041c0d02100c03015502d03654046a140c0c0c4518265011043c00340210745030380d5043d0f030214410310082c03c112400303581c0481032680301c1c2031190859081c1140c00807036170351713a40602280c0c0c40d01700200801440c0310080c40b42d401e07482c4084071307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 563958920 1250 563957670 563957687
    0x13050405030a050c01060e01080106060f0201180204091e0602130812030103060e07151d0402130e060d0b10031e050712031e091a0c07140111150a0606080601 69
    0x1a400c0150220342401301c001c00b034000c10000d045009420081c0d50f16129458000c218901c50f0001060701208404103060040c042c0002c5004003035143c0709016000d40030312000c0c041d0490200e170305950024130001c54020410382c003070410b070052000603120452041c6200340d00e241d6801840e003030f602070311402c0940b802103c00c603810f603076024201042046003c40c2d0a0715284494200070f8051194400c0b085031941c1c0000c0c0101c03540301142040f643c0c00001e0341072008a102e100000344074410198400c0c040c09951199040e008007024040d4203d1a143c3d44070041c0004003547c2c1501c4050b04440200b090080c03440c00c0100400100905014040c019500c1a585165500c900071088805c010701106160151290011422800b5491100d901a02c1c02c0100050950f0203160260007820f0303083e0b8404803204e025514107601d01c50040407154105001030008106d82c0c04031904000c541c104618400c001407100c0008014150680d102d01d05000b052041039500c141c10401c1002114420040b0f6680d008000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 563960170 1250 563958920 563958937
    0x181219021e031e0c210601060807050912102a020111030f1005060304030e041508070b030406090203030c0607020f060403270324060e01080c0114040e01030f021305040503 75
    0x41400e2403140c1e6034003c1c18402042c14095109605c9144107003403d40104681c000da640801c180c034040d0b13803108815140070009503500c500080041c0101800e90902b1018a0010b080503000c40320400c40080415081e44c801001e031605a030f142c0d50b880302d5104134040c89a91030f8011400207101605680f4442a01804004c16040e044140c00d008a541c1e45c0003102508040e08001e03040030750301d00c0c003401c0c0902440702a05040d4091340c68500c421140c610b042280d4010b40c0c49010151014514040c04000e8a070409002a107000b5564851080140d80400042020890b04800f40c2203d1070040300107170403c644031580c11100d410034030812001960010044407881243d40c03d280e00c91590307100c00d8240320781c9904000c00d03000c011040b900d01b00210380600346510b0745500061150b16128070710390006210078071441c0314591000c0800c00c00b540c000c003c1c800001004d610f400d41132940c0c0d030758004820300c0c0a82c02500c0190020442105500304110180302c801f5000809105909141c0e44442e0380384500c000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 563961420 1250 563960170 563960203
    0x1030f0b100801181a06090a0228080f0109090b0105280326120708040311060f07110c09060f0301020d050c030f100b181219021e03 58
    0x914040007681c03220050301500d80200255000d403410a500700501520560f8140c030b800c040b9061510b0301c04446031280e1800392000c0c24948869440310042d4001c80403154041c114420b44881641c4406140c45081d01c441d0740d040443e0900f61850960808180c0001f4a11400e140c0c0c800042007200c00624115030041d140f0500c040100321403c0c80c11080300c440521002c099100c00414800d500e0040403014010a4002c02c046d80c905c0300d08007441c460240300e00d9031034801d80001241e0300d00900c0d6650344940681000c10b0b5030344507200b1480c20f2450454040c0c0500c42e20b10107000d04142c1c04501c40e221034502030010034500c1c101d0b10001c0c01c2002d006103010300c2050402801078460314290107950802010781c1084c4614180040440a503400845150401501034400901c240d070003034509400304c403000228545044000d40f0542455815032800315000080b800c8031500c061402c02c40940c20341109240c26402039103510401400c81c801b222004030304804030660381841d45d030105070400391090088 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 563962670 1250 563961420 563961443
    0x102103c27170904020c0106061b02030705040c140307020601060201060b0405010c02040c09082b0e0d0809010201021b0a060b04110d050402030c0303040303170f1e040501060b0a0504050307080601030f 88
    0x20340101d58415403d0081d005800401d111034901815001801500c90540321124400d40c0c01d001c00c102c4062070240654103500c1120104903d04242d44840c64210840c0381920717240100c03804414181c1d2041e80c51000582c040c800410030180e0a210703c1c0045c01000005a14040c034100c0000c1c000c40c04620040e10036580c594582140d14003030000d400c010403042c0262a01442d04000034180700f000c0501086004071016049450244103e00d0000354002c014041c00c0f40181d103840c1c0d0a13540c0c0015010605542d402c000000c0051840810340c411428800c00400051078680340032010743c0d1603500c081d0302540c1001c501000b240024001d8800001554800046542d202d00000e8a4200b4100c0425010b000005010081c940c1c000388000c0380007001342140c00161102c402c40c4a10a204030740c1004040c42e1000f10546000d20805490f030040d014100106160703407101c1414115034800030240d000b260780080e041250781020f00107000102840b1020704019851a100c00b1103000c4880801000b110094 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 563963920 1250 563962670 563962703
    0x1051902010e0d031505040605060a0f1106040b01050310050c0d0c090513060f0e01080a03050702040b10050307030e03030c032a03010f0f08010b0102103c27 69
    0x75031058034800b0580040740d9030b01c0c410080140080501e02e510141086a418001c181820030b4040c1d0411035401814032403402d48116411940c8846220701101005040c0184041c0d40104011141c0201d001d03150b44010795140c03004046c581450003910021681c240000c1100d680c50080c04c4d50026243e594001c140000103280807908001985c01c040d078840b078400100800c0324074a60000084d2448455803900c03640e106e420341058100c091140c0610f543c0201d6007800081d01c81c1c4040d0021030b1010340046102c50b030b04e50015081403020781c1c000000900c04001c110b01150b05020b01c1c002e91160700040c7d455418880d1025031b2612004042d4103652541110880003440200c1d46240350540f0041c00d103403a561205451070102c0864460b40140e1810044086002d007010320406c010401c050b0010303d540c111440309a0041c101c1031003401c000a0b503280920351542c0302c1c60b0898907000003480303007c0c421140e6003811800b1590240c442d002c2c12605100c0c0c14010301d078000f1104020fa038200b03100c08070a4000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 563965170 1250 563963920 563963923
    0xc070f1e150e0402040e1b0708090d020105040b0c06060306152103070503040f060e040240031103242e09021207020d0e040216020619031104030201051902 68
    0x1040300c01d80013840043c002603464145940785000e0380c0e940c1c41e0884041c400103d880514005c2d03000290a403030081050b1941c40c984960002507041c8181406814965075810301c411540200b030b41080320b500180300300891843c3c14404141c2c070489444900700360680c1d000104d604070780300029101200c00700740c403c0c0b040c04c0e0042082c0d03444154000e08803660355403950204003501c8240e20408010458860b20408a842c107402901c0303805c255003105d000b0a0086040391500e19061120034407480d02d1803944c003407450152050b50340c09140240f101c128208501c000341403819031540c40094156042024550a079800c0c800304541110f408604502d460902e1015081002003110054405040003000020380001b0b40c0c014107181404e84d0082e40c044d555041003680c0b41c8864420040c0010f06881c92610280317055070242c0410003110800d010b481c5826404218640d202e0441900580c440280003400381d5814069031a0702d0200c619111308080c91540083c0180c0038410403442214a500c0b1581401ca10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 563966420 1250 563965170 563965187
    0x8190501020c0322050603071b020f032a0f010806060d022505010e1b040c030605130203180102090907050a020f06101a09100f02070b0c070f1e15 64
    0x90b009070f03a030b0f46200f8840c894000015078030030107a55120120019441c90000241d0340701f41020380304e09403001c02030f41000203944030b099012031341b021201340c54111a071000c1008800107a00300c1c882e01c204150110040c40d00a00034107210b80b19100b02c1400c40c03030f10390f80482550b8200700c0946403140c42d68110381c2281d0103401500950340100c01814414107003d03040e60960802c4500600003045140d615844417a1203051101959020071840b40d9100c0503030a00c0c2d41301c000c9440e20b030702d00021141d8440340020080010400d55420050b00442441030a42a0004064001d0008402189410301708000b00b030f98054020826014000c0200e10041d00ca4002c2c4512500381c4064030590f486031801c0160380c1041c0846004134446020a0010118041510340c110748008500a00c3e070403840b0343d82102260104250240314007140030b800300000b894207403000a000000702207000b8146d03c1c1d0400340703280d500e41400d60190580c3c00c00da10b01180c50902c041d07020f0050762500c03e1050980c2803a12000ea88184 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 563967670 1250 563966420 563966437
    0x3071208040f080c01140a091101080601020a0b1f080706020604080f040b0a0c050d0306060905090403110703140d0e01200f0a03170f090727140405070f0819050102 72
    0x1140054a098004c034190300c0350036000e00720422100c140e114504c1400480e11440e10051002d928440b40c05455070280c55a9071340118140304035000d015850345d48604601c2c0c00d98181802d000720141006180d10142d00e040003900481c40200045450484002d55901d006400a4110480040e01281903100a02120054107241c94400d40c0c030640e01500402008800c0c00907950340c01809602c041c0244613014003030440700c00e0ba4610009504000030000e41c00d9010704114180101611441f0702c01d441800b8820082d4010b18414011000c00341c807040c1000b0352040c036502009032129498102daa040402070500b84998440a002c0b41130501d0782c540b4000d5000d003011054810f10b108a001c15038010b4178a03a10580c003142408054880074101b01d4030361420340c0d03140b2107604440001d105440ca030f180c0c004800c208107084010068018100382c81261103404442000e0b8051030200020f2000c10080d52004241e101c0510030300030700d08000da0303446034101e584074a40400c8803140002844003d40644200c203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 563968920 1250 563967670 563967683
    0x80f0c090f09070806011d060702040b04200a02011a210708011109180403080f0a1b08070e0d03210b15040501020715020307030807022109011103071208040f 69
    0xf42404003000e0714000084030450f0000e40315081070442604843c40920320440c0262065003048200d50810020b0302d079520150390460f0b0f407060740c5115032038640d035440080084a401d03240e0b900c0500100a00f0340c0c021040322102500d00c408051200d80f07030985820101c1a104c02ca100e03800040c501014140851540300b0030316513082802110591080c403006003125003080780c55220700c241c07000e01d4004401d0115009004030319030100040d001c11800401c182d1000c188c00d8001120f0140b116010900d14a260b02d120018100500700242190803004100c000300044580800700c074800e0350014208221048022401002c0042a00d01e40109070815888e01c0740007000a00c0490441c1a20000c2d0303040361040724018441d0076400a51003d0b1801c020001400c40ea0186260005a8030f094030a4000906200c045200d18140410b101c1c1640c001c800c03600c80400202c0d40d54140071800189015905580c0803081d8104205040001e0148641c4004d40c6c040380c1410001d5071b0300c03810440d14070000b100002e03002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 563970170 1250 563968920 563968939
    0xa020604080724050106031a0a12080d0c0c060501090b0f04110c2b050301030f0204110408060a060f0f08030d0b0a051507021306080a11040b1306030210080f0c090f 72
    0x248840e9410882c10380d070295908015040083d0a0301c5148e00302c200c0d41c5074000e0301c09007090190480f150302e0000c1c81405080c0491070801200340c0b0504940308219050002040c10300e2503010400c443c001c003401000803003000c0c442c070125072000459032070b100740c41144a55960b03016a4002880340d4207448003942000144d5007801640050341000500e100c03406204040c20400040c882402141500d05807604180c290441003015400c0c0001819045110183c0902c1440005000c010400c200e034400e60060700b01083c1a03180c00300c0c0e142511499002070000001001044c803151a000040d00d81d003502002c0301003002c1040c03001185c0c07006180e0b00700ca078210803036004d40e1401c558050014882c0ca4800e40e00243d14500249420048444a000d0144c40f03400440e544004943c2c09060303c0a6450000c000180d00a0800000707040440a01c2040b04042e44031102007041d480d101c14600e140f11000d0901024602e030a00714241103030002400038510040220700804551941e41b50781c101508082c0c600b905 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 563971420 1250 563970170 563970233
    0x1f0f0e120303091615030f09020a030614062d04090803040804170a0c03080c0c19180207081902100504060e06070f0516060b13021b030a0206040807 65
    0x1c49500495614200b44240644c81210402d5079400c3d000312008240c2c009003211114000310080c0c0100008100211b8452280300d0169440440120045210750400609000601501c03004001c00509044c401c0d1044191640e410704524005110040321024851014054900140091501c9030020709191000b0042104121000c4020410b680001404201d2040101801581c640401d60000c08006001c2010000611204003500410b44038100b520424400d04002c24025080358030b616081d041000b0080201541034000c03c61313400ac292009603d05000b41d1502540c1d803003aa0020b40741c3c00059504460040c0c802e000b40500026510f005021505040c20b044000d230500203401449405404041001103000c1c0c00d5540301400ba58403440c0c1850464405c90240c2034a0740e00541d2480d07181d140c0700006984604104008107600500162501218900341100741e8081848a5055004020324200c05130001030595001d54840c0f00e2a584010314906402282d10b06003260114101d20740c3c0804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 563972670 1250 563971420 563971423
    0x7030b0d05071409010f0602070b07060e1b011403040c05060705101a092206020309010b13140601050408060103060b0f09090c010809150c0a030e0f0102090f1f0f0e12 73
    0x18100011070f0740c0c44c901d98840380d031903d6a084510a28003d6032140108100001001014040c00c9004d0540001c90307503406002c40e401c00d0011050600b000041c070750608042c2d03820000c0008c1d00d00c9080c1e041420740c5400c4d5a281c0d03a030312050241d0742c41032102041e102c0810074104500360b440d003030058003806000050040400c0304040440814851039200b00042e0071503c00c90160035483c0308082ca0242c44441a4544e44000c2d44081c107585d4041d504c4030060580c9445000c094045148440b1001560910500b000507410034090046810040104810402110005401c606403500319800048403451440002d50030341e80540c2c0705810070440810030403100c502091648d143d02007a02e4031603a9540b62031400e0b807609031585007040411032000100c0d045080b01801ba103054841c900f000650300c000d20706c05130b182480c22a21085140c0d00040c3c00c072141d0a0110403001200026500b2005255034101c41d203c00717010031021401000407000d000c041d00c0e40300b000c100c03100c036002038842e0b00c1403180028081e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 563973920 1250 563972670 563972699
    0xf1b0304030f0c0b03070e1932010509131e050c030708010e06130504110307030c09061d060105220b0a02060903120609070c051002091c0b07030b0d0507 67
    0x69032905001400043c4102c0c00b201100e1142807682e40b00c010b4505e85c5002c05c664807120f102c4410141440c07000208804425274000c0e06840d195404800200740040450001a09401b40482c1080b0f01409120682d84400c0e03018401041c41d49400701e8003a04801803607003080303000c0e1001c2d0790f40c1d4280300511941b540458011401000180d0f9444940d80c0c84100790381c42288196101a0010555800094021010345c8540e4000344243c048801500140c0002441c101e86604141c4104200c50420059116a4070900380184600c90030000f84d0240031004180c00c640c000e000c14140a00043c0008800d0f01c1c02054103180c070706588580260540707441240c807264100e8410039005d8890a80825155400002074030fa440329a040d58000c1a41c4e0072041c428880c001800c69000c4c846086100c0c8001001403110b0640f0300d8042c0c00042c0c030f40c40a8800c00c0084803070500d1500b0305d100460303881c0001c51030444000d070f0710542c0741c06c000c24110000ea0110701110710081000c0d019000b404408900c1e0000e01e44803 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 563975170 1250 563973920 563973923
    0x11130303030c0f05090d140d2604050709020f0904140114010507020307051c08030f1611060c0307090905010b0403062003010501030507030e0607270501050f1b0304030f 74
    0x8118401c00b55000756051422038614401040c000d100c5e003030303080c40e090a4600109118001e04850046003082062815608000301004141e02c140c4035001480c1092890301d050480784049402e40c107240d10381903199480390007003241d200d40004640b65907440c4002203030004180600200050000d14402002d103a20038020917403554000080c1000c1c561044040d148229001030150880c075260030b013040b4442038650016502584e0909103c0007055401020354414030799000003920341d18090402012103d0040c000c103040c4030104900c0c45450a000807200e61010692000564980320140150f031141c090740d10405456003803a00200391135407520701400450b4441c40040c0420351040b00302c080d40d6600d9130301c0d29203803000030300c010040c80d03100b0713004903030002c04c1800d002901028500c80142068800c890300c001294464061401d0405261100b03100c0e406106010001907040c00d00003002486104030726103500c44c0100b20341c510b031144003480580303042e200c2003203a0b503880d13030f91a14014800c3c24840 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 563976420 1250 563975170 563975177
    0x50609010f0c02012003150a0b09010905150313080c0a030908010c0f170a021608030414030a0c2913051506090a0e01110d0207151a060d11130303 64
    0x203903031100c2c600500903003601443d820f060490354800e000600c2d020780c00081a61029146940c08440d00392244042c06002d0310060071040e6451140c0400500710300036641c4501e01070800c0508000c8403c01d0282540d42215481001c82221126410158214002c41751180443d000300c0d0018402c05800084c0c100854103000002e00228095031000c5d07900c541800040404a007002d854038210102820b01690310100134075005040c0102112281c11844680808890445000003803000f8083c0380c08202c241c0304081c40055182260b141d10082c40201030301d100515088000701c862400c0c5002e031504019200314403840701000e18000003240480b00390910155a180a42c02c10a61010020050248030f800050091000c64a401d10307140010314410130340c10100e55807194459000d000f150300415441500132000341e03e41a183c244025842101d09803211185d14010191402c3c0c9104450501244011034000b615002c0010103803015218843d1501812440002c85c0510310110455650640e4040e65 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 563977670 1250 563976420 563976431
    0xc02060c03010528150305040516051507150510050a080607020606060d1b020d110303040f020603071815080a021303060b06040803160b09151f03050609010f 69
    0x4a610000d210038043c694100540450804602e50740c813004503200c0d00c010009a151903a950102c0c02d000d401040100b0010f5110400c0c8002c3c0081044803901031035404101035011890030001921565040888083c4007a0100740c000c10b01000c4015000d105801c140d0510040c6030480c0b60080650302c40c06800d1048281c254042411440021011b05c600700c04d400800c3c29450301c07000c10425402031086100305940342d05000e68602400801c003d401c9800307070024040c8000701c04000c2c290006014070465664424810007001c40c080e850102c082903010741d09941d4948441c0c00444071000642c0c0000a0195643e10000746802c0d40304042911604940d10384c1c0361034480303840141c217070f00c0b942c4090386071000a04010320108140380d11402e043c460003130034030f0315050341c4031215815508954840d2000040100810050103a500c0501c3d0307101c07407541e002c0c0129016a48040060580141c0f203250110a40e02099401d0449150314902464202003100c44924041c91864042c04040c42815034160800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 563978920 1250 563977670 563977681
    0x1608090c0915060c1e24061c060605040e030a0e102a1a040201020a0b060613060306080f03091e0307170c01020c10090b0310090603030c061104030b0f0601020f100c0206 74
    0x10410200c1c250003900e04500d070202e040c0301d00d0010a4047c1c81c0d154482400b0030724081030102141201c0c44940f10300804a5100d00e04810441181d0840314441110341042010b0011140c0c86101000c1c0c0c880100d0314074410503520700c0220740c4c0350041d00340380607203c402c49440702c0c01c40c0c0803100024982e48140780705446e2020100e41c103030819000385c6009016078000309900c0001554a010980c0c0284089d010070304014036480381619401c6258850b0000c80d0345e910b024006030b04240001e28080d03102000035881c006106c000700b0010581e26141c040118038681d2100c0c0c441d542404030742c0c001c0092110881841007003001c1c10340c9070814980343c070b400f43c4641c03d02c0b4241c80c20f00c40d9508180148607122a290316113002e070401607690004087c03c03040446244007241424951154102460081d91f8255050320b451401b0022210810210000104180810030000300c09039000d613800f10050381d0785c003281d403030b510f00503441c040035042c20003034900824440030220181c40e071168010100c00d41c200d41160300c89 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 563980170 1250 563978920 563978923
    0x3041101090b12060d021e01020606060315090414060103060b01081e01061107030c03140609010e030403061d011a0a0e0103021005091c0b1608090c0915060c1e 70
    0x10701c10ba0b201c41c84103010441183c1100300545a20200c05404441490700d542d00207500400490010362845640c1e800010141d68100502c0364443c0b8299409440d50a0201b10510102200581203100f6015400000c0401c4038401030780401200f410111892540c41e86010b00151404100b118001b45001000232001e50211843d0492040541c512103101d90030160304481d51030800c4400c039182d00c6231210000000b200c0540090003540102c5c25042501c940503885ca040040207441a00d8a80c103106070380c54054404021501200d5200d2030014803c0d00030790b1100602509201800055460500903a000840100c0d64600300001114031500039501c0e5807070f1070307070740c080a0001a410480981e4030744a03450240d0024000c60100034032409041c0c0400030401c481120030503007220050090030030b0100d1507484114001c48200b40c1e051031081440e145211945d2410010701c1709108003480c4020034110880c610005880c0800034007a0345d510b01c940700085039519941c6c6800c21002c1c11320100900880b10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 563981420 1250 563980170 563980187
    0x21504060b131e0506060f0c030d050c030907050613080118050c0102030a02030d02090a050a0305031306030903020c130e0106030f050c0d150906020409090f06060501021903120f060b03041101 84
    0x140e0a108041036041a080e190003000018032172504902c040041102400c94600903103260071040300255910102c0546a400741c5070b000d0705500701e4000900900501900100300c010641c1c100352545c82c1c5030349500d218942c4220580d8400145075180c040000d407010712000f90003513074501070000c5800050f03603100126600e105141503400160400d115139040d511094000340051040140401d2f1000e44540000c0d0055086a008407100e40c00011081c203002014407814005106070300b01006030500c40d0310b01070740b96014915103c0c428ac084184c0c907100e2522550001804a03043d400802419841c0d18000d01100f04c40707202520507100e6180a04110301d8031209048a413503200345980c07091001490104044c00c9008003c5941c15020f020211714901c0394801d10058600810301c1c110480c407141080c0d0110354a980159045401c00d1651300380b010f03401d15040c00c0d8140c1c0b500e046a074810f1065400401031618168800d0128141000064039441c42c3c0007850082e402007c841c1c14040c60030005641d40103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 563982670 1250 563981420 563981441
    0x10b01140c0d0c060e01050910060509070512040302070323120a0507080c1009200103050106080c22030b011a0c0c0f010318080a090501030b091501021504060b13 71
    0xa00c56440c0b54020b503c103007149042d25229010210303140a81e40c00a40c2502d0086814401e50341c04281070030030803a0b282c0101801003000740d41207240d40c01c07c4c0b600240b442c41003130709070480f0f038100c500481c3c105803003045103600658022401400e0300c002228181401241104110068404e040e0207101071350001040f500c198815458991400d21700e40d50f02c3d0703031a81000f00d000503107000b500400d640035186401a004001e100e401c0700c819204010401d10850038170300350a1810103140c2401848004d420440711600100f900f500c160300c0f000100000000c3e40603a460348003200321440740000400207502d2a05050f280468042d0201c00303000e414204480c003800405e000d8581c007901c0306100030f051100c28100780b508185008540861a0701d208403120032001412591044002481c0c100c1d42d41c811226000341c4000d107014090100d0003800aa030b100300c06042c1700080059807484440e107078001c110062102c9900380c54400eaa250604108006055280103140200c81c5c460030002180c40d0386c4141101030f03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 563983920 1250 563982670 563982673
    0x1c05152803120c060c050d0609090c0302090901061d041e0f171b0d02070f060c17121003030e06071a0c0d1401050f091b2802010b01140c 60
    0x1140340d51607003081400308659080901000140a2004c1001030107208410b50454071983c3c0c0d00e076040d038041c0c412981150700c0140d2152405641000295107400c6140c1108c0d0120b030404542d441e0400c0041c01030440c0d52003d128000700217658821603030580841071282c2d014290b0b020a02507050710010b2803440c201c2000f820032851503100030000c2e0180c0e5010414650056030710303047c200e841b05c2108024130441d9500714198040c060001035141d0400c490b6029140d00700c40c504e00c89243c00c1d005000842403120041500400e800b0b40c0650785250030036500c018980715140d19113418101140114803501d40403d0300068000319100c855810310030704480a144d440003e10840c2c032402c0b4808103840b0009404214014002c004d085030410b1240521002801c0d445404030055240008010420451404c603901a0855a04228000404140e5011401d03030380c600c01c6642d02c4800300f211303c00d02082c410180c0503510a0441e800001d40c1540000f0070200d080e01c5d400310f441c031010300d10051402500394101e502e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 563985170 1250 563983920 563983999
    0xf0901051308071a090625021b15030403081807120b060a03050708030c190201020c150706060b0a030b01020114010510020c09013002030607051c0515 66
    0x42a07000203003411400781d0f04a01c4c9600403031624001104d010740c0c02c05260b501810500a2122401c0496906100354208590b213904060202a40740c0e001486005031103900c81c00c4250b9181c80c5c0d8861078841000c0100700540e02d00d414500644400c1040d0b401c0309490314880003451040c4800a42e05068811201e07101c41e8411056803032036400d01008000c160081c0f00a040040024001c11500004d4205440a16224200c5190440c5000c0841180e02600d513881c040c0d070350140c2d802245080030030304142c0da10810140f40d0b070454107440c40381600080100f490305600061f0030b90841c010700030051241c0d4040c412401640c00490a80d03c2400c40800d266900500400444ca800e655090280c01d550042c0e4000105400c00140351400076400709403549951028408218901480803090390080001000d01d450a5000b00c0d558910040580c0107000c0c0000d803c1003a2030070500d1841851810003070501140c60b0501517144908a14a0740c14040c400d418540c10000c89c019446034950541d48044414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 563986420 1250 563985170 563985173
    0x908030703210f0e0615030613030f2003120a09150e010e0312100506030c070b071b050c03010c0509090c090f1905150f031609090c080f09010513 64
    0x40e0310070b0105640312025a10382c8840b4403a481c5018804544d100100a00010314014580d4a5a10159807025100760440000c1149400b007030303a5484051a014688582070740d405420648426007c4c0c1381c0d084080c5200c5080441c84580040100303881e011000800d20a916103a44080076240038a50040030002402c41038014001d159112101011035100042012200f500e102400c0d0340c0007001c0081d1420341c00c2e04200428401d81c401400a0100780d51452075880c2c0341c00c100c1c0842c0180c0100030008d04002e1b0115020501ca01c1c1022842d840050855800384040c3c07828642d200c000b40c600b00d020f035080003608840103000d41d00342d80e01140084c003048440c1d5101ca4504200750b100044595001407003105c0601c0c81d860700d1b002c0504840c5440c00700d00d5040d041000700407040020946c1000c0d4014208440880000ca05061340d821511681c480c6405811101e070643d2110869005250564134141e40202c940743c0c450741c811301408030030f41c1c60f0a00f510760006050030394004a60300c5841c000b481c4207440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 563987670 1250 563986420 563986457
    0x150403121404020d030513030605011e05060708071a0a020c0105010501020607120b030102041a0301030c050303035a1501020a081305030a0c030b0a14060d0c240908030703 75
    0x121721a15000d89481001d80d50808000349680050b11a0f5603a00014040c861440595407003542149180d000c0e0f241c0b07003e000a0f51441801c00041c1482c05c04100c840410041d010740300c00c24111a042429540380c9070111100070b40250449807190760800000041c03550000c0f0316a8011840780d541c1c0640002c0303030a0401c1c040c040c903030450760f00356601f00300000300c441001d140e03201c0f15122006070720750303d52550038a0402d1816a4201d98429002041885000826210000c0d20303100e21000481508244000707901100301d0a49000403110840b442446c1948280002110b440c3e219610f0340d20180c0f1404402c811000c0b41c14030705805640440c4c07114000c21180c802400704507101e03200c400511070b21803001c00c1c10000141800c0b25822a0a181401004128919150b00c2071812408114010501d81150590300300501f0060082c0c3c82050074078280196000e040e0f020b070500b40c252011243c2d02c103010bc140d0244034141403002520b030350307000300e100800071003112542c0d601a911900c50b400c0c5404c585 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 563988920 1250 563987670 563987689
    0xa0b120304060513090507020a020a1409160302071b0503070b130e100f14010306061d130e1c0809150c03060f040903232a0f15040312140402 62
    0x5203910244218005817003085400380c83c1c843d809a42c05480f641c042441444854019038001c801410803da41500d01c80e21881105640240700c1703800043c03084010038040c0c0c024418000054406035240501d00b220700100c000d41e2044034400d13400c980c0410342c0c507000f900321405112542e40407046446001c0101140b5200382e1504a81d001540e80c00555403011016808900c5034800c075829103e820b010803140da018070404004280d1070038815085240641c0100c5d10200030a00a4410780e0f1a40b04d84d10100050b600c400302c03040c002011100d0312454900e4081d004160b03034034810300003060200000c0c2c5c00900452a114861014104441607407100d0f0040015234000819180e0406c0110944413410b036a60300400404900030344824004000603c800c1802610950828004510401155101c0c5062006543c906079041070300310400505200307441c0c10f02010f1f01000b9024880c41d101c40791040d0144800e40d0045220303459403207a410480c081182652030f0064681c60b4540c0e50400980541001000d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 563990170 1250 563988920 563988937
    0x412050a0507230a03030f11030103020d030f030609060807080f030a021b06070206220b0a0c0201050702130207031e03051b22060e03010e031207050c030f0f030a0b1203040605 77
    0x1010200f0200c1c83c0c682200c03100c0590000c3d8448030386902d24110b40c4034200190340c6400c0010702c2c66040d5004129030f00c02c0c400e0000d0030455400c51100c2c0142c400c5d44980b02800002409200300d607501c0303610310750701c00300d500881d4600d0042c42918a02c0d07000000c201c0c1c000c40701316000b820382100003a0802c540f1200800d2600d811002c100103840040e0703500c000600303186064021400b418681001c2c11001c501480d00000d160303c03410012546690b40120300c0085043e0b09180590340c80d240d501c00308120500303d0b8400d10303006002203084400c15030480600303203103034042c0059081c8501e0103a82c02c90079144151641440f5014440c09040950a4a001050140c5100151140398240d03260200d0310000c469000c000061841c0d40b400e40986000c1c0203a810144115008600709810004060b600700300103402c03041480780c009103880b1004c20a106848120000b60000c81c1c60700f040390b002804e075910072100300c0000761a006004c021407415098216078581c4010003503050034200705080d203c59205c00ca1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 563991420 1250 563990170 563990213
    0x180a020403021c0b070e03100f0605060c0304031728020102091305010807090204140f031005100317032404091e0b010b03070206041205090d0b0412050a0507 69
    0x1001c4007688940c0d402c1c0c21903a03880e15942d190118281461140c081000c1c00010801c4400010051982d600042d4a00f1004c41c800000560050080e59100100103540c0800d41100000c550003075032010210141007100c1c002c0446081402503d95040094850140079a040b1180392609005040000c180640340084900006240c4140310000503401000040000c90745900c1c5c2c40180200b803c240000c100803d217440c000e41c02c050603c002c03240a580710307100e0310b4001d888400140040d030343c0800c07042843d078084050030041ca0401d4405007000a02d6800180d079840424400d8030408800c003000c60344140386050390220141c03402951481e000103d6601554403540301c60a10000c610f0030b41c5411242804171165519010181c42d140d07841a43c140d2010329120001e004204044d900490b4140c1d0080d80241c543c1c812004103c41600d15002d14240305800100080c200c10400c5092810315008601448062003d40041c420494a41c801c101c0300100007041480160005007805200341000402c0d00c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 563992670 1250 563991420 563991427
    0x604090206031026031b070e0903121b0304020f012001090210181701150602010c02160501051215040e0d0306060206070824090901090c0b09180a02 65
    0x1000641182c100341e60303152a50010040401038180041146503501681079610f4a00d0148400d0300c0ea16802244d803140d00e1440c22022410480c202800014058103080e5040c075058100307050003d5603a001f4031815504600b0030320100380440d030004101a075501c8000c5400346180c1e40d95003840b10514402542d1410b0102104603210903221111088525102c3c3c000001038040c414010000ca5014041544040c0188612603200180c200c451180035941d20f810380444a00080c19100d0041840034001903074000320004c04960f1981c1034001d05c40340120742d0700712102e60307074a150030b200e41108511039036000c0741d03040000714251103c0000d07923540500400b40c1c1c009064140400718041c2da107100d0051010381c11030080c0c1e01d0607940512480d07000c5c1c04184010561450100b03009014500c0180502040d060303c1d200110010071200c4044286030301c080e0100440c6c0c104203d185001c0d03d20780d2030840d8203070241b0384041500742c3c520f0f0541f180640e0040c49080d0003c012820009110800b0745008540360302003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 563993920 1250 563992670 563992673
    0x60b010c080c0f1b0d020d21170a050106020714060408030304032309010f03020f0706090c0f0b180d0206041a040302090604180b1305060c041a0a0512060409 69
    0x9078090318680e000380c0c024090258104501a042040c07425a2421041c813200403083d850b1211200e0b481c01d144e064416950ba19980d04019443c011203100c91440b030045241c105604a9200c00310b10140501e00c055540705444000c0400180c4a090140100584c000001048034281035826290320030409000e80b85416194003020382107600c00c03502500490450550b4403400c00c1b96081d5801d070740340a9000341d0f08014130300000030900130b0f8030604181059004a100381c05041e441044419256001c0702c104881e44451810f541390b41030502ca11850501c40400001e01e20b070204003212640120306c7d80340a11180c1e890b0401034031110188090340c22820502c0040b4090308004000010380070001d0440e07461b24658410018030a0004004c24015420710140050607072642d140101c4469001c0748010050b03440000d0b070400c40c3c04401c00a0264440c0c4814424102400d400410546202000141c0a00c00348400d0001900c16002c0b200700040003000503111440c1c06031101a080b2000500115a0b101c06 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 563995170 1250 563993920 563993933
    0x5040e10051b03150102070503030a020d080a180b0901050a0b21030f1201032d170903010c050d060518010e19020304060c03062102120a021215060f0d060b010c 70
    0x200da400300e404c545254003d450390b0b010049040140700442c02145859503081009407950081c00d03c85050282c8a804141c0c61030964001c034a04800c103000020040001e418a007001104c1500c442603594a00b102048401859001d601c0603c0d8019000c8002e00441d0078250340115104c4c90708040d2800b05000220090340c00301e0080409402d41640c0341100d50450910f00500c031440040301844814035000400880e4040c00075000b4223400038603038040c2e14000287d0084510410401d03903419444c05005040b01600000540309018070000d00301720355174580052141308106203901c690900b010500411429001500e45640004540e0010358020070407030002c0142c1c1c20a9508031482510f82a171000e545606108020080210b08442e40d405860300c101c40b0740c1d145040901034081ea0420340784010042c0c080000c0b4a0007a805082c10030304026070100c0176143c0686020300c0540f14480004240315207055007282603448401410f080c4124920359488009100805005051108808c4800046a00b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 563996420 1250 563995170 563995177
    0x2030105070c030e01020303010e070e040609020c01020403110f0105070b0c0d05070905030f070506090d021c0308100605031501030903180603061a04080a110102160909060605040e10051b 82
    0x802c1c1c40e14041c803007907480c0c0600603404203403031107046520034001040403040340713205075400016905000000c45004004140508119001001224000102039600e50b00550007042281d0146c600ea802d003248078400c202c80d08004449490000300e05000103000701721000103540e00074020515591501c10104c1c0410700741c035021940c180104140b80401c002c641000e100a6000240d068098404241003030001030703580c005c00c00018018403a0015002c11500c4d45542182d1030005400c07214401c460901d4001c040c02000c541d4081c130004e44071000074880c0d000300d045e01d0141c0074500b5401c0d100199100110010850034005404101040c818100150403000b040c0004e04980c5c0d801140c8641001080803e030780401400d050801e0041208110480000c501544900d40c0419000a51a04540102e1070285c0c10703040e4800400e25143c002a14868691294465901c1070740180540c640e82d01c1000102c8032082c1919015400003807144020f0010703588002c0c2e10008800c2c00849020345003c0300c240681 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 563997670 1250 563996420 563996431
    0x606050912030c0703030e0111031303020a08030307091e03020d1a06030c0d06111201060e0a0b031306110c1f0e030a0f03050603030f0d02070201030f20070f02030105 73
    0x8200180c41840390400c401d9400490901d24019440c2502c0103000940d205a2840098100014888148082e80c420b095140070801c3c9082100d4588800101e4141d03080740d28402288a400c180a0010703a90750040180c1e4810314894480501131843c0840304240508900c40022040210010110050390340559010809000d401078043c04070740d030715110080200103840f1070301ca0340c040106280542d5940042c9940140d00140103d2002442da0700940d1318001c800d02c3d042c60034164400401e006074010241005d003441164815191540c501041d140c602c01554540722090780760465801052013a081100001c040119507403408000103038440c140380c1709081c61140308440c44102c12240126014036150f1204140295242c0221824040c0195118680003001d05446400080e245d07035081c002d465522141c003003102c2d5500403c442c020025400b85400328086480c040d100340d5030112501c150074210120840c0b03030690031a102c003422000d0300b1002080714100740000070580140c400303014050184 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 563998920 1250 563997670 563997677
    0xe191406090a0204081b060d060608042f04020a02070b0a050408060f090d08070908070308030a140108030d09050a0228062109260c120412020f130606 66
    0x1400c0c034800304240d19034080c01890307075a0b0041c4400e024004011402c0c00d2002c070400c038081c40d50200000494107030b0094101282050340780600004000fa0401003081c03050788501100c2110340110f0224a01a038a10cc256800c100d0000e100040d4a04007980104420240342c01150f42c01e50b6610b28086603580f01509810001e407010908100c808000c000e020f800000c100e01802d0030385418440e9036580c3d509400807100b0844440c0211742c0642c0201600c0c0043c00c0e20b9810b5a01c2e5a44900302481d0030780c0140c400084141c035011038040d07510103aa09550607034480001035443d008200007980003412100c6000e80d030b180a2000000010390745c58603406c1e180d02c0200c0401d24410594088a011140d459003e0300a2100100d00507002c04826009240400003054001449200d5828046850310040c000b442d100304422000e80d00340b044801c0680149082c40d0708071004500d84000c04c000601031846019411440c684c3d01000524201e5401e880f59080a803a000e000d4485400c01401e851040e4403401c0070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 564000170 1250 563998920 563998961
    0x1b09210102041a070809010503041506080109021002010e07030204050c09060304050a03030608030a0c170708210921220f080c1507030e01050f0c1c0306030c0e19 71
    0x100c80560f40300210582c0b0b000281402c0032482d0320740c04014032540149034108540000041c04110614200c9000c0c1080420f007049265110004980200b1140d4001d92040346002500c155003441401454003c42e880005400d40354a180d0034880075207409040300c0944030341400410f8098a172100a184140d000314014030300b002040c01e0203012a100c41d04054075036001081f9609030b1640000404a800b640314840c4840e0142c007209044690203a6680203102d0800082c1c580206040303084126400ba00311030010000780c680d2090039588000c4410391b02c640000350740d070a000c03c1c0c0a000207461610f8101504210b0003a068075110344103e5940c010308804d0541403070600480c04100b1100034070b041c00380c40404000190410302940c50041440003010402c1c04100141c441e4421800d44410b40e290700402d03510341032500e00300c0e074aa19044054800c40c82c6405480414180f0174090501140e8110fa084d4200d0340c180043c2d101c0912000b089000da150061600000c4043d0314418180702060b0010f14546 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 564001420 1250 564000170 564000179
    0x31e0c142a070914010e0906100614120a0f06082e1d06071e140306040906110408060a0209010c021504080a21171303111902181b0921010204 62
    0x38038140c05041c0385010b511010400c000e01c9c1e43e03203005c035041e02c00c2810407803c4048550b20202c12032040525181020581d0024071441d07484903000140411f205907400d02c0550344810201741d444224044650b080003012a43d503030305180c990b07400d8203401041080032030385600c41030318903020403440220350041e580150100400240c1c40702440c40c0400011000d4100460035850060000102850700b0100705400000f20b075841e9105e501c0010f0542d40f111084c844458400d8407841d05400c03501c601300325809403100050320301e5a9803003120300130b520584584080028903024002400324600d070307484c04010100408143d4042c01c110501c40f0511441810311003084541100e444e14002d003100c00e050040061488142c020315030072556000700102c981c00400f04060400300c079030b824400ca080329a030050114000700035900c58021180140280c074428542d03401c10a10000d41202240c1f40100e4242c0300608034042100b0358000c010850f80101035103002184428800c40402002c1d40300c1daa00e0703500107810003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 564002670 1250 564001420 564001439
    0x1606050924010b072003250807030f06020a090e09100b10120f0603021203030604050c04150302030415051609151b0201031e0c142a07091401 62
    0x502440c0c1c041a640c0803545407500c82001401400b5000340000e5900c10302e002e07900d110340b1020681c2440101290040c20b0400e800c2e0b400c411014400260002032003c000c601180c0002e21482140c1d40015003035010210b945a0100a401a140c0002000a11100000d4080e40b00341014080e0440002601d11282000403039401c039030517025000c0c010b0086c0d800c524000743d0040100b1649803a1424041801c01003019104018841608001e5200c40c401c840c2180c03800000000e03603c1598207407800c100d03070784030b8030403012050141d03214210507202da00b88032a03441032103074000d19045031083d00f0002190384440707030007400e80c0d408680c0e110003040a221099244c640c0029910002c003500e0b50780154407044828002c1161400100b80004065807400200443e4400e600040010000d00e00413450046200c42c0680a00b071200e60400c0025034526851240e04440030407038420010480d0740200c00070396445411010002184011258040c468000071901c1c82030140b901c000c00c1c3e14103000c100758100b22194 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 564003920 1250 564002670 564002713
    0x5010905030304060b041b0e10030b0a030b1803130308131206090b1b0403020f130606120c0e090a2a0e03060a09030c02010c060207123c0516060509 65
    0x101f4000c00e0500045c5c5c1950841c880c0d4004d10810380d11580084800038040c1c0240090040d10364121007907401c008140311907040d1240c05281898009510240706043e056034030b0203840b160002506610380300300001402107000f01081c3d10080c6407464555034031100100f55403400d1000751000d585038070400080181101c202940918682c441c400e00500202699070346004500009002d01410400c1d40b0071940c403100c1c0c000035845d40450600c03005840e50401411307620994940326515041107007415899000c1d200c0c512034504041d21a03013581d500d61b44410058207500c03003403e140021811050003640800d98041c00740320104d44612400c0b17116081454944a00208031100d000d140004a000080d40000d01d0b0b81d28540910300f0100b090981c0c2401d1000f485102d000400f440d07051700c5203001030340e040a1b2040c100009940880603078425800105d030442e200010100110f810f128040d08080e000318082d014031075a07031104003008001643d03410100d502c107884441c09a44504c01c07002e1a203d02016a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 564005170 1250 564003920 564003941
    0x5190905131104090201050c01020703050a0f080f0f06010e030d052106030304060f110f01270302060615070b0a0522200117040f05060108030a1b05010905030304060b04 74
    0xc81403034100354491441c0320b80d14880c024400e03503e40007a90705581c411010741e07031002a200021541e0317414a10b405805503001c03918280204001300300c60303d40d05000302d140034819844003500072600c0d5201d150a4110316002801141407081c04010b10b48240c40411104030400032075210f5a50326110003082c0d40e8901405c1984110340407a100420640c2d8070040184c1c0d044130481d05001300c0e0200d0840045d5850300700744a090b150b51080c03d0040f07840e0003054210f602ca24102080300000c001d00550f400040341c0a4280c0036016038041000315800341000d02c0311520f14420284280d0030000140d6481010810035030700c4003149502d0342c1c107001c06040f1456038250540801c1c0d4074081d40c804241c1c0c03081500700c0348445c0d0101181c0180f400300c0469001e03806180130720890000c0f46009141514104601c00e0041c0000d03110b40c8071340000413036603660005c1150a01001c0d13491f030108102405040e40700c5502483c60854080d501d4440c0c1c000020800c001030340c01580f08070f501140032035100040c413049400d040740 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 564006420 1250 564005170 564005191
    0x3061314100906270906110705061b0306060a0804150c120501270b0d0c08061e06030c091f0609090c3902031002070c14060412050705190905 62
    0x30006078100b10203050744d0403402940104089407203080517401030a50803601100d03014000b0303d0701e04101c80404c07030910451860160f440c01c0403a00c1c0c0a02030740d010856003290045030411a8a84040c015880306078454401c00b0302014045680444109890110070904c01103132101900c26014038042c01000d02500100203003000c0704c03c9542e0510b298001c4041c0300c0611940e1040012081d40340c0b000c0c20503207035070810b4441c01903a513541140c035a1000211074400110711410721a030070082844480e82e006e24801002400090341c2d1500700085424050510408440820040d800e214202208940244070356166202070519141c1c0e41d0050741d4100e1503c2d0100242c410f0b085030006205490f0b20349003080707015901410134011801c2240307540380000c0a5418494029141c003d001329800074103800e031182000172101965448200a500000b422995010005120502075084140d90629540b070041080351a0b0300c1c0c0e6038000c1110b01c0414954041d00c0450f261080c08503a01502481d13800840024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 564007670 1250 564006420 564006449
    0xa02070e090a0309300807060f0504080a270806041e081e070f050309130905030717070605040f06110c1209010909021b0c0901080303061314100906 65
    0x50f4001c19290741d070300800b034030b101001090b414650341c0d070403601d5161100b003901243c0c0c07074505080441840e00403100131a54503061240c0c10395090020300a8a006980c007104942c186003a04005036508000120070050300d4003c185040080780803d02d00720000c0907800090070303407070420307040c00c5d40c010901c8514007210341a0044103200240c009000ca41c408461030481c0050700001c40210190361144c1000540300495a51781601401800320040c84c42e6201102d03114514030301a04c610301540c0c20248050701c6074205005800104003105400e8031134120401a15180800c1541c0d00402c5480c2910203a918046403001d4004200841c45171221407036003078060a0420031003031405a9200f04003100300710070000c00b0841035010303402102102d02409d818003040d900c84504a48040c50407072580c10100051041c41880c40060401c000c445047c1ea0258000c2c52443d80c400061200c1003581441104006984040c00d501d00c800940805004121101c2800c44080ca0034101b03000b83c50305600300e20351a07800d07034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 564008920 1250 564007670 564007673
    0x30f010f05120613080702060d0f0f0b0d020411041d0402040b040621030315081f0507080403031a09090115140d061505060307050408070b0906041412030a02070e090a 73
    0x92241e481801c08200d0184c1000500e00529140900c01000b0740102000c81d01071000d43c1d00e0f070071950403501051000c02546602d0380340c00045d2001e2295040d00403c6020001d00503090a80003000340003202c40c3c1452405940e00742104e50407260055145c2d19041c0a801e00c011850240a4040150700880c0e0610405040004800300030a141c1d80d40c107500c400c15642001098040e80101c40c140b4842c2c00384800082d95411855101c1000300c864000d0001c42602281000c1c00c584101c1340500c84541d0355a800b0b80d00c0ba81c05800030040c180f54400610702c0e00301a0495540d03010421071099480340001704941d14042c0d00c0c00840403441c2c02c2041803080c14500720071661250300d0148610741c2c001c038010071407002c4003a081c4004038685d00555004030000080102d210b410000400413944e40d03104030703136031582d451010369602d0241d40748184c2d04c614104000c121000b0461294103840d90001d014a00c8111003e500c140b4660082c0351540268209480c02c02500452141d40369000344144041c10711104079 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 564010170 1250 564008920 564008923
    0x3070210150e04030e04050a090b0c030c03011205160f0611120f070c050301140619050d060b2808160806072f03030109050124030c0212030f010f0512 66
    0x55002d540100c5510400080c1458882c104040392001d02603c03c1049080140745840170303241d5080c080c1c0b145178904010607144002c0782c1c1160710614500f840c150442e400d102e40c0c850401980d40c3d06844c107100e045188250071914680180c0204100310042034a0b51a02c00d000c0d2088800c5003000301c494002251007042001e42e0400c88108002c080d0803140d94007c1d91074032022244954002d10740540c40c000c40c0c0c8006503400700304507000303d60440742c02c0c1800e48a00e1030071551a01c9401940d40054400d0001c000040160700715440d600c100812540c640d66075520044030107000c40e00000e41d56002c0c01004c10030b8070828000004802c1c4d81c01c079210102d03411b00720300a5903000060411005c1004001d640c0d840c0003000841c5559000c16071521b03001000d400d040407943c03030b0003c1c0a0540340c84d140c031000143c44401c1403c0c241c02039000a000d09103400000c1c00580003400000080810350141f5040c2041e06e110030b10040d4452075402112600c3c070350400082d000301c04485e03000313940542c82c2c05020b001d030281c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 564011420 1250 564010170 564010211
    0x506030c150904060b0c0c0118150c080d1406010912030e0906040608030a051305010305191a0d0507030b06060405010c08030402030102070803040f061a101116080303070210 76
    0x401440d00d654038200b51001c1070007091160710088004070041540e41c0403080c046031498403804240d0702c02451514180316003504504601c10342d4403c0d02410004440640103050105296014610f001d05010b4654140000d031410403982c45465000541008455a0041d21000150000442200002032141c0d000341c404180c050b0707282c0c4500c88030000580ca580e11504038030007034134641d01607030f1300c1d0090410003824941000c010480c1d041040940403503154800c0c400d1a02c986002285075080d11000711040005003414130802d8144901032039003002c152560342910181c10706c035800806039503107541460943d01d030018200502c03a60080100f000940ea0118034910307095009102160b981d125403000a0080c428080000d2a43c0d002008100038042d5800d6600142d5002d05010b001d80412810300381000c1d540158082d0780400016002d0280707502c1031004a51221490b001c407821186003a0f9401000c00403039001461981c000800c1240301c0c1d5051000182e000750781301c0180001d5804000c601c89070407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 564012670 1250 564011420 564011449
    0x60e0f0a020307170a061208070309052b0203010e0715031a010e01570818030a05120a1403090d1101090c09060515070804050d030203040b0406050901030506030c 71
    0x1116138001c01c40c0c8150075441800200031043c03006101c00001d207803084407038004072810740c04a1140c0000195900b825100781c207405407410070465080d660070089103026010a80103a8241d0342c0e03060941c21000c0d0400240000e4005d4080c1c2e11001c0d405440c0040665401003130444102900207101c0d001179820005104985800f42400d00c0561a0403007400340305200e81f0a50310a04a65442204040c02104140400d13407102454040560160a048503855440d400004009403001c00546d2911841c84422500c0c03d0001003c0d10161001034036114600401c801d100505a000001c903146415000100c81550310b641c080c0c040e0440ca0301e00d142546070499803082d4024080e540703031121540c144c298403c10b036041d0f000c2000e002e850384030002c5100038115402814001c0310081c00111500516800fa100c0301d0391f000315918a400c0c240410701544030145101141075202c14003022400d074201d0006480907180c55030782c03107403500360600006040e20310190066010740c00c0105042259100e1512030340012 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 564013920 1250 564012670 564012707
    0x306270705370813050114150d02180c040f23120a030c03030f05040c0f1e12030c0221010b0609030a06270605010f0509100621060e0f0a020307 63
    0x144e482c03c400c0d0100f0441104010099441d100444295141c0d0401c0c1502035040d0703034142c02d28116060f06002c40c18442d144041d40c48040700300424080c0451860b22544150402c010b1810541e458444076444846500812004000c42c10146044d81041c40640e140340d03401c8a007140000c0c0c9a0324101d03280c1c1c02e80e0030050308200304102d0720028540240c010040301003445204011925203402c01e40308000c5680140c40389405a60000144603c0b100021031000540d07041140000385013801c12100d0b46040c120480a00c02070381441d030007581c1c5100d0003e81c030303110703004c22417113818206a112030844106081c200e200359030034040b409454600040081480c0c0c1d208200044055140b40c42011707402d039002c1300c003c0300c04071465194200100c03a0002812208036200c0070500310b864100300401840101d4207550a80da00c04002c120f800e109410b1a40c1c0d00104009500034500034212050603174102d90000070310b004511007400070340e002c040c141540c0140c030407a0460640c1840003004000c11000801e001c1030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 564015170 1250 564013920 564013937
    0x52e030903090302150307030f0c0e060c0c06040b070b090a0f0204050a1d070806090111191b0b0906090d0203030109110408010c03050106020f0d0203030627070537 72
    0x400d40542c6001018540041000c11294600f039481d588136070045030103100090030400103460300785150051503642400e640300c0708203100080c0188821034100584042661140b4502481261501030080000d030100c0000380c0d60340d06090500590a44001e000c40c002584040e8000010964010a0f000440d40c101e80101d050740f80c00d11110064814000d00b00d800d104110100000540e00280c0c3d14204c403001010707542aa903450040b03500300e402e0700d181c18042c00800c2100b02d6088505a48200649442e8100741d00303440014088800c0e00300301801304649030486074003805010407007001a69400466070300140812440100025141c3c0418401c039401c0d41c0e10746514113010780c0c00d1002e50300504681d000070842e000e0782d8840100601028480d140160007040703a00c0c0f007481c0c0089040c2040c210290002c62031a10303403000b0701c160208200e480700104580d4410024074a4413050005006103001ea4030700d6160381120441c4110071401c03012041c00815009450300c60300d046210300c00550901810700450 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 564016420 1250 564015170 564015173
    0x10050406050d0518010e0303090d020c1f0908060103060c1d011d0307050301050a1a0d03020a150906020a020c04050106051303020909120403120e011422080313052e0309 74
    0x51445010404c240320f5092900009a00b40000069446020088121810f1508111081c0d0302c0e54404079400380c0001d1201d45091029100e204640c0421000346403141009644002150130003c0a8108580315600c6003c0d1f11480c541c00019844005031041603203407400d81e1100064041d050000b07000c41c001c450071500301ca403543e040c8018001040060000d00043c5451065000109405c1281c0c1c05440070107140c00a06003820a9942c0d81c0301d0385500105840f04481e1a0103065011248900004a440740703070031000642c060001d088420003503001401d240300c004041209580c0140c1011003001420702038a0400118071103000103ca8040d600b0314203903110400440e003003030903c04240f116181d0001d8004200b0107a914203403190120b90343c408041d04826001102c200d82c0ca581c40c401106010310014510a2641890001d0070445801c140c003030541e9020304600b950440200d0601c505c04a0b0007c00644c1024085150204138030426000c08548105090505101d0000b131003007003503950f402c2c010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 564017670 1250 564016420 564016441
    0x70809031b070b130e0109180809031603120206060102010b0d0f020d08070b04060f090c140109090c02010f1a0619030b04050406020a020d020105060f100302070606090b10050406050d05 81
    0x43c0180240f01c0783d45184402d00c01d00b01c40d100784030b5001c080103000c0c00024401c3c0984035a102610021a06804030b950341e4882414a0b0002414030341c0c0b500034004110140b4014031a403200645c0305e410300401c0f0030700221000c7d0030807000030912415a410700003003080c680d441802108d5100e0b801968902d82407044d0010405c0d54003a460003c25070280012800140b00c51400b02d90300c01c40c0306020900c04000c01c03001c000f05480444030010646640004144560060148143e4040348189800c0700fa15543c0d088880948051510410150350b4800d05d1180ba000d45008078143d10100380801c000e04000440070038114854032621202d504480ca41c030700e1240d0300c20741241521000c010001c0c0414105420702b07000a50190840303401511802d03440d0764982d4010300801d031052400030a0000c0040707808003800003035644181420300305542045683c0000d180c502c900d501a1105240010310070f90800180445001440112024050140400c10800d54040c088442c0710f61002c034042a6500d40203143c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 564018920 1250 564017670 564017683
    0x60f0606050f0c0f03072d0c030b0702030c060f060414010b1e1b011b0e130c050d050f0702160b16022205220308040615080d05040509070809031b 64
    0x18580c080011840c050001c8600e00101036080f500104012031f00d044010b584040002400400c13040e060703102003001c510710b0b04480342c1c41401401a0b900d0110b0484039542010b508035030a0603003004603414820b40e410203100d4055400a40c800c1358070341e94180f50310b06849000b200701028012211100780c001e6044823000b0788008940b40420001d100122001c00d9000e00404c00007889c000380103502d6911024842c0e6900d404020700a4a4805180030161030500600750403040070080c400100f20341036039900140300d2a40b117980f21140841c0582010b20009080c60001003100c150010b44000a20109a0820489503221410101c020251060b072000c2810400451520f160b00c00407140c1d500e20340d50403500301c9445000b151008e500302051040003401e400d465010040c002545810018000842c0b99000442c40c0207034200c03400c00c0d95510388202c0d2400c81e81c105400c000410100e010855403d00c1d041142e003002d51341c109840180f400800c0180c1e07a003c0d1598440001404441402050b42d051124 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 564020170 1250 564018920 564018943
    0x2070f020618100306141e0103110f180a050102060405030a110c0402032e08030703120207170c0c01091d04020d060c020322080a03080a1512060f0606050f0c 69
    0x4500030150b8640f01800030122441445d540200307194010b406880c103e0780c00080c66101c0074180d450b00380d00c0f80044008010218550025820422a02240f241c0303001c09828a034602d208050224526802404064050350b4070a034190b50150052000191021065503100b518600e03001c3d034003803594084a441c048001c6000c940151000052240c408161080340558803500d103404400003000400c1220298041c0c401c2880f035070000e000c4280001d100312181303010110b03c8140035042154548901c03500c1c0034500540f80f401c0f40000354201401b07400744410000400e0909149004600e031107001da003400100703042484003641c0c00d80010110b40e02d0038444080b00d030b00310100300a00004580044d550368481401c1c800c071042200025221140700d141a001a100420050102d194072550103480d160801342c02400c480c0d4807101c48001010b010b44d00c00d00100b03014210440e8076011400c05408452800000daa2120304042003072000b00c1d006421100c54400903003045648060720021107040c509062035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 564021420 1250 564020170 564020179
    0x9050405070c0605060d0b1b0d0e0d0210090209060f030f010c200105100501180305060f0604051302101202161b0b0c19020f101205060402070f020618 66
    0x40c03201d959408030340d04050350b00c03d507010032840d103801c000c00c20100c40700140104103000840008072042c81403144400142ca50100c80350070316881c48a460107441200c0300c441d6850b03110042001d60181d0410078600c1c5240045010400341e0000d370049054440000c100c180100080b412158558900300806050400a20020131551a13080c0c4003c101320060520420325108090b03000042e480103110709401856541a581c203800d1030040107440040588900d8074010b0407407070001012800502880b8410641042a00054505001040b08aa03806400c8cc11181301800b00e02c1e0042c0c0342c214017042031000c10b003404c9202d40380122605020344140c0700345035000542e50010f007081101150041e0444e0740c0548642c5102601c802500c4c000c0e01074030f03041c2107469110b05403130040c404180c800026594006060100038000c1d10007c42c101d002911090b400184050207054010b40d031a00c40e007500454101c40c02d619280154440c022682c003040350192140500003004d40264200e11a030f00c0c0645009403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 564022670 1250 564021420 564021431
    0x313030e06160f0204110a230909010602070806071e0c0c2312030a1e12020307020d0207151205060402070501060303020609011401030305030c1308010204140f1905060a090504 77
    0x25143d0f54000c0d081c14200c2c0a142440c01a08811a40f44182c2d805140e15985400d020f0f110b4556800d2162604030710002ea00d40e00308010f800d50749425140d0707406060350780c00811207a403800c80d842c1c0c40c00c0001884c0d03400300b05044050030a9501001c000d400701c0306607443c02000018031428440040380461b40075a05920070840368641d0f4505c00d00580c0800315003218124503802150f01099100d05c50041c450317000444002421048076000503564000700400c1c03406021420f040200b0380d0403a0300a41c0c1c680050303804116800d0310661b042007000c018050071122509000d81c8072034080d008d500c528900340e48040e15500020100d171030719030540d1550303600f000084c0402c03503a90070060b4a451090301d1680c002d508081018a41c0070300000b1941c100c1e42d2581d28075140d03565007030118029810a044850f8564280c03600058403040034009032024100343c0307651402c020350103400c0104501c070740c815640c0510700748914098420fa800490f02c00302d038016640c065a030700c800c6604840b40720032a007103c1d900600d050b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 564023920 1250 564022670 564022673
    0xc030a060807121a0103050613060b090732040b160c1d1e0c07140601080706030f05061e010c06060909060c08040b070e030c21120313030e0616 63
    0x48141e0724044c0030b03480e032940446409580c5031a01c0030900000e012070f03200314045801214140465102c550081000151a6100c14000340e00640c05448920000c0c61260341c0d41d00030030351600645620030440b8a400c0f541c551844030240b860040b48038460000d50041000c1032410021001d1080744e030382c040e40c880340442d1126140d50704549031800f1071400c1c58074100000c4094110125556041904011810361035a44450403240c07580200000c40303c401c035240c441010f0742e9080105a0180612134050140320703050002c01030460351708099058050b4245802e010307a03500d03058030f0078540c021a419031000c107095680c0182d500000c0c03010014019440c0410000b000c0aa9a000c00c0100b0711414090000d003040040480780140d00f40c801902810300d550202e1501c6020f80d091100c800d03030250130b482a0b43c2040300010202030442e41001c180d01600c1040e03d8052100b80400c00c101440300e89500c2c11030919002c00521200d102c5d00080a0000e074000c64811581c8038425070320548601003c111048169 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 564025170 1250 564023920 564023939
    0x30e01180305030a090b12010b090a05100905010f020109020f09060a0b0c010b24180a12080c060a110a121b02010b09060a060e04020304111f110c090c030a060807 71
    0xc1c0c0f2504001682c0c0c5c0c240407840303602000031680b062403d100c0e2041c043c5d003041c0601031503611207031145600c0242c5520000e612344502c001d002c1c984800d9250500c1280c5800d0000d0b204000e900b14030001c5901d4580c5208c01642c0b07609075400c2d100d0007565610303510f9840d50007040d4141490b4100800b000008141440c4440d0150000501c0c071400743c5051041c0980c01e0f110300c02e8860315084c0504604000c0c1700c01d4074880c6189400401b00b040041103144000d944071004400300d0440c1c0000d4500800c00241a00304040c01c000c0107400c8a0420010001001400500c81460207251110003c002031201086400c41c0e007a004074001c007203400d0308400c5045120001900810078a003546005640f40c100189452414001c040116502925046040c1e168041000000d6100900407500d07403400c803c03d030307000303898141144030b24580184e00e540c0134520f50000a4008082c0030080e40700ca0780041c0b0060866251141c030b65800800401078203489841d2020b42034054002904205403a11410500007500040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 564026420 1250 564025170 564025177
    0x204020903010e1b01020a08030105010305040512180a08060702060c030406140f01030506160f0f05040f030b060913050316060b1504090b030c030d08070c0c030602090f04090c03030e0118030503 85
    0x1040413080c1000061407005a881d60406603014012907014801007250b9402074208990080c4180e041c1d45020150b2440980c036a00446411450810040b40e41031703d40c206108548080c1c81482c2c01071500d0310340820001e66895000348282c4003054040040340400405030865041000c1089401065142c105620382c00740c50240300603299407180c00041502c001218001607200c410766070755400b0500781d240302a505810090301881c00c00c0310030400080d0308100c080491001e14498484440f880c1482d40c2002604007029008001040400700280e0021750000211050012048420781203404682400310007054001512608008483c043c0d03c10306060600070825100c444004201c010b60a006045d030340d01c400900c1580542c001400160340d14007517100750b94010501d03e0090203010b041d568054189a260f8400c4450381d801003404425841c2002120707407242e0003503d0400030949075495012503600984000390610061415101d9264071804140e00401000801c0280c07150756450142c0c0e9a62 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 564027670 1250 564026420 564026443
    0x2070812130209010608070908060c07020a05060c06130204090605070804060c0e06161b030309060201060515070b04080c1b09010f03120f0306030c090e012d090204020903010e 77
    0x1000c20002980c0c21000980e00700941c0e00601207203240d03800c09600340e449180c09081d150a028007813100040420081101e18420031503e8202c03900e400582c810300c410114180c001612500b8203000c20320621100084256010410841c004160481030002c503004101100000d490b80381440d0420090981107101d4071f00807441440108030004e8611421244030109a08003030307102e40c0410440742c074110525440030419024500404c00c0e003c12044280313884001c0c0c0d00482c0494580f40081005a03028411200145400e4a0356240081c8800d03203140b26110305840104500c4101d0b0200301441914401e850380701c10800c1c02c80e42182605d03c0d000c8020340d01030280b103200da808080003142d060001410300080384c0d408031820903061f81d04082580c25003c2c00102030101a540c042c00000308202524010041c8001500011032820a20b00c0b00c1c00d40d85600742511410030414440b007110080c40c841980c0c100028000081d00c1269440090060b101d2180720070f515600b000a05224403002281c1c0782e1010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 564028776 1106 564027670 564027697
    0x12007020f04060f080607093b012d1a161719030b0f01030c030609020d0209030609010b0a03020915030106080f100608030a21020708 59
    0x455113079002000016681c1c5080181036000d01440d90400a645031160890341080c00b0b000c47c1452807000e041d03808041220a0b155100511071445941060803550301042d6550a031550b11180d40c1104021791f0040b400700c03441604c02102c03041d411140307124201c6075101c1c01e444441d0070b00c3e08116134440000041c1d4490100041e01800c8192500911401c000c0d241e1003a010944101a0049202418075141030014400d030742d207942030310a2801c4c09203004640404900c0d000c60140c410356004004450000c10303a40b52380b01ca40d4000e440210820740031107096640d2003000c5420b89440845090b00000004024005401c2400605030300c100c264282c1d2243c40c0c5c924000c40e00310b40c02680605c2c0326030020f00c02440303d114240051180142c02c150180000340c203014910b84c5a114200708803050251038041000b5200c40b4210902e01f040c0403031070441d00c4038020b0600c05c04030740c404003001111 = true := by decide +kernel

theorem cover : BRFrame.Cov 563848920 564028776 := by
  have h0 := BRFrame.cov_init 563848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 563848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 563848920 ≤ n) (h2 : n < 564028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
