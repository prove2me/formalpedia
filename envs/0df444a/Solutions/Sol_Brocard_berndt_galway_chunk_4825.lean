-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4825
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:51:36.050749+00:00
-- url     : https://prove2.me/submissions/9be683c0-0825-45fb-9278-b2fe81f8104b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 867625899 ≤ n < 867805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 867627149 1250 867625899 867625919
    0x60921120f14191d04360b072106030503090a0b03060102060103030f0c12050d060f182018100809100209010c080408070e09030c0312060d02190f 64
    0x469402a8040642520240e03800380c030840540403246200380d034000c42400c2c9658891044071000648200c800382200c041441008405218011414000000942c442d0100d81c048482540c4a2500d00702805880048418014116480c05c1c9c8440101c2c08e1180120400a011001d00802503096071021a16502c403140f407035031800211103181c0140e202c5030040011070721030700380c4110711030700340c204903000800586a00101c2c004120450011541c0002d00c500d001c403161141d40020852443c02141030360900841404942c0d24403281c000040c0c45100d8002c02080344a6070444514541c0d0003980d0710380680c40000b500c10b49584509103d50344150010042900550b01544600038000142c4002c03500c0e035900800a42260545604021603250900c1c0098084401800076045c110010441245421582588008020155042600140050001d0840010a44480b0746071001100843c2d40d666000c11024900b28201a40c4802c888202c400e4031480300390407405517500c1892103058144c54004485d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 867628399 1250 867627149 867627157
    0x20304030c0b09010f020d020d030b150c010903080a0b010804080901090b04142b060515030718051005101d0d0809030d03020f0f03040501060e0414070f060921120f14 73
    0x80252708045500e6140c64800e50100c462601b005010b00754500c1c0618403100c10b508594042c01c0c1c030742c0d901d100c070409054100b515143c4c4451814014000401d01034002000316402500041c039651011030f41030042d80c060f044800150180040b9151a02d640c2e41100c4030400320204000c2c0111103255412aa08280074845040c0810401c1505d1040c68981c1c0c4840c01048000c010318151b2000344007050003a90140300480080200c1d15125011704240903240d0101c0d60064441c0f00c2207500218100071645804240c18000310751800c0c070036560000038480c080c0c5100340304941d5502c08090206842040701c880041c5c1003c03041034003180e494244002080d0100d20480040d50040c01c0140308d8910f409546100842d8014460300000c14910380d00e030280103820400f0340e4200c40c1125a0341c0300088a081c2041003c000b0030203040110034561031320601a2029140f402480b404174400510503c800b02010b030b106500d154049404c552032418a0401403501c403100c440c4c50000b40b900304030b082c80c90b01804195 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 867629649 1250 867628399 867628423
    0x60405011d0901090b13031d0d0f03020a02040c0c120807120b01030e0102070305040312170705031807060503011d011a0c07091a0a0e071d01020304030c0b09010f02 72
    0x1001c035044440c480904603910050040040f9900d9000280004028060701e0340101202c20800009022900c2d000d0485003107441d1422124042c841240d946944003541e0413602600110381004101250608a0819001c640040d4000f41090101d454095002801c0c82049024400081c075115016100302c0308603c1c1030324514001500c0d82403564400c080c5a20071050204c05040005904080e54401070a9030001d000603004640042010028090710428103500e5010501d01585500c0c80c3d16403084ca081e070301500f0003003041004070001d040324604500700202000240304640d04265a0b080061030b5034000d00603c0110b00c280d002c100c403940f00c1401501c1c1690300c0c1100c1d0f000c00400320a030a5219401c2400300307010318421150000356064991081420807000e200c011311032003030780c4820b000a102042d030058038406da0040401440c03685c031028001e0340001c40d600c031035014154100100d2850043e50800f400784815600e0000d00192890003c001a0070f00382c0f146c002105010030143d071038411400340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 867630899 1250 867629649 867629669
    0x92101110a0e030c1e06130e041407030308011206060e1801150b09040e21090109060825050409020c1c111c0203190809210f03060d061b0806040501 65
    0x800c000c0c460100e03415a94500c006d0003840c141104460038070340300d032150fa12014880c424207060000340a2514500000180310702c2c01040198550390f40240150030500c603054000a04103e034000300115900400020500440007031444d08128042e841c004210100c034580301d6181189402c01c0c03900203d15101111500c95401c1d051561110511014020404000342c250050503214030008080b0001c00700c400b001501d04545400780040094400a0145c1102c01802a44000c01c0780d14070164401207491300e51310050020303622038080f040e10580a41d411609285001250350115000c1c00500c860320140b940c880c1c0b50a601280905440b248000400310a5070b4200712540e910800b880c0540c0401a0380e148112450f103020700d80c00030346c000006105140019200410f10030f00c2c0c0402c00c0422916201c141200c4051040e9008000c9a841010813066282e80007000240403030303440c00f01420001d81c1002c1c003400961070140e110000d0600c1c04110302c0100d28440c01080907810b0510a0605845c1c14801d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 867632149 1250 867630899 867630919
    0x70206271023090a06120c030b0a0b070f0c0b09040f02071703100e040b15010f0e011805041a1516060e0c210f0c06092101110a0e030c 59
    0x100404084030740b80200c80c00c0081003101d50469101e655844000340b0503a510010f0310704110f0168825240c03000009001c050810fa6510035030760b58011010100c03510070040d195240d03480e03c4c2c00014121a580c01500640500310009075648040c0001d1800e6034040380e0410481034041413038422400f030210083c1c40344900c880c0c20301140000e00021900424209650200320303590303520688529108640031114038a0440c14004103040000e00100d0060090a0021300b10400e543c000313044440c900901c904100e19211035105038102d03011107801801024206004022500b51450f0110200039411070190100040301c04034004048240d174031488038541046071403040c030385501d8050804425030640301d0003110718141c1c40e81d81e07040860f542c80400c2e02d0600c500c80300d5242d4842c02e000301c125207049960041f140100850f0341e01000c44002d800c040391040402190100780190641307400265191661030881c40d4041030340c03020081c011602d6190784034a4101030341c500b419100c1d22003004072504118059 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 867633399 1250 867632149 867632177
    0xb090d111f110408100207020f03150703020333011b08030604020a12020304030801090b0102030901020304260d0203030907060c110f0f0301061e0806160f050702062710 74
    0x60801c4654540b1461001c0c10709071100091428003050129154800b60f0015211085080a01e114000c20074100e0240006000c00c10460380751100080400d0704141d800000513501880e0304100d5a1140310501d0203c58484100d03a2008549051400941c08100404611032342c109000854954181e4420203035070454483d082444042d40085a40406001e071078543c18a4540880c4003442c4294041da45a034020352400000404462500d180b0074110b400402c008640e81e41c00000b01c1c4c0466401542e4490362804059502103a500350414031441030141e00c1c0850307105580000950f02500085055809282c1d8803042a2003040300244020083e41c040f1040f100c1314074003545e55810b0b13514040c29200304074101e02c0000b0308481c82078100d900110100000783c641e121814540da07000c1d00e0700100800d10b270b0506500e81d0f00f1464101d100041080010344403c0031044c030400644040550280c441500c40340100c030400000b000000409440e403100725601d8255160901c1e8050800c40703652a0154403800381 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 867634649 1250 867633399 867633401
    0x90903040b1909120308041a152404060203070c05010e012c1c050c18040b0403050408060c0d150627030c091e141302010c0b090d111f 59
    0xb10040b402d0021000c00004c83d801803040302e0f40c00a200e5600d20140d441d051505400e040c0600024200c04903010041211000b0354091064000404480c0b00f0500380d007200703220102d07407143c1e6149014040c01080002e681a0008041c022191288544502c55503c034001101c840b45a03640e01400942640904d00302c65021901007140910023144401120b611310000c2171140103c42204444c035180c9074242d13001e0040078050152881c600301d8a0484100b449200c2003201e101c050801303070155100701c020508141c0240100c4008200150a590880c075000d0102099500040c06140c8510f082000209a43e040d0031384450690303480d0b444051445c10107074040e03031102c0c4021303076054907058400382d011012401c0300101c1e00c000d0460400c04200c801c25400c942c0300503040c0e45001c10701c1a080c54000e0b2503030701101a090b54804058040c8400b000782900048400c0140d624010b0851401003081c001c20080110340900460060744903122190001802c1650302c8040ca010000140849086100500e00d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 867635899 1250 867634649 867634687
    0x504080d05250521011206020c0712060203150f0901060e210a02031911040f020f0a020d320d02040e01090605040f060e040605040203010e070b09090903040b 69
    0x40e40400180b06001209002ca400941003842d1001c01e0000c02c0640340d48034802c00702c078078504681c0c3e0400f541d940741524150321050803c3d0024500b03034000c40d040703519040401204e00100240300740340c4c5401c0c0c81e0781400002503100303441c0894061015010544175082c003650055440101a12a465030f030310304001142c411020200d8107511203007510800400100c13900c1e00c00c081d00a0103015244c003140314030406142c88011800884003041140d0368201060003041400d084201c1a280070a441a5260710038000344034100040d0880c1d080030650540d00c41c0e00040b0024408081c0e02d502d01540313185a40840c1e03400c5502002a51180510500c000460b14680501480d64403014050b05058075405c0802c40c00d90242c200619040c0d407840108682c0c6440d014000c186901c4107020010070b4100040c4500d4603c2c000e0001d0011070f102d03800300d400c6407030035401801da1411800130b07101c334907031215401c0740380b07074071141a00303105035a140d01140c0c6035180442254111500c40d8000351400c4020078442c500ae4170 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 867637149 1250 867635899 867635911
    0x80a0906180b01080d03111903020d180311010b0616020a05100221160b250507031404120b04140d27030308010b220602010e100504080d05 61
    0x1071078165014030084505084094148074507000803466040443e018a03012009458004040c1454051481c000d445030845d4500707540c10440c0c038108810040300b41c0c040d00c10305961003641131a00c420400000c0040c94242c058a110b41c2d201384c19071601e050058242d03003610001e5588036504120035032110121b4071103502e92a2010301030500c490340d00c0000824007000e07071010401682140c82182c1c0e00700c0e401c0e028201c10003560329504d8242104020700d250701d00c140d81c41c01000700a0390804600c03d840d0400c004070300401103280360750045d04403110040c1103400c00d81c0210042004100c1d21910601108161006e031003000d040d0040240c22620340211041010b030044d12110507036240b10048034001d210718841c00100d0744401c0d4110300c000c6002c2a100300959410056604003c00900020340c3c0126400d04682000c050170b62102c401c0325a2200b03c00d0b104940000104100d640001c0c103c3e01034000482c3e0f4810300d802d03648089164203451003620400c803002009030302d007042882c070400041e030b10030303034100d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 867638399 1250 867637149 867637151
    0x915090f2c27010e061e01080d020d050c0c0a150e0915060f251106180907020106091a090603060405060a18051f0608151801110a030f0606030507080a0906 68
    0xc4d003003c1445050240554403000c001d810080d80d000f41c0d0314255480c500400c400801440700400003079000f9254480b0b50056400c105000074a0305c0908420400381090350401080d06c2896a614100e40c41110b42d08080c4001040c0c410401014918102218911880a803102200d0714400e040c10010190f009084101036140b0a120061440e01d0110030741c01502214005105078034641d0402d42c0b07054000c6602c141c41904104201030405089151810000c4000e582c41c410030384801d001a40900206e8009054a51a220030341c252003807480740f03c2d4409007055442030070b02d031603003024187c450000310b902911980c0b200012481000745980700d480c00e102c4426080321421080e60f240303810310b440d1840000c3d2000d0211841142d0740c1c0d071889803000500c6c40000800001c449200768545550009000000b840c134050b0102c08403400a41010000c101e05076501c65480d0f6183c1d8000e001801c01080103018689000004101c0c00e00a01c241801040f03992183c004959900f6040e101500450408641c42 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 867639649 1250 867638399 867638411
    0x110a0c08160c0801050f06150a0e0a090f0b0a080a0c0e04020a170606090703050115080901021306020304080d0f0507021309080a0525030915090f2c2701 67
    0x800d440300b0b01140030340b1003c80045400c0c240410401c141c100b0241c0700c2c600c41c1004082140020000c0c9003145e0300c60090b03040a501c48050b04000a050381000c1d801703010340e1410900f8004101009502c8000c0d00001280c07400199a02c40c0c54482c0e6580c0482e400611441011200f4486500c2d048246a4001e20041049000766150800e01c00841410701d040e818039070060f010300c0001d02e0184001540010280b900300a1507142056406891f65040851001c1c0300c0e014001c500405000e40403241c54803140c11091030050703a9098000e5590b0b00501c1203d9180c02801e0040751407074818060754031568099900d060410120382c0801903001b0060710820011595802c0040005500c3c1001d01403250781d507142e240c0c031403450068110300c2e02c0d03042e854908200c500c012400c00180c0c02462364002e99242e011081070b06d805291058480d40065001042040c1e540000001c09585850701b456007425540380031004240300041850840a0943d152501c00701c2c1c3e0000ea100c4150407900e00003845003400000f00760 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 867640899 1250 867639649 867639653
    0x910030c0e060a0621020f0d0b0906030304170a0609030215181e01140a0f0f33170607120b090402010e060f0409090c05010819051027110a0c0816 64
    0x807681f00080480c110034010030840035031001c030310440340450415a000c0c2601d01c0c0a80c006605ca119501616880001e0145c001c4c645400800c01800250307406482040600c92a050196450a0f103c030503515507010000015a0b1448080414000451840080c01c003015464521070400d206811440c415640e10b82d00c4411035005042c1e12230085204010029074402e4107170000060340c410246a07511103081900c002d2140041c400000002c80c01c241d2500800d00c48c801e11a4490825030703111310030fa0920242c00864504010602c64018806a01c3e0b83c0c1707101515120483c242d510807000c4980c4583c040b000103000d9401041c202c43c1c0003c1c02070026160000d841310b004c00c1d580080e000850a00e035600d02c108200300ca22010007015042c2402e00356810310b8030542d03500412000444d801d20980c0c40d036003c44c01e668100784504019203030a4000c00c04c804460314030a40c0c2611180c1405100c40e00307013600d40116100344011251000440c4d510400d01c1c12554403400507076408401c0302d0410350b00d220381c8200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 867642149 1250 867640899 867640901
    0x1506010509090f15061e0f0403050615040f0504021e0310020d0e0d030204050607080d0b04060b1801141b0c0a060203071b051e0109050910030c0e060a0621 68
    0x100c2490340c2a000d05260900001c070804c41c4000003030b040c0c003d02c0104041c071203e00910200c030044140c15002d29913039003006080d0310154052980018600d214910620000d01f401d0f800f84d0509a90960f01008101c42d1240c40d801612800d0f02e010b500480c09036042e44001003002095164104007a0440b0a910400c4003000d040342d03c0341d0b011801c929a078a062a05c0c4c0403081c040035443c044545019402d2a060800040c21741c4114840241b01010002d0074440d0381c0420380104a600400410401265603903d050070709541c40943d17000c40b00c0300341401c40403066018405480b520321410317041900f0010503131030852040c00c0c9000c403803034144181e1035520718031703641c01844c117014000650281d07403620114a0300031010540343c4d0040501010202e010300150302c0d00d141845242c2040e17001c92141031941c40060361030105640040750070140d02c03001c10054211782c041c118216403140c01456080c642c1c805140e001400169400759101c07044c800e041001e140300721b00c191540304c0c41324114003000f4225000c41c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 867643399 1250 867642149 867642151
    0x60a05091807020f0c0a03030e0d050a02030105070504031103120d0f090615150908061605070f030801050f0319030c24140606090d1205130e0f18150601050909 70
    0x20b006030b005010708804114213000d0300030380c41c070191903441c1024216640902180c0e007840c02d42c0e0195450350144070901c007041000b0a6469005002000f650800e0b600003032103544540003e032100102d0b5495815141400200f50224130032806101b030500342504210070207032401150216043d41c031a884400803c40910501d444e20748405071030390155143c0040c00a54041c0d001c9100240400c01104003d810004034030140e01000114807140c41e540e40b580d05940340d02880201624100062401904240c1c00c48a05410b85008490b13600c21800410100740c1c0d1001c03030040d00c8201500403881c0d98000f13405a00d03001160340c4201d020480d000207800c1d008040c1e0a4803210803100940b03401320142020340070303e180f40d081401641c100c2d01d050568404500814003541c00188070154071802e6400062040302901d80341203507510702da100c0d5a034841c04801d50440070303180789001e42001e5021901640241404c070441e528400090102d02d02480c02c10107407050700403c1c4c07905002c0204045016952050889 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 867644649 1250 867643399 867643411
    0x10080a0b130e0c090c0c0601060c0212010216112710080f0c0a0e06030309120309041d0f030a080a150512010c080906190b191502060a0b060a050918 65
    0x20240b0402c80c2d0b0030403180c10700107003117003016040c200807030843c1d80004225181555014209204801c040c1e00c0400d0b40950131141c110750552010441184200310081c0000b101030140b641802000c0d40d84042000e03c621215403a0324035040b4004003410750007200480742d44448448082c0e1070550744c1d10152414800c10780701081c5a0b42010720041038518149103000c000c1c240e900c4284080e482c000000c2541d91003004586031007110086110b072958082081100c0c503404024109010b401034800641501d5944503001720018002c450424031514000030a4424810380d50b968034440f42c99034000d40008002c81981407604108030035000c2169110f15514540d007210340400020129011750004115010141003082e4981192050000305c00d585415103040e817207008400120405500e0005000e0701410302d00c0210104ac444000071113a001107810f94a1440640075100340d680d4111002c800c440c458000154420814410545010b10400c0078142c80407001e4900290890000401d5461420403202 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 867645899 1250 867644649 867644653
    0x8010503070b0912120f030f0f0601270521100c0206010315090c0605190207032f03070b070312020306011e12090c080d11030d20040608100510080a0b130e 68
    0x280f0011032135007064560b101c607840d8516402412b20400003441008002c0d0040c00712104a0010040025207d03c40d60007000300500001c0e41d501021a442c0c03112800b50070000d2540100107007038100904030b0142c4455400282e001d41866820742c1d48425400c00d1803000c2014803581c851900000a07002120940980303299224076413101e281c0c40507800341c8000c10000d001150440c08007000021409501c2e2540050070000c4e8421010032019044d02411300303000b0b040d50511504000245011440c40242001d5000b0365030300c551400c44200318400c0e44400d607010f80c00580c480300d45030350003000d01d1050f005080c0c2e81d05d04100100c141800c0342080c1c50340254144d0b44204282d40400103032200700100303a440851800d03c050768040c0c010200707469018185400c04020745415180c80240440b04000d071102c1005019a40c8407a00c48400070300f007840071503400d0000c0404110103d010325142c160010040b00e50380c4c80d01019510b41c2080800b800e42d1980b4150400307040718200200c0c075007034051101c0e61070f01c4d000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 867647149 1250 867645899 867645901
    0x203041d0612010209030c090603010e0a080a020d30021b01060e0a1a0d030905030a0606031a0f04030f110712060c080c030c07110a03050a0308010503070b0912120f03 73
    0x104000884482e03400001c0ea8410020014503071804281d07201510000c48400d007507561483d0120b8003500360380c04c8248060040c03000703090400c94240043d1031501020b500719942420310f40270980ea01b0024030351042144442070344e400e81c411820350140094500240d405402d2280038191a144020040311565840c1d460710410300ca107925903d4500e601424081e414007040560301c7e402c242c518078081c1c800c0e01070055610480706250190b10759030700a16015045403c21a08d90502038018441400101c030214501c951103520704004240c114000c031917030100000f07240c4481c0d4060303410313018040690003444481c01c031240f0400000e00000005003000703154060002e00518281c411660200d542c3d0f800d001040301401256020345041d250321200503854a41d0394180c0e820702040141c01c40480a500c0107003041d0210804ca40072612801e510710944071401c4030790b03d42c010552900d070345010b00c0368034450911004805242c024404181d09811401795420383d8801095044150701500c5000c0305048004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 867648399 1250 867647149 867647161
    0x130e0309041416030605100323040c030c0e06010813141002070303060b0a230403080d0b0420031302010e1908060703021e030619091b080f0402100203041d 68
    0x56183c5020560707074034003045424180800103400c000c065903200c08040d640d441210341c4070300204c01d0403c40150445038942c42c0c0b6092400200748001c5000844200091300c400050564521480f140124016190340314075940b5035180003509486000183d0300071840300100740303002900b4026825503500000000da078032491418054281c41072603000f00700d480420000c0310035103a80080d1080303030030060807034400032818000d4001d04280074941000d004110f00041e1002e690728554048a0040070a03141800f51150f003618080704840c01141410a07a03800b0400a0f1b01100d0400c21400f620b032050501c541c404008801040103e0001001002c2c0d4004c450014040c5180420041b94801c40c985015898140c8030504000703921a2000400928030020000c00c500da600d8440b9054054800780e4690180c1e80e8981481c1c1c040c00b516450084c4910301c0030076512041e8441c01c0d51a110703410201038003100b52113035800e101101a50010100441c00184404070b04100f80900c0d4600464150701501c01c036081c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 867649649 1250 867648399 867648421
    0x9060f0d1d1603080f03101802180d0f08030a060806040b100f080d03020a030b060a0816090803070b13080a081506030f0a2c160b0702130e03090414 65
    0x2e01480401d00070322550410010303c04c80101d80c420360a00d03c500761aa165003480d80c188503c90b400061169220b1010045010740d580d010300070804458088180c02c1711a1014042c0d248104040a0200c030072142010b00800e0b0340b83c000356006100d40b9030000d0401e5a03550320500740601a60101c0744a0000014403000501c0081c0390006410009001c990181c03800400503904e01d090513a0900345078011400440a5001e40e120012660010304401d50703070a0403003001003005800301c1d005031103980e903c043d00016900c00c0d0b250100b82c4490b24011071924447e900d80c0b000d0300d80010312419407403140700039410000781444050b01d0701e00007507114241c3c0750904280b1800d9034500000c5c454066142030040220ba518031710041504000c00d5040018000c03040e00380786038000300921401610108656048161283c001804042c07034076610280082c40c0d48a86650001c3d10407600c01940c4074000c0c40c00003448864541c0001c0d8160403880c03c5030f240c02080c80100d8140e4107260401030b03c152071401001142900c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 867650899 1250 867649649 867649663
    0x204050603010209060a080402041b0f090602030a0c03080a23040b0112110f01020a02091005090105030109030c02060a180f08010c030606080c0a0504030b131e030509060f0d1d 77
    0x110000e5081131030142c04201c540c00341603451410400c9620215007591074230f620040b05080c50300b0340408821080140541030b03000c06085d07980001ca044a0000f900c500c08800c0d81e540105654400b91351640c035403000c607513012001d8280c81c00c095449582000230441c024000901c0ca042c44180700b65480d05091591480030142d00070b411803120411403800154007110710042241e41110146841248500101c2c503003540200020f400c40d50402c148840b10902544590844004175562049aa2104181400d807000d02d94001d0100d0300d8250740c0401403600002510b880ca84903d040e00c0e00c035220101490034000750b607010101440c030f00001401950b000f170040009007005428288452860448020701401e001844060030b1280441e04800880c441c5c81101c0c000d542140350f80d01503040003d541400d903030450104071205000c0c0070303084c1c400300e01e20561504c1d11605512010308000b0714005004c910b070f01445803511003110170001200700d030354944212119940c180e0507280c8c40a8110b600700d450b280c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 867652149 1250 867650899 867650911
    0xf030c170309060316020f0f07080c061e1b010906140109020711040e030d020c0706110d05030105100903060f09060501080c0906120313080f0d030204150e03190f020405 74
    0x1040142c4441c94564204032504011000d100866414410300b00b2400c00541400031011805114803015000f4000a40142070390004000d40e603c004a00381082524401c41c0c15140b000c03088184000340404064001c2c01ba82947d000300060b16581200c545421034040300401c4801c99a50502080c00345103805002e40900741c412411882d128040c0c4440310030030b4254940350700c02c50b01c45800b0300403290705006507460f41c109480155141c6541000c10703600d502250090a0008091030406444c4001c00100f011000d00c041e1038292440e404d190a0107001b0702e9403100c0800b8400b43d0303200000014a01d100b0b151040d282c80071700240c0307a02079280070421ba800603880142d0a40c404020060580d0f90500300f2504800304450002c001203003201414198020440308a620110f80e080c005094800440d40c030001820700030980b981d50380140d0781542280254010200f4000c201480c00350700c2409042071921111000742169074a01c2401e22020320701a280364111204046d01e400c0780c0440c24039020345c5400c030b5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 867653399 1250 867652149 867652153
    0xf0405061605070b062704210801030308060d0f050f160b0405010302162405060d030c020f0409050304080d021209180a0609110c150f011a040f030c17 66
    0x3a41c0514014041c0c00b800d5000780c4241081404582580e4411400e41c9101d8011082c001d0303403044900422668140840b4140c0341d078080380310190f042403004400d02200d50525200d03d103050f405e60700c04071403070329004040c542c01540d007212510208034900f408030f40307040c402c42c0200403c10900304154200714286c0310048050b0910071050010381c034004240d50580e40f080c81c00507100d048820241600701e140d60809004a4242c2d6a80102201c694180d680340f540350220500181e1030b103006000d42c04481c60320160004010011540c01171814181011090b0401040418840120707285e203411540203500c04807007988143e131103a1800342c0622105c502c0d8104c4400460904c070041c00840c121040100303907034401c5503040000071084101035016001401c1c2c1840e0400c2100c160490004080c0d00203840c402c654403d101000025500d2510303003522589101070b81c0d07103c603440c00d034000c0e40310a4407a410740c0e070841d002d12003c128003040305501c100840c003440d070ba0040b82c5d00d881800d00d521075601901601c03603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 867654649 1250 867653399 867653431
    0x1d04060209031f0e0f030a031512060b15090307050d06090b07030c1818020c190f020f0603040c180e010e0a021f091e03021e030606100210090203070503060f040506 72
    0x51031010041c0c99030441c1e48e08010034602410300e15030104903115003100740414000507903102803143c1079001c06000c0c0700039030310003e809032110b468590a001368880c1c030f540355000a81c00d0000341041e00100c64098410903004c41e0b8440305036102d40b100303002211141c00003550790703000e614607590003001501c0410b001030742c0502c00c41c00c26480c4081101d5440541402ca1740000301003ea003c001c00446e809003181d100b0b071a0034001c0c01e1801d1100c01c031110b80164452b403001071880d0802e2610b0001c80e0700481c0d01c5003503a000309240080314100e0004041881d15210759544003445a03810a005800641d0803103009011582c0ba50700c10060180502c42e0710f00703449402c1906403082150003030a4441510103903508040843c5200d0381282001034581c0000390400800c0000806c00910480203802c014800c500303482e6160750304c07030070b01c8542c1c10034208200040e40090101007451005520000c4c0150014041d108000c0d00e40c00072078546442070703c4940314803050b4402c101c180882402450740090601001c1040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 867655899 1250 867654649 867654673
    0xf0d02010509100c020d03080912041508100504020c0f010f0e12131805070e0103110d090213050906150d0309230405070306030506101d04060209031f0e 67
    0xd000315070019004240000c0380025043c000d84513200031550041142c4420446464010925142600c2c00501c1c1c2c072400802828054403001514140e0741b1740f03068894441c40400c030441c1d440c0006041440040300810380407401d43c403980002d24001c40000020140344000203041c0d401c4481d00011890350914140c1e424041c5103002c1a503020058030403030801e403510351540e06102e0480c4103131310000710030301031483d03c203192691608402d06c0345103140ca82418200500700150140d9070034080d0880e503000200050050f44800b540098185400070b000303050150b113140740d180c1c200c9009036810350041d40248200300c803580110001420700001914601040402550b01505c0c24016000d190104a200e415105510078001a0b102c00c1e040300034014040c9003880342001d4000d02140c042901c0c4c80c02040001040b110948520008654100d94844078007040101c4080311103a0260044410a40070000f120745690b04105a194170501130040349103481a0141420480c2c8502c0607007800d942000d00c04800c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 867657149 1250 867655899 867655907
    0xc0d0e1203030720010f0b0310060f171212010e010f0501020601091820031e0604020f0d0803070512011d07030e0c0306010306060f0b07050c0609040b1e0f0d0201 71
    0x60410352a0130720b4420451003c180821050754144041901d40c0380019543e802e041ca500b000c2c0b800d02007a011303100c90b00240b0f001d0300300740c03840c0303002d0644240c0c0d042c5030411418106420707583c002c00d01c084c1606c203d60080e0710720f0b50040c0e0110450b00f91000c0350800500c008140e1901c0940105030ba851006099490140040d4603204144184c0d0300c0540c2e24801004100202d103a200d1005a00005410006400781090203003a00b07540001c40c0284a0300c44a52f49a0f0028600c0c80800320003a40146000ea44590030006403c0072441520f400c11290078850001911850145008803642c2e00c3d11600c0c3d041f40301d01801d6a070016440521030f0058458149220000c02483c190000210716011a52822848540c0d00d40100e5082550301842080000000c1c081250301c050295940e000c07042250075555941c05145014421010f01240c00c40e01800e001480c2400081c403200902400116080c880e43d00040d040000c650744607600b440210b1200070007403030b00b4422060000811aa00c0c0540319040d00000c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 867658399 1250 867657149 867657151
    0x1021e120306060903161401020f1e03071e1208070507023a0b09010504030210200313020306061012020d1d1014010501081f0b0c0d0e120303 62
    0x1032500010201c2e80c50384502c001c45940702000340884403096054074841c3d100030344512680328050203400704403039a5880400e601000d10101802480b030305103040a0b00c80607041911140c191844204842c50002d0940344c00802407095018001c40c02444900b40f10038855424a00e01040005160070851035603041001e0301c4440782c06441c0700301918000c0d02482c0442c40b1500940035102c1d20007807501c1c021a0460051690184110440c003015280c0341081401c4c2c4c1c60954008026030803054a541e14824a0f9001d9004906441c0641d03449424010004510342d00c00e40d4445d684461226a01d020341c1002c00016811600590310040f0041c500d290040a0b190807903120349030b01d500040d004034199021303046048140b0103180644080392142881d183d40e8220854a128024100000e0500310402500c1ea14100c80042c0c50b481c203641c0d1030310312421101e5501d200d500002c2d20480b40c08103e042c6000c018120400c0401c00500200e5800d400241c0b004002c251081d00c1425100c0c80d098000d10302005403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 867659649 1250 867658399 867658423
    0x30c24140a0905030f0307150b03030f0304030e0904080d140c040b0d0e071403060a1a010e03150a1d03180f0d06020310090606020607020d080705040509090c01021e 72
    0x4181c07101a440000c80d1442c0550340401c1e4588a02040c28200840101c01050010302c0f072145055070b15907202c55501596400c101e0750354903400c188002d043c4407107003200450b071040c1300386007100300203501d480002c80140f026075090f0748a0070f01003124800d00381d05104182c80d44080700482c1080b8075200001c02c20038803075030003060031209000c54424480180d9400408032100800244e8035001e442d81d120141090301644454420300c11500800d0945c5020710580c22051750390a40314280345004030041d90b040d01c0690742250588600000038011181e00b8104d0343c0241d100e00e8000c207462102d0581218004600d101c20b1401e9001000354001c06046828030543c41c0a00342e4000d0801484200003a03175021103990007524031800042000040c450a00140d020f0311201d10081180c15240c2c4400c0382d460300704641c5080564040c0d13408580a5000c0c00d5a20b038802450300d00360f45029241d5002c1003619001f03441c0c1920f26440082ea180d0250f8052080707604a51140c1c4201b04452104803201d070b40d0f003d061360a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 867660899 1250 867659649 867659687
    0x3170c0a170f01051012020f03040228050618040e0c10031a0d05010605062209060e0a0e1c0c110f060d1e020a08040605071d01031e06030c24 62
    0x3c11446a40610f086c0000b480003894215111088001940010b0303008030b42c1280301d4202c3d60300f10340c400c5007041d2103400350801c1500c4940f004c90400d02401180d6024689807400341c0110b040c07a80c020741d554002c112020190001130301c0c128002c0000e200440d407030013007030105050410760100c1034140821402001032800b110340300c400e0400c60500ba030040c049038110340c0d040342000507501d680c0180034003003800b13655505001003032070ba43d55180c80007150424000c0740c0030352440e00045004003049812a0602891010954200c6c0043e11000030f4a4100c2e036280c0c20224070300200541c00c5c00078048081c4c88040f41501c02620002034a00011010311071442040006a500d0710340210b240100310201e5a0303d48018003c5640b005c0f03002d80a012200300b120102d800905001c00280a80d00c503400c1c1c0d0240703402c41c65031941048a0100190094106000c14400d00a41a0402c403036004040c06217500440c00b403c07032500707650f040c250030464000110350308018003000350400e0310403c0d5101540e0101200301d03080c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 867662149 1250 867660899 867660919
    0xd0504020a030204110717160206090a09050a0b03121e0a0c0b180d020a0c0501030c170a0c090e04150b01120509010534050703170c0a170f0105 63
    0x2000a4400080303070000ba4000e860320885e0a540b0000c18014141c1a02500f06000c00705040506810302d4485d41c15108165400524070a0060910601509500d1340040200042c1ea45035903400d012100c0c101c03461088161540d201413618201804014403001000c2002454082a50885e000c0c01c65007030f554056080c0c0c000ba03074000c950f02c110381051240b1f030301007040c1110b414100d052036000c02058034840c1e2075000d204200340c11140005014085d0603800020358201c02e00d004019001480407046503024408503001c0b00ba04410ba040b280c3d07105680030100042d0091420000800c03944603504007005a03456601403101080000c0b440c00d1070a0001c0d08046051552480101e61580f9200e8a0803541030812003400303100c041c1900890320515102c1100304640e00392001495400743c0c0c00c45801c1c3d5441d411012401007a104100a100300c1d402814101c0e05085807d801100001c0110358402200102107400c0100551200440ca03c10400f40c40091040c00d2005504040140c1840340705e110703082e824 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 867663399 1250 867662149 867662153
    0x15050408150402061608092b0201120632061c022503030902041b200c100203041404020711211501030b09060103080313020118091d060105060d0504 65
    0x80c0845083c45e0880451680034519490002516008000c070300d0b00c22544843c100350125061172154800c031815602130801243c1e25001540d800d980d05c0c070b01e2a400313a00d811b40842c048000d10792034078801c2c01c050b1140058100400c08440c041c4c10755154684200c608010600448558090303140402c0305800700107980341c0f403141000c0a903084980700b240c40051003020784401e054041d0f2210a001e0300a44090112034400c100ca43c2c202d4054540c2d4101003498411b80704130101202c40141b60302c0c01c0350b10803689010480c1c03000a6070840704040034001640001404d104240c801c550182c01c1030003c0d141942031083c1c0303a842c5c40021818004890040e503061080e00b59598100604400702070300c0400b80ea00c000d000d1103692041c64030900007035503c40001c00c080f4460740c10002e07801b8122500403408a0031341d01c4400d5200c618400b081002d1b41007066080c1c50422034885105071200429000c800010104128194007058485030031601005803c914010406a1511011030300d901040f00c41c0020140d99074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 867664649 1250 867663399 867663409
    0x70b0903100c050d1a0a0e130f0203011503080a030b041118030709060f0305061305030307211e180201021b010306080601060807120b01090b0726030115050408150402 73
    0x82e034280142d00b801c10f035615454505100b8003c1c0350450943e11b20010395103498407956200c0058a40c030400360200b500d06808035a11707118203440030f48000e0010031600400d074030400715100d1301d420a850845000541c99080c0340c16110f04130016600340d4003800401484060134a20380a02902d0a0312000b1a03044288541d6040c800400070300780c6680104001c41e00c1e807012200b01005800100d0b1503105000109142d020240f4a840f082c9500400840c03030359450b55003c56441d150084110a20180b00ca0405000300e01c1e030140741c1d07030b02602a0500210030045400541680c0c02c1c0c3d0744040c3c3c6601030100441c00350b40e021564403000d4041c144c02a6000c0e4604004030000c00d002c2d0300001480c05498008500d00e9071240070640111115603580445210a02620f802c407008500858041000c40b1410001c483c030a41c00b41000728010310841d000b0340c2c0041045510001c81c1d5200b00c10182000006106513071a0740c150f10703100d61403031402c81d00705170811940030f582c3d910701100800b0454507417001804640e58 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 867665899 1250 867664649 867664657
    0x90a06080a23101b0305060607110604081c1706100e01092c01170d20030c06191401050d06061a040504050c0f0702040c02190302070503070b0903100c05 67
    0x110b18111042003d40720001402000c0d13070354050110207000c10201030040d202e8000c60703018580044c9410b107406859038507040d44580c0300b0900790704150140b2000031003d4080c8030f218800304490f0000300f50a0348031540109000109240344002410f01e10521000303482c0d1702101071143c881810182c40000c690401a203028515a00c00b002800d04505210300761078028000f20b1000074481d500b0116a6291000e07200c80c8420000c00d00984c0c1d1200c8191182039229031154202c20489400f40c00141503540c00c100d0465124019282807944800c1c01e000d505282c10000081c0c090318882d0030422000900120500d500d81071184034450441010403000340901540004c0051201d281c0306440f60280d02240c050b41c0d0040d1050a1080d450700e8006041a440c01c3c0840b503102110310040d030700d0070000354200710052080360f8004003184500391144644401c00f41c0700c0a406e5000343c004026141c40c081c00c16190115981260441d44805d00441d1169100002c0b1595581f418200110302d606c503030b46044840f801 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 867667149 1250 867665899 867665963
    0x1b2102192d12031d12150c090a060e120123090304050d060515030303090c0f120d05070f0605010608041e02011d030723090a06080a 58
    0x510006039401030036400400740e070541c400c84845103210311000307075408800b4030610000b00c00d50a04040003901c07540540c5419440c103915000c0c005800008100081407060722100c0c55400040c10040101100182c1c1d9071081c4d43d1005649060502d0011030318440c5544a01c0d1b09020003641100c134259541402d0060520203c1c008114141880c0000c201d8144034030341c0488048086004100320741c6e008811501551009000240101038681c3c50344000c1c40001c10814410060700d19284d00c0d41e800384002c41c0581b0b0544018602d0240e02000c101c500c2c02c0744070200c0d200e80040040365185100c08502082608c54070304015480e2821800d01741c104890841c0300400ea207285c08004200250080703001c5020318012085181c00801c880da5480c01c03a4915440640400c4043c5400e80c40c41d1910b09424496030805019500340603030318084203840341c03a104551181200785000940050a1050344190f011069507028407089240010080d11011a5480075001911804041600d201d80c0c00c64180800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 867668399 1250 867667149 867667189
    0xa05120c04020d060509070504030203070e0c1b0c030705040204050d080a110709050411030a0309150c060608060117072904031e0510060b0301300f1b2102 68
    0x2180080b074400003890a4017034a842200000042040d0501c502c00b503400b600c0d0f01070b0050010a0a143c1000100c40c8018031030890150200010030381000f484928010400f0f83c68010503100d0040020141021402c0d080240100d00c14001003041d5524080e14002a0b50482607555850401240c110744a08040c0440ea0035481084000646521142c0c44540700b85d00400d0030003610650710b803c16407a880c800c240a400910051018441014242400f08640483c0d0030849480070660f80c64038143c0d0b0701c1b680076003026080300004200c08103611030b4254201905c1e0024110389810004100d005850030aa402000d650310303880122820582d408440c003564100e5069000700000c128888940d0400c400308031100d010f41140014444210700940e010b9419005050f411a0f00780340d201ca0b10b6000d21107038100e040d100e1211901c1611110302100404901a2950b0341c0746543e142403000c00303a140c00450f45511008090704000792100180c032082c00c2500300f1072880302440c82d80002481d6580003513000c0200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 867669649 1250 867668399 867668407
    0x3211a121501030f120311070212071703030f01060c05030d1503080705010c0e0402031308030901110a090303180b0301030303021303292a0c0106080319021009020a05120c0402 77
    0x70111120039512442d114100074000011710444c21001d1b2410b000b56100384110500002c0014944100c10800d10b0f80ea003000c64011075030301c21003803441005010110116410000900800080c940760183c05800c1034206117061a00b56956603a8900c5070310720170505103503214151400c0300b445074503200c0110342100300e06844132081c0c245503000700409441040442d8440c803818031f141c10a402580e1055241c03854103c04410a80c4900416600007803076038045550b1010002c0c6450140d6000d070110907141e136100780100d4114903014000180c0f0400701b0800540b01c0310100900f82100003180e055a61501c1c002d138880611180768132036214030780c200403c0c40c0e0700c01c00101038150408420b0300c841107000e100d00c000394a0345101d03110542071810b40d00841c54918090058000f02000040c1410420400002507a81e501c2a109056420080b86c0d02441c041001440b078485504102c0c640c02c282000c0800c00001c842940060801a401c0c841c8030300400c01079980c0320010109002d81040c996002d0403e55035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 867670899 1250 867669649 867669653
    0xa05031810090c180b0a120203010f1802180906130320060a0f020403050c060c150106021005010819060f110403081306050f0909041e03211a12150103 66
    0xb408000d0046201007030658400c414684d0704c170f00440d1032122020f814240490f08010400d6488030a000c0d040e030f0150740302c100c2c04141551910511504c4d0300e00c02c01203500010720384100308030003810b0040310507410806818042ca8000c007042a43d0072030b00928010480454900c0d05450444d80b003860f0f0300303640ca00840400c640900202c1c1c202d114145a540070000100e02106e4802280282d000c041c003180c0c480c4620b4109410850000e14449601e58111440f8000001000210b030700240c00040058001180800d4103001c00d01510b80502100405451070340314810545c04203021988001e000f050712000d00e140408440d512121100a03010011035035551030381030103c482d40c01030b030740c1c00405001d401e800141c0910900607141504900c502e285d280c0480f0104200301c08c80007400685a50340f603055007283d40421020062036043c401d8031030140c42f090351020501250b048050702040103042101c01d014695103a0f40310070303000c8811235011000d00c030030030710241c41c107015804040c844100d18800441 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 867672149 1250 867670899 867670913
    0x307060c0201050c1804020d060b070c0828021521100f03020d030309020316030b16031506030504110307080a0b0a02040605040b090f100f140a0503181009 68
    0x4840c64550024012a154903511108500c6011080780800000394240e030020302d4590001c09048010300e8001c030300c180d16203002c50990b5115a004072000011240c1c20445240103000241c1e4200f40d1a24001072580e40008045a544034034900a214007200e80c40041d0b00780c0c0e00c2c0156050301c060004261495810200d407140e860500b9202288452400c0700b0007d00c80c0781d210400b4055a602400f140b041039110759054001d000b041c1c008a034140a00f081b011082c049200d03030500150700500000b4400d09004a80301e007003a1a0140241c02c042c1400e09012050360592481421241a803800080a5495013001ca400050700c07401c446d8075000300301c40080c800e0741c006086501d046c0903103c840d16503180d0208000c200e201350302c40c410100700c003488200301014140015080d410b20141180c400c1100c03440000d038000103c4180303400490b02c078201e10100076a121888400781c0b0f02a1441901e4264a02c2c4080d185010050044044043c040c0303080074150342c144030250301184004010703c000207507450300303007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 867673399 1250 867672149 867672161
    0x6030a1b020d11060103080910140f0a030f11030c07060b03060c070c0f060c11040e1f0b04140408130f06020714091306050c04050d060606031b0801090b0a0305030706 73
    0xc80011980a2001490f09002c0b030000d04a950200103030349403403070507010701c82c0a50543d5520000d101300210301c03045605501000b480520040c0c0442a030300c40d10300c2c20140443d0365885000b01d00d80c0c03800c4454031038403200c041100d40282d00e18100544401d0f841c9400d4014101110505803d40200b0080c0480324080402400007140f14105400f500c1d0b0b119428025810414410180083d5040061b500071858006440118100180000c030b101014608081c2c5803000720031100c0c00e000c801034420081200c1c20b1103803c40c0c410003160280300a45a01a082c04025009003010780501000034504d0b01c40ca0503d0b00080c01841c2c1c00071000200c1d03981d01c03400f80d01c82040344940030f490810800f81072101d25216400620a01c1001c8079055408895101c071001458001c020241042e410080032441d40d80c0e03517020383e580c0c45c030074003002c1105410880000d060360b11401c0c540580000014505640c0c0ba007180006040d50b000c490f0001c0c0a51058000546800c0b443d0300151041c00000742c03400c01e202068100c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 867674649 1250 867673399 867673423
    0x150e130e06011a271216030b251e09030b04140c1509100e1012020412081308060f13050c0409060b0a051c15090602120106020c041a06030a1b02 63
    0x201150201112491b41c07610400361100c842d0225009080c40026010f42d041600408860182c80c21a150b8860440206609180300c80c00315a112a4041071540c200120b4069a82c451601c0041149107a5413441c01c0107001e04010550b05040140c0e204035107041241d032042000090101c0c2404080145088640c1d00180010703001c0e111b4a00200c0d1081d0060040b4190b0310300c00b030040c107403043c00d2050446000c3d81701103500100300d03002c100c000b42e01101000d110400c68041c000490762404400e00030a0b05109951100703443ea044102002080d001d0011005c0c1d100c41160041e202202c05031408030300741b030080070300c2c59403042c0781000c2d000c00d1000980c0580100310301900c0b80b402c4692650100400e00d680300001c44039420780c214180f00002d007041100c03580c4080118001c10812207a580d5601030782c200c2d420564980116000401c082a41009116060b18060390200040c0c440081c5d0175250380448424a402144004081449a4040e40c068001601640b030030172940a0354050080d1206410510 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 867675899 1250 867674649 867674659
    0x30f160206090a030b24010503070c03090816060201052203050a02030909040602030105040b030c090a18050a030f14030408040b0711120f0f0f15060604150e130e06011a27 75
    0x380500d1052410202c901b0205071682070460360740c003c040790ba01c0003140c1c0032020861403d03400148044108403e04e0302d4442d4082c0c2e190b8003400c00c900207007150303001485015100e10f44038403031944600301100c1010064241c505a55100c48a000903031440c0302e0b103014503030000c4451082005104041e03002d107040c0ca00883d4103200c00481c1c80201030fa900703413403010240d200c00e020340070403622202588503541c001c0b54485076802c1641c0545445042005185d070680104d221481c0c00300944c0c0d80406540c2104144120480c29820192220005030041d4040c0b50042c00d00042e000007440302441d100f03840220002c0c2a44170521a900e200c0e41c03950740c540c8060387e072881103180361420700130301003842c0c00b00c486507c00500d00c414124003003015504018040941098040002140c000714410b00302402c0b00e00ea441d00402c1c22101020b00c00d41d050344101010741c5c0b03442e19184503c0c80310007244903811201c8401040c001010818040d202d80d219800000c002e40080410100101014981c603000c06941225 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 867677149 1250 867675899 867675931
    0x7090302040605040b03060123181e04030c170c010203100e0c04060c08070c05130203250f110127051009020d060c1803140708030f160206090a030b 65
    0x305000a4500468583d40e06da0803400044c060310128000b01e110042c8100600250b001c00040894900c1030025840781c0310340d4044042040c0c624030b0031210b00d200749014134a07401a00d01500d00800c0142c003244000e0020801c05101108000c440d402d903241300d180000210b590f801d05904210000a140c0304035400004401c00040c1905400d106070b038215015a15180707083f504954807144164031080c001c891503140b02c04082001c0e00d92041440544041303203001030380e908200e00c2c824000d29421100c1803500d002240d10014150b07005800900b020900d00784140c040d412840914054100540c1c07110104150b9284a04007260003060001e42c07a004a0070303104024418100c19013500c40c0c40c04042e4001021000f1040003030405e600c100c1e5203404c07918100da2801c09d003c000d1a58001c05506c2076450700c0301110910014034050200034010941714004600d405a0710703007680d1141c025116000e107020580180d140540d02c5000407070302100401807450901079105d191800991605481c0c80c54001d20000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 867678399 1250 867677149 867677159
    0x605103813030206090402040b0a09140406050d110411190e12030f071b0b040801051501021b0d0506090106061202070804050d020d060609050a0c02030301051804030c0506070903020406 81
    0x401180c44128407840341400e074900355020b03c2030640c0f20102013030f0415400c000015402131120b001d00680301d41651025807543c80c001408109621881085201d50315028007003145580d01100d14860940c403509007030f101032108001500904140c28070b0300c0c00d9000011104011024210111506001a2102d00b41518081c091203804003040c0250003040e4000c0080c0b81901d0000d901a24490b8800c0c28004800081046007002c07050a0364006d00152001003010b1103140401c3c0502c561010b6101101d00c035840c80030f03000035a00d0925039804406108021207694058443c02d000c050314503007290445490781030001d8254000c01c014030550b00003c044918400b089010780c002c466110b40c102c50785038102400c0c04100400d44405038000c80e44a40c00045800018800c0c0c05110300521640034001000c0c906100c010042d210084801d4046410410040c0100d64400c2c14110031540c07030484009143e5241c0c60107954010308010701400c9442610104400b46130302003983c0094910a60307091145903524 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 867679649 1250 867678399 867678509
    0x20c0d021c090f0e040c080703050115050103140f06030c04141b031b0d021b010911010c0515130c3b0a0b01031d06100506070b04060510 60
    0x1806180d52803120110104507014080e00d0245e000f07401001d8181440d56903a41561415245600840d420394440380403002081c0e044141100400b02030806001c205400c0e000c0c0b401d4143c0003014103000d40303061400300f402500c0400024031450030240c010800c003828460f811150660807515080242e8000c42c8400ca50040d0704207490140c0f140e0207203030303c0507002c0c5031211000b030304944907407043d1f241d09200d5806a6010200040000d03018000002103407a000d0604180899441c0003941c140044a03090030000340c1c00150904175058004100042c5445e21004401c00c043d060a0240100541a6010840d84080a04240c050301e03480a004036041c80c2901100d6000044603c0b4038040c62004005010218207070082451403105160020315011104844010b00b620f540050a02e68862030030007000310303070040050015240454040341804816a40d452229000820080c141900d92000c590f400c4c07410144103014185100d0f011002c82c0c0c2800f030314112074000892060300d9040c1903003034591401c92 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 867680899 1250 867679649 867679667
    0x1230a08091e2817180103060515073008150904200405010b13140a210c0e041a0f01060f2f070803030606070312020c0d021c 55
    0x4400007818880200003109624a512450001c1520b600f0003140f4000411038034070400082800e903500754039181c80903d001d1031813490850103414146400c40921040d6070351504007880b955208100c0e607680c1c00710f11304400f0401400120129044401924400c411a9102070705c0e11556682d0350b010041d80ea00d14a401100200f504840c0c1200920b004140401c075802845006214030510800740d10308c06501003011100241d000d010041008111302c00000300040f1100000c000d580c84c01c0354000052000981c2e0316407680708078491500680c00300c404091101c0d0b0300c5c0c0d64458001f60a51354040c1d9070781025403904400c50b0226660100c18420b4005c640c6c40502e101d014001a0381c110281340c3c01c1184c2680e030300107901074039402e0042018401e046201000200c002c1c15042402001c0c00341c1200304914a40401508044042e40051041289035121041680c110315014580704401e404031b8038008000344200303000c0079154041d81034000c0180c0c0d00000d8900d900c956400a06003031680d0380e0b50403191004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 867682149 1250 867680899 867680953
    0x2030403030f2a02220516050708040e0603100e030702100c0c1a0c06040f020916120902010504050319170c0303010306020901181410080106050901230a0809 69
    0x1000e2641c80480c82d07a1000d003202e61348040d000c8100d50540f1692031240d00701c00455802442c0d103c0c0d0800502e1141d8034a9002c04400604141d400e0905581c0c0700041c078010347c028002c82c0102c000000e5001c0d40c08100e140352140e07c07544d007005500901c145a82c1c07203501114042e03001d140c5000c01c100e40c1d24424203800034460b400c04407484015003020007004c1e142102003112042035100340042802060103011150140e44076001c02c000039001481448140d0238010281d9141c1c0b80d805001e1805a90801c03084001c1100800c40001d015070b103480162150700858000701e8042c40f4a244030700c00c004013182140c03401402210001005040c80d68a40c2c0310784030300c0d80303c903025401c24401000001d0039500030b8256880141000181e5004685100c901c0706100e41c0f0a00c4243c0c5508856105400c1a02c0564440300d0603107004031540d0b040500290503441118000307030401c1459a80c0742e0114401c0c4d0548032050b070840c25410756501802c003006040500650307103c0111b0150181e140101c9640110300e6070400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 867683399 1250 867682149 867682187
    0xc010908030904050403031d160501030506090a090305040e0a1508030c0a1502160c0915261006092712080a020906040e07170408090607081902030403030f 68
    0x41414050101071301000d082241459201e03000f0103d02c1440a01800034030b6450340003401250380c0034121058401c0b40e42e00c80d9061602c2d1205000d05625240e0b8103940c45100d200c1e022803044264541243c2d544581d0b4850030018814209100c80180f0b04d400103403034030962044055200781c880c12540c0e1039205048031060254401114600015002d80c0614041c10071030301e0041c10140b005a08402c210021603044a6802e40c6600c203001d261002e1241004020a40100121a5080a02504540107600e85040c40c0c2c0e0980080035495100801051a0410035100d09020017683e408009015040c183d403104008482808100403503103180101540003a00320500c142c115840f02805c0e180c0f541d003d051400d20325000c000c0d4080a8480d24020700003040865400341042c03415001c002c21082d150110070010480c3c2a05000205241c18150740c2d40250440c0c0c103a654030401d250104080c0328104030020104611140d843e1003903004000340003101d0094659040c40803521070b04694859814008055403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 867684649 1250 867683399 867683407
    0x30c02070b18010c080403080901180f030206162112110406030c260a0e0a020f0f010219080918090a0305072406030c0815041b030f050d020c01090803 66
    0x10540c24030a102c2c0d189040c104061916070b0342d155019554403039001a140d08400003609070255a00c10344040c000c00380070840c98503441c10000e107108200303c5440040d100c0e00c0045001e690f104030003882d06060b1a807101c404059004912003003000711002c0410b0501082d01c1344d1181000681d28001c00a608000411051506082000581c000c1c0400d03001a41000040105115140d40c0b43da084110009804c01101061602c8071041c0c05a80c0901d421200903001003034118016221844068020031085502c07040764071600004034603000030892103220050b0b03000303c41d0003840305050062001d10429101450140b0320515005228201900e0b02c0e03d1a0340700c0038601d07000c40e100300301502400d40b0400140b0984100102c20244000280d201070462a81d200b40400c100a4800304240041a400000c0d110b00800f0003411a201403004102500407010204034140740c11460000c40b02456001000c110864600e0810590314404890751202501c160108902e0f030398000c28120342140c210350001d500d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 867685899 1250 867684649 867684667
    0x90f0b09031b030c070501110d1d1008010e060607030f12060b0a0f2c0103021303050a0803070207230105070501060b0f12010f0f030b040c0801110a030c02070b 70
    0x8044402800900280800d000d07824004210401c00715920201c180119114610318005500300b54490f4080d074180b180140320843c4984000c500024111040c1c01d025440200c0c1c10300c82e03075001c2d00e20301300e29a2200241009091054214080c1e9040e01c8070300d008205503030f0b070f04030501807940700322100540400c5d003030103410b85540c1c0b040031f041c4d0000c0381030000030600996070b0100891540100c0b84442c04034000e401920042070f8400c85490078280e5402d0600c00c2041461500050702e8110b40d8211304050300001c0754008880700c280e581c00299030140031982c95860600740380c60300b80c20641d58980103000e409c500081010081d400204000250b290300a4242502c1d40103540307507031000034222804d5480705800a00040200c0103084406901101196a03080c0403d002c050240140c0144055004c15102400708040f04806a401c0e680d00c03581c01d45007601c9031304050380d108003264071174032a66007010b50243c4034007181401303000c0400f0f0f507890038406182c0846081e070711058503010321742c0f20381c000b4403c0b241 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 867687149 1250 867685899 867685913
    0xe0f15040206030f09010b04180210090e01050103020c0708030a05040501080a0b01050a2610050a0b1306030905071509230d020f0a0803030f040b06101b02060f0304121101090f 77
    0x13030001705083c000a40b44c0c0b03441002c00e060350280c043c040c0c0c01c209074400142c10350610079480c51b114100c0d0b04d801e0211a04100c210750120406004041c101035000c12a540e04040800084d005400300008a0fa00c4403141c100003880c45d403181c080c850014080c140403c2d045d56041c010760541c0c0b50305071205c0c0d084c24601c4004480200e200149020320003505500344803030515007040a4069018611200007881c101414810700140c2d40e03002403840d40c810420240d80402c0e100444c01a80c11600c2e000c03031a00c40346d040036844c01c030340c5030000b4003c13190100c50752980307640000035007049079911502d003c1c1c1812844d00b004100010251207a0b0010444510f0000510b400142d0320f009050007441041c81c03640785ca5607549140c00449645030401110340c00d002c2840306c008001303980a8800c50714101400c07150500201860807121402d0416001c10860b40115a071303400a80b90003460002050f41c89282504120b00c24044541403203000c00c4044403c40b500c00018001c00c034031a038110b6004445410300399038082d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 867688399 1250 867687149 867687151
    0x4020603041a0a060501031505030a0f030c0507090507021002030f13060e0304090f18020a0905040602090d0305091509011d0607051207060b01090e0106051303060e0f15040206030f 79
    0x31500300900c42c48240445007844402d0240314800400a610b42c2400d0000d01110064030b040c880000760750200b0480c0390b800186490704950710141c4045c030709007079107425180134509501c02400c9004900c404103c1d01c21030342c021886410a5400c44000d14403007404001248010b40301480c074903101c800092451030f02c0142074180c091080100003030344143d4210b1241550026007043c040b03075440302d4801c1c21081590003600010100f40000419000d5140d0005280d1072840c81058801d0b521000010700744020740c0d05641d0603001c05082195a003c8a1600504c1035110308035284c4650244484444d0720303d481e20a690389100180c40d04044040030f101f01e0080e1076000d01c1101d51090041000400080c0207100c0c0341ca0781c0c400204a5526039025251880542d030305040c401e41003004520081040c1a5030b803284504440c0f05040060b958034403001c1c203904100d066000540820f06280b0303a202e0081c000640c0c0f0030102c1d0903606403010500c40c40840403ca20302618040c0d07000030300344042555105058202c0f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 867689649 1250 867688399 867688403
    0x723130b0c0a08030a091103060f190e0703140d020f0601060c020a0f090b10050a14030a1404080a02010b010309120806061209060f0106080405060406110f2205010504030b0402060304 80
    0x49104850a980f2018658411100051200e444140032004c015507040b61090311207044001d040d5130701c0d0000203542c01c444010300c00c0c00b414041c080000c4d01c0c03180e258484c08040e0700c3d40041e507030500e8507800d001c02c0c92540203529401500c601040040c002c0d10108543e4641c80c030701c0014107291792074500b04803010300f04603100f030742c7c0425440400541c403942208980300900c070003500841c2000c00c81c82003224100c1d640c0c1d0300700107100f02001103182140c0e00107280030f0190626480692651642e1604d64028018801c0030801d600e40c1c04d05100500c0205806800c815040f07900900501501310011000d507038100300b004150f03001c1034044260023400b40c030101764002c40c0500501d051418400f203100304102d0907209e445560304041d00344403011000040b0035000d003140e41000066030600340c2e00e803075660400034000b41c00b181c0d841c4419061780c072031102212141500e0b00503058403141114060500c03080010341a1851506171800024554064815541229000864180c980e600d50f0280641a4402842 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 867690899 1250 867689649 867689653
    0x715090b060627040228091502101d0105070e04050108010e0616110303010b0405010e01170f07020f0f0105240d030e13020406120b0118121103060723130b0c 69
    0x2c0e00f0030307040b5505003125100146c0d0102200d0044902d0050702041d601d030020440c1c107030301110750001d054001500c0048020300b141d0005541810240041004902c0c0c5005803080d401e0005002600f03070310448002482c0030440f010861640d0380d5451a003203505030000141d4a030000000511071a6070390500031280412400c2031401039020700d01c6103046910980081002030303000b040502203560b10416840d80c00c0c4003824405d10401e035102080094110007000300c0c80054182e00041c0c8268801d100000060070740000702c0301d4036800c280c0000d01034501207880602c11094890940414081e40d280c04070300b0071020b846c01e03003000950386044542d42580c17017165400203840382d030180c1120340e1840100010111079031140082c0c0f940d03070004d10940e002d01708414104a4030000030f003601034000500c01c0849200310695001d51503546041108000c0d1001e05030307494010081001401c540111028294024645180310703c00ca840007400b09601414880c0100c0500000040c00012603004c014254880c070082 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 867692149 1250 867690899 867690907
    0xa0606091a071205030a20030c0d0608010c030e0f0604030807050a0905031c1803020f0d0201090e01080c121212070507140d0210110a140715090b0606270402 69
    0x162000c483c103206455000144002041240340611480350552400d0f601d0b014401203040301f401c00c0c81d01d01010344400403041001815410005c45c6610260041c41050024450921019006002000141e0980a2030f02900040068400c008071741c082c440c5a05460f80c403286c3e01d51600c1220503030041801c200900000e03520109207540e0403c18644035030b0310b44040346112007a100c0020f01d00a0311441900c04200c00078811310050303503031403910460000c0a48000411a9179400100c035210700560084146482c100000b29040102291140c82d030700c0140e4098401000c0c20080c1591400c0400b019180d800c014480c2c2d000810043e4010b0b40c1002403480d2442c2020303545c0e210070002006581444029a03c055006c00080e501032100d0503d4032841c940401032141d41c00c4c0c050000e88643c019140810036198800c40c1138500040a980c0101d4100c0908400381034100c007400c00400320b440f42a55980c14080005003e03103006411941d0b442d400341311000740c910110300f816180c1c00381c61118030342c0990240 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 867693399 1250 867692149 867692153
    0x8070b0304170301150e0f010206010902030a0f0203090109020a1d06060a0e03030c0a030206060604060207211b080105060a1d04020f0d06061403070602062206050106050306090a0606091a07 83
    0x400694040c25203101d0170386014a400c100600381e014071001243c06000c12002030380440ea00031a0746411105585409a035035a2020b08000003090340f20000200e9503c00300c140691118154401a0a02d00c03c0d81c036104607036100c032107103140c60101c81101d541102400c00010700306d08102024011286450410119003411100000d046402445130711401d50300c2545407600340f50b41049103640014040c1c07215481c1a003051802034803030000e809144004010192008407050314a1202011681c0000300354000c14102e110101c0e040000348070b100120340c00e14021070141d20f80000c580c4111a21800716001100d2708071303101105520020016644083c1c0d04110715215120440c0442e4001d10a2200066160400403901032003ea5201240d009034007042e000d1014a40010f40c05403c528107000d55196143c120740c0344040c8020841c402082c1074140740000a4007038011000c0c40c05039508903202e81a031b58521008500b2501e00d0703c10000050001c5004110610700080c4400d050881440c50500d406025 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 867694649 1250 867693399 867693443
    0x91f020f040320060412030c11060309030c06221202070911340b0c0d020d020409051605340b1e13020114130609050111060108070b0304 60
    0xe03920a403445884205500400c010100e50b03881058801c136480c5081c103041911a420308000300f2401801c0c4642c421540e0140405e40c02e074065035070001069207a50b8076100315101d0722500b00c4810340b0f186106080219079201e0f41c10035200f18011083e13400400f9100c0035100c0071000c2c07000c82845001c1d03004094020034065214041c25880e0813030a01140d03a14811544807103900c2816102c50041c881c200c20340701c030610002090170090300340c000c0240481c1c2d45444685190510880280d40219440018a031a8800068002e80200c5140ca030040085076500007040c20140851000980011740401140046000450109095590500c0c910b1b5503c0942e0030050500d01d600c103c2594402550802c003c100025101195406280c2d032241d4412400c094064403003a0951000081c1801040999058005c601c4000d0340d09294420106190181c0d81d4131001d040013206004490001d003a5600d101d02c45200041e1260480b1008001442c56915000d681034080d000507004540e1420340040b101d0100041e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 867695899 1250 867694649 867694657
    0x1219031d010c1d0906043606050c07021302031503030708040504050717160c0605040f0c09092411030709061709060f0405010204050a060512010905091f020f 69
    0x800c00001d50040c01c807601074075658014410444000428800d400b083c0c840500181c0c00202c1500c001c100c020740791800c1d03a1440c814030f40085442c5032401615100e804811031078940c03a0300030441044182c8500d020f50786030b4840c00802a4101214401070103454101d0380c021948200c0080d904480e858523100000e00b1544040426503a50402140c103001d02c0c501845030b603800c03107560304144010000c1032400060101c4024140b450b0360305001c07121007402e405002c15648040e845003080005240510301284040310340a010f0321050040000840c5086540c07103000d9041ea0000d0b2825a0070082490712405690140c0034003400c19160481030808110020245019500c0c1d40c483d603400c213003007810003480c6820a000f956084240c000a100100c407000c00c44079007203582010b04042941c2c4509050b1701a10a030350080da0001203d400015205a00002401c04c030910420b07050001d990310000141661030035a0b406281d07402401c80c12004030007901e0b01319004e40c3c180d8009800c2c0024640d00c5521604 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 867697149 1250 867695899 867695951
    0x605131a06030f0a0303050a0e01020a120905071a0307140c100506030a2f040209060d020307200c01020609010203010f0b0c100f06050f03010903090603090c030c03050a0c08121903 79
    0x203200c00501c03440d000035009e01d007169140c900086050000c00c05000b003007402c818403002da0745640d5021b0344013444414414030024201c5000420140ca0800c03ca84040f03a0040f2000d4001138101c0ca0305450501c122030458103008610f20050a40810b0110520000c1402a084580c03510075030701c0070000a10850b24000520300200e104854000b92a9401e8074800c1c2c01286051003581704200c01402036554800340e805640e98070400603280e903901e110a462012401c81c40c0000e6000c9400c0c05485204001106600310340280e081d10a952070310786405090340403e0146640701c64180d44140884041c000103003052060a00488a80000c10044441212841203400322515210a4103101d107080c0410884000003060b0000c021202003610000c005c4d21050003a8010180c03201207000621500c1070041024582000404820341d41d00e00d40b8642c2e904800038101d5825007480c1001079031003030100d03074000011b011134221454140049503041c030f89451103c0032000d00da0340f034410360345000c54008501d030303440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 867698399 1250 867697149 867697151
    0x30b090703170909070f02101a010f03140622020a0801150c031d010903061802090919300c0308092d0102160f0605131a06030f0a0303 59
    0x30300350304003041601d581e9140c1802c0120100070b080306036241c1500d01d5610600600d4004603141d48071000700d00f421100954500d1550403d000e56000311010040b00c02005000d0300e40300d120111601d0143c06841c8061003148803c046200090301d1030528503603101c41508004582036a080c4401c00c250203d8000f601c0c0703140000c011000502001d00d10740c40389400c4103128148800383c881c460b42d0003040034030000c8040107489441660000d50764016a201c502039a4000d10500031041040c80d00020070200541c2640b0480c524808105004808102103a1050603810f03e0b99a40c4120340798031710003d12482c030820000300001070080550003401d045049108965451940101d5541001000b102c4003400c4a041c68202800800c1034041c2940803070b0081e204660680c0c4030b60042c81d1420300a000c6c032100c0c080c42003190ba100c001080300d030300c0000042c14450b20080125031140040314800c0c0502c08402425076031180844030030242c410f0a880d5024800070704481543e128071080a0a24099010481c003007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 867699649 1250 867698399 867698413
    0x308070602070506150f010e1201230105220207031b0303090204050a29130510080f01090c03140a06180204140c0702130e070b0702100311091009030b09 67
    0x102c024448181c101400e90b0030703a116518174000255080e680c0c8441141480601460013000d500e40741c1103030040d088050020010070385c020f80100d0b244032240d444042845490350001c6058a084885100c01c00c0c10500542422000e0301c01c42d40080d4441c64040c2c007440320002d05000400e006c2c5103843c0000d88240d40c00700e15080180305020617200007410144416082c107811401120788144805ca0300301422096804401003c0080f5910005007032100074228180000c01c141c0790070211200741244c6900c800c64111002d15a5900c0c05c03904c016100a025002d90102000450408a400520220403034191340b0140c1540ea155412100325240340c150444110180761309614141c0b041c072107186180445d2600610303150f01c4180c0d0703e01c5410002449680c1c1310b003540c10394658681c00550f08008010880c3d120a856000d407200c1c0da0041c0104031301c10003001d03500c258000d100c0d001d4005c03c0e640149510b070803c5042070400c552102c0d003412540401c568080000041403c443c1c4450240e1690ba01170404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 867700899 1250 867699649 867699653
    0xd09050d1106060909120d0f02040f080601080615090c0c0d020c210c10020f010c081b0a08070f11030d05040212060c0304111f020622020102070306020f04030807060207 74
    0x102000100400e04c21341e410000c000120030081010744d00301d029031305415950003d01000800800304400c0c4a000148082808242003030307212014419628003030304032a01685c6e60f00d0040d50741d0780100c071518139046402c82c0c2c0207900c2c14080340c9140c10403651126076007000889555113180c004840c4519006030300c10f42d0302289a007461a010303800c8078400081000c0b03c0ea41844010b548680040c13034035010761035180614010500c00d1240203510401365000344900c04804500405080c03041d50742e03110550150122a080c1413a82e41110000d41154880c080241c1d43d0a00c00d80301f861004000c1e2080c4417a00c0300e007402e41801400103012038010b5000000e42c1d400d150043c440021050f04d51402564040700134400e15250b9202a00c0d400303613006d48072015041c07002010510349985643c040c0d090003031038a940c03120190081384180c070500198003804800104900024000500b003413010340942c00c903607001d02c082030245d00206055400159001e151950301d1751800e07025407040c4801c0c0c501301c0c0c2c04901202 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 867702149 1250 867700899 867700903
    0x191101140d240b031614030408120705070519051204090518010509030d0e030d02030f0708060f0d03141b0a0c0501020604020f0907020703080a020d02070510050403080d09050d11 78
    0x3840d08440c1c41074140040c2040b528500c14440508507040024000d601816064071031980341d9031086c500c1c500f8684034113080c54484000e8001c0e20783c00004c0c444000000d5500b070711400940c0c050136003200061985040d82e22401c1980e0904c01410b5502d800740341440006103285000070001400110320009043c6808000001c45440d50560000542d0400e4103006400e00000b0941c0d041e101c41d0440040d0542031654900d02e90721685048254590000c004c0041c0d14904100340d82c0b04042c182c0750030905554903010010040c2511170186d80c04402c45402c0d0020a02c82c2c0321782c3c0290082140124a0080d80603841407205010070341d03800c0720f03500c521956410031402c0039001300140030038002440241483da001403010f141c65140705008542040c0003920007442007108200464004121036a11360040000030b44516075407400801511416100144604010b400f5006030129581c1d1581809e040d0f0307a6001c250352085481f020030980b0303070844401140d070038412003442480c55203410512248008400b8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 867703399 1250 867702149 867702191
    0x6060a020f1902090903040602060117070909060c080a090210110712050309130509030a0e0f0a090f0b060906072306010906240905010f020a08030a0905060603191101140d 75
    0x348281c1087c40100001500014a03605644c07a000c5079240d2104000505850003071143d20a500c0c40b428044034400b400f8240e030000c1c100c2c000f9540c3d403203900e58880c40c4070000d583c0301c004000e4012071b61141c020b0303900e482030040700d132648042d00c10781300b4031903079082541026001c8140c250342c180c00c0043c40360b0f02481c2c450444030030031006031001e206030721b800c003d020340301e001d6042400c05012800412800c15030380d0101401480000904080d46540c40302002d8004010080c0c180b03452615001e154132a070329104003a81c040c404020b1480b4a072980982d5400d1148040d0002c919056141c888602d181450612580340601022100051030f280782190311b0403041d280c1c003200c050300c80981a1150006901180341030650b00c081c02d1031210562202001c80c9444155400600f010340003000b031002c0142c1d550460740e032581c00749007159402e4450908040d1100380c544161801026030401880c0020300c6480c01c0c00800205042c1800c14002040c844600d41c0c0c044246540d00039074500d88200c000135100510 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 867704649 1250 867703399 867703411
    0x60c0903050f0f06220f171b0c12060112080702030303070809072106090809100c05011103060a120302100507080405010522110f0d0c0305190b06060a020f190209 71
    0x5a0040502d881c8485040e000002d000144d001b40300c035050000c400a4204100a07000e00256103100202d135850319600c0c0802012214000c0801188071894549400081401c0110142c6402d0346010202900010122011a00f03400706120389800740c2e0f4244051442800c058030390b0907140c50041080c81c1041781d2600000001100108900b1207048585823040f038460f40500c1c00504d16510b8200b030000c074055104060351001410b02003501896120056041c050f1041d00244a4901c07070151121a0b400100d80e960342020350242d007040912a6946c901c100e090207801503a00d14032640c030910381581d00849050300440c42c05824072040110074880c05600c440c400c4a8101c0c41800424041c440312040c1c2000350803101d603800c542c0016690203091202d0b1400081c804c84010204c0e1405045005203480113a82502860700780d1041b502c10784000f000b0480d0f01c010111803581d540410003100c0d4020703600200840c4100c40c52114102c0381080b407990000300e803501505040209204000d4148401030030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 867705899 1250 867704649 867704671
    0x12100f08252d08120408010e0c0f01200712120804030f110c03030d05010e0c0c0d0c0503120108060108010b0402090315090a06020304061e0b030a060c0903050f0f06 72
    0x82000503281c0001007051a00c0380901030002e40152000505441a0326088800c0341e00801207080c5842414030000c00884d541c00c0001c0c40303a20b807400411034a840c040c00070980c00c07140d903200d40c40c4076600c20003c1e00010302d80c5c61100c50340d0036031020b1401e2070b00e252074000000c10318103940181c003401004d0f02982003d02181c544a07031a4502540c0040400000400b00300520800110300c1074802002d000e00c074403589014040742d0300c440c644408100540300a00c505405031344600c02156040e101d850489952508140081c034402407461030407a4101400710090303950340001d1181c034040440a038052070003020350030b00070311701d5505008800f800c590111404610a52041003600c0041d1404603041c10103842c01c2036a445295aa0340110381009008800181501d10020420080100c564810840040b100c1e0318009410703032814202c0100e904010680d64141c2c422a5079034001990b40e000182d0342546442d190042c00d69990b103442c585034804200d0212500301c1c40e107a035448101086001c1d405604850 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 867707149 1250 867705899 867705973
    0x7150504031205061c06091208100605130b0c010f0606020a02010e10020f0d0302130e0606120c090a0b0403021e0d060905241e010b12100f08 62
    0x14014003121030904008000e070783c944000840950f07034600d0600410360141d03003141c4000c141c0c3c50130000038801e0503c21901c104e104444c580d41140f0800042d0301c500d0069101600c1241882d409a13140c1d0000749c2c940341d60440c1c41001041585401001d40908103a4100215015071590b071000281e07003003500007400710f51014041c7c1000d43e0380202421031410064902c0340d003c05003c40e0403810003101071a8042c180c410781e10343c58802030b403540c01400000e06180560302c56a0312680800400c0c182a14101c0d4000b00901502da601d54032588000d0b000140050003518048503400403c03000002540300102c07140340860100158208136581701529044c61107540c41b6041501c00007180124441c2000d0303c8140d03614821420440c0410600c903170301150703800300802d105194200b034a5906003120ba40c1c1d20b685020102c404901c003003010305416035450724003641c2460841d8009401c1e8401c003d05002902405540000d511000701709400302510480000d00782c00d00003070608103008503500e40b8004524203039030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 867708399 1250 867707149 867707153
    0x2060901020c2a090103030c120e0607030e0f0924030606010c0311190605011401020105090318011209031e0518040c0507021302030117011401151e020307150504 71
    0x410f0204106043e1802c105503201207460010758602c01040241d080041c0c4000401490b03000b28a45048610841d10a56000c051060480d003914940a0030b5030041010f1250b100000d000d41c0054a4080018020700c07010320030100011090f003020390385502c0e42c46640040c415007078103043c20000040c2c010740061899003441e0000078460401400040c08000a180003422003c2d001d00c000284a4694160802c0889190a101005000a1003060240208a01041415401030040a1240503410065030501440d00302400c084403541e4003da04228500308082c640c074235a41304c0c00000071f020703540b500403038030a60802900310003007100c0010501406210940c640e81c1403150392401400140c03008540702000b0001590705021303018009520007084001001030f4101640554121581452004034000c58400510300b03c0c0c05611920714103041490041c0f107900324060b2105182d40141c0f400c00f05a10240780f040030841c1c50504a0340058000203a81c0e42444111201004a540ca503d42049030b0f007065 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 867709649 1250 867708399 867708403
    0x609111e030304030813080703060c03050601081e0606040504090b181501300b091b090a1a0303030f0105100306060219030917101a0109180f0e0d02060901020c 70
    0x20788401443c0e100700159440e0781040030468400213100320b00c2210012178480c42d100d00684040c1c48584000dd160000245aa41c4515001800b40484141940701406e4500901b104000014170b10f81e0482000c010001c1d81d40c945110308004e0900411203420315081c16200e81e503070b50300a0f03d1220803030391040ba12140d500064620580c112001000d445402d1850514404100807480030201c001390340d84415901030229444a851080c2c00100c02d0b1025080e04105800d250388101c1035054119020800040c40401581e00400944000d00402c9000d40c070300c1d4001906e154012500548884000c000410031408c0004401c4090103290800344041410104029035602c0c18010410f1404080f0400c1d03001e041c01584003002400c03980208000c2040c0c0356040a80e40c1034201b0403112850300c0c01100305070300c000080b506038141c48140d44104080b40350400340000e1070503a0891091180c3d60300d6070924922843d201d40071509040d40054000d26040c0302000c0e040035070083c40d2081c1a401004084450000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 867710899 1250 867709649 867709657
    0x803070803220c031407060219020906130504080406080f0c0d091b061112041a0d061d01051c1113110a020105100b04030323070609111e0303 62
    0x1256031010044502d5054140103900b00e01c0300a010710183c15008020710120001806090b08002c0444000554a1030120b940b5a40f035480302616580d5080c10785e0051410400d100c0e0002c80003444141c1105001800c4821100203480132240c12800003010448560090301403580000c4d4003492502074508003901450303d11480640c120707050360300c1484208100c0c60004051404038418070800051303440b0340c4040d04450700280140b00502c1451880001b0b005c02d80120780039202c00340e448000c0b10b0100c245040542d00016074aa4185480f84804103450707904007941c90440d8407002201e401c03545020f0034400420143c02e851044807000c40002d001090b41980c900100c01010340f034440d0705280500c5910b00401d010780d84040201000106907800b036505401960140e40c0300c40802492aa40f41a4940751344194030000300450f00a8403200325040400d8444800d0307034003c9980c03e1070a41c90741d807050b040301c40d078036021200c101c104103a10f0300780d00f480d003090580005d00901032501e911700e001c002a40d03801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 867712149 1250 867710899 867710911
    0x20604030903330b01020f0f03040303051b0a0305070204050c2b09051902011709070603020307090905041a06030a030203041a1b0d020114070c021002160902070203070803070803 78
    0x1903e45264844010f40205804000e0b0103410380a20070907016190041c21000080390b0052240106814014001240c4183c0014008000314509465070fa025251178000c0468042d41d45041d88014100000c24041448124480c1d559603039206c1d181c1c41000f0403580c0c040c2c460a00401c1c1444220411064802035011a014403607020041005c65060301010b0001e00308010030602500a441d91000b0021074001c22451003600c500030b5020254426000c99201140c85c5c0d180c0745c3c00705030700300001c60099004541107c004d00e010031026883d0020b00c8141c0303034141c034200d4025004006200110408048003032b04400c1c110058902c12015840003907590060303000b40c2845d82024610384c4404030940c0d0844041900d01c1c05468260454000b0090f260881448aa00554207014164180c1145000a07030700c42c0c0c5840d101d0444038506031b001e10601c00c903061082c0c0c00358480c925010400c24058240680140350072440540e0701c4102d441410b08201d0540c2c001c200e0b03a401482030400054950050b2a4405 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 867713399 1250 867712149 867712163
    0x16080a0b0c04050a0305031314010804030e031009030f0207150207050616050f0a06150e07080406240302120109050a020d11180717011a0c0106080105100312020604030903 75
    0x10311001c111030720510907a800300f03a00910500c0c00004001020024000d9284817418461030a5a904d10003400105207100440c0010b8840700040d0001c0d0203201442245000501191500d50144002001300c0c0e080e41010350110344a01850305079668108081c901400001000b4505880500c0c0040c2d40d0f0350031402014802d150200d400c0c100116003100488010350860200c1715002d0444415544034656601d0a540752400d00342c01040803002e4180400849101e50400b030714039034991004407207001c805032040b5039951b218000420f403c1410a0482400d4204210307040d0858550310420141c61080b034203190942c0d061581c220041480410ae06005e40c0d01580c0d085000d45807483d12945003250054100d41c000446009844c5103100000f03168821851340d2145140c0c070400550440d92981c0034420000c3e00c802c40000c0490415244024001c903107145000440c00c1a01c441c0070900750750381110a550f441c07130903100800c140100c2070301e00d001003146400500403d00b01a1401003a2030300600000d01a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 867714649 1250 867713399 867713401
    0xc050f0f1c050708040b120f060f040504030e0a060f1b0b070c0c08100b010e0315041103070f140a0605040807211b0e010503122a07030c0816080a0b 65
    0xa24015401c42e54491380c05205259510788440d00d108003034109007100d6807006214400110810f01900995001d1500144000d0440909804100140c000103008500300412214a4149034803100d036148040d14840c0c40b4111004920140100026216101c00f541c00030030645c5080880c6d800360445030080d4091505554120345410960109485940045070a208034412003407804c0c410343c0b01089501c826a201c040300135001040559030310310b480390103c039904080080b40001d112000c519454a4000d01a01e031011390303654900c41c00d9441a0b1003e900701d0b144641d803c509250030218500640010b003031207030501e0b05004a0355a030f0020f0303000e441d051720402d201c0304c07580c61400032507800c615921510000059589040101c405003592140c3c0242942e100c00110700c40c0740110b40901c0081807145864181010009001082c50740d2807940d0f026410380b030803001d041510030701100000c1d500512180a45a14003444103161000c1d40c41203508400d0080c00c1888141e001040e0f28101d075030032000306142 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 867715899 1250 867714649 867714703
    0x191e091502070f0806070306060c08160c090f0203091014010e040204060e1303030b010f020d05030a0902030712030e030d0f030e0c030102040906060809010b0a0b070c08030304030c050f0f 82
    0x107401e1076078001c0f042148000e8000110508006107483c411140d982c2c06002090b540d0f4400c1d15010800c080c010010081401101c041c05810b8084001c00b030b0007495050302d015a030340c6034902151001400301d054103070004200465518100102d80ba80c12218038104909481000041c1156006009541380790f0203031404141595a942c21540140050208407403050030080703034840120300c440c14110086030500b10101081e41c059160488000110f4014002084010604440c06da01c0140044441d9913118000400f5032010040b29019200c0d18080000c003c01c00e00b8098485624544218800ea00c18400084100d81c0040e51140e4440281004210229020440740c20101c0b03038140303260998408500080c1c0030702d09400200455849880d81900b949511a4403130070f03665000c0629801801600f410400144414000c203c5140580483c41100e6103070108541142e005075415000244100c0c1580c0131300c18180a0003120442c40801440031942a103070b4180c0307559a04640f0341c5180001144240 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 867717149 1250 867715899 867715903
    0xc1509050a0305070323101a0a21061404030207050a0b16020603070320031008070b07080703051e03100b0306031c030e19120c0302030f0a0c020402191e091502 70
    0x19140a906d0140e840200052582d0341c010050440220705400c200384200307441c0d04003d81c5803010794200890020800f0380f01c10400c0100c0b4400441140c000360350341c400c0b004941f01c8040d00350082d0301c02d42c0540156031503d000c022800f400e40c1c000c640001303000c1008282c02c2c162100070304e58040c1d06403030954603640c90050540c0201440c42c81000105001c000c26820f4800500045104483d910f035982c2a05807200c1c00a507460609003d2901d040340300b00300c00d1000c52015409000c8c400d11038a0103a1034019403000c40c0c3c1010a210840542c404004403e000c00311200058101c040c003030f200107841c15403400100203030b07503807440c00110744503901c0c10906c0241c2903100740c00c805074210021044403031a0307a40a19403201043c40c00c0c020b8881280880c03a00410318421440c400201d42c05500440c14002041641740465008084800600c600480340c0c20058407940084c1007e42c9074000b01c50301840240d02d01902560b10b0a00362058068804813135001c4640000044017038071988261403001c0e01d00410168 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 867718399 1250 867717149 867717203
    0x160204050a060509130b0c070b06060c01110f030a0605040b060a03110d0903020a05010c1106070f121a090c0f0d0b18040c032603040b10030c1509050a03050703 70
    0xa0f0304004c0c124200028500c0f8050100e540610401510302a03690b404000d11480c0a2040014061520500418410300d4140d001e012140100c90001510200d01c182c040c031a03502514100c0e0802001100700310740f40e60188122070007414142d40c1440303402455800201030f40f00d03814070701c802d1503a41d03000e05400010302c500781c41040003000300800c18441780b810301950395201030004891942c28603544c08896445144c00003290701c80c1070010301942e240d0a800b542c900b90101818004c01c221074420007407802e064051103003520603043c120240500034000f40700b8021401050032029400c01c01401c40c20444c90812907400304411200000c00044000015454440101c41100200702a074240300a10140c001c220040f24803c1c0458410808115242c040200d055181e00302505000c0c4001b8011441e94104980e00040007181802025100e5480c041d10712a141c000941034000144a8001030340c02140c11070180c10100c921140c414030350360303035155164564000140034003000d142c07034229100c0a00d200c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 867719649 1250 867718399 867718409
    0x20d090203060109020d05090102090f060a1218050618070603090809091f0e010506071401090b0c0c0d0e100309020a18090309150c021017150a050303160204050a06 72
    0x42c1e03805503034480d1002c0203508094040165079182c0f101142d40b0041c14401c69001c1e1001600b09043c09000c1c10410046400c84040403081c8160f044051503031806038400c600ca8000c01100850345480141031051406100500d6256a100111101e802e07174540020380c0c03002c41e0414500840c1e0750314030340381c0340074240105d11040350000313404070500241d90a03660705490701d082c110802c400d05a039190b01e40c012a60003840b8007604030904102480100c0c6005c0c032805140d01904001080548156850b1001c040040301d801d071100001043e1100100c10a001c18800c0a000d40360600022400c4000141c2490306110310409144d5180700340400c544454070000010320032120042603514008101d0000780955400850008014140106030302007000d48181d100142951402c5561010350700340080b5402d92941d00091000c803040a400240c80e1036041c030700c1420b54500b080e03860200c1b1020b019002c2525000740d4880d41041c0710507030007401c5251001c0c0816030121404180390300d540c0b9801c0c0041c0000c0d004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 867720899 1250 867719649 867719653
    0x230105090901200304030f23090402120f06030c2e020c101205010f030f1103280b01270b13090503090102101104091113060c03090503060f0a020d090203 67
    0xf03c621825030000954421800780c1c0b200102c40031081d5088881c840101c0090641c00002034854005805600140900303c1000c4c00044c0791a4801118102040003250003003900381d1194100401ea04041c0301582201c1d00595040c110a480c402d08443c101c009000d000840c1a600e20687e04a54030804c1305100320b440181440708610020304006040c540030034603520007a07040c00c000046090300301d5908001c0700c2e00041000071749001940c400c3c50340442201a5503241c401c160030032801d2100518201c0e4001c103100c01c074148001c40e514001d91009030581c0036502d0940359036a901002038500d40f01c20000c10303264400040c07440941000818540b1415048103410385008001010480c00000a008001e400d0b0211b8444441081e940c1701a80c1c0703441c41d40703034041c01c061000b00501c0c200c5401100d591101c00124074203001b071051664400507100ea2003c030018000500f90000d068010040b00e002d42025806000c06151911200c41c0d4224090200c20100e5070016a114126960fa48003044040c0d008003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 867722149 1250 867720899 867720941
    0x903040519091a0f0f0a152316020d0614010b030a200a121d010504141c1b0203101d07120204320109230105090901 51
    0x842841c60410700074100050310f4011020400c0a0b0071015480b4080c00404008140760076209000d806a00390300265000341480d0720200d0017020900900c00c6a1030300f60744003000703c00004194a0f41100d89503140c1c0d80308804104044040c0c244510f40c0b41300301d40542c4d07041d0750700c583c5103400001071141500410007142d01e500080788201815000b1402003454110510084140b80c08000c21034040e09540c050450042080041c80c0340a054204072698003400001014040e502031644541d100148a6145940d11010002042105c0300940e00c1e1f00c07601c0e401007140c4040e440051040c0410003400c0300c240000b8061610721254020a0004c02a50250554000441100305200640422000e80b0031015481c4011001c140300020010103c4403202c2c10160141d49580a0000410301e0081a040c500200d1200d4016241d14205a2010a503c04040d9105604d00524501140c030300c0080144840b001d074101e1300325031aa120388141500d00440e0318907142c0e250f80b0112030041c00040315400030501640 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 867723399 1250 867722149 867722179
    0x3042714040210020c030d0f05160f0210020304030308040f14010f060f080a0b0406050c0c0307051b040204080a032d02210408071203050403020904061509050c040b0309030405 77
    0x25514501851083d540c25035001e103010001e0303858a0f000b120280d0160f0042c04000c00e06886108030005948250500901e098500c0f2580c01c10086103810030798869078181c49500850400083c0d100c03020781d4920245080070300b182e400401880b030140000c5e26480303000c4d000c0d02c1804008541e0848595041c4000c010410400c03038594045c007030510541000c3d41c20040c0002d00703108003045c403410b80f0380d0010940c00c15640340d0355240000d00b800741214581120a01108107004400c01c020321103d030040004100d10310109011131582d60385034407100d01032030042c84200f003800c50000b0460712280d454180020380450055a062101800884200d1441243c1032106211074000c034036030024840c0307140101d03082d00317403007e443e19a8856482851075a070720500c81000005020544601e6940c440e180c040d203043d82d260002440d868080c0e8060320700d103550712074030b0608441208410300213040b070b070800b44103a00d40b640c1c1003841402075105143e4444e00010000c0d071080424070403180139000040044072100242 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 867724649 1250 867723399 867723431
    0x120204020f070f0b0604060b0906030a0603050a050f0f0a0c05010e13050c07050c0904051e1006031104051807050d0c0506040e0618061c06201306050705030427 70
    0x60700f01524024165030100300542020300805003a200200e00c202e24001c104070a11080b0340c0b0040101c100ba0350707141c4000c03000078410302c642c59800d4051002489040d622075005400c00c00302c000510390b1a4090b0207468000741c061070882d0225002400c00c0f124615050020034411804030f040250358034a408100f0140d150001c01411003180100200c50b0000d00f800c09000e07604000381da0150055014075050480844000c0d02001d44002040a50302ca03080c2080052041d00d105400403038160a0f00805003c0c0c500301440b4041c0d001d070b020300b0795000105000d84d46a03118003842c00350602a158002c500340c2800021440b00d8020031024203680da54556507161107c0c030000558005209000000a404010034034000490048200400d080d03c90103510381524128207800700700701c86550321810b10b01e0400401d100040070403410800150b9031103500740d07045969448a5080203051040074401d05020540000070303901504c861030012509112403108103881d105005681c5200103041c006a0301d012054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 867725899 1250 867724649 867724673
    0x6150d02090d0c170303042d08030a020304110603061005031503071202190e070c02040906090308010f0b1c0506120f1605090c030601180801091a0c0301050901120204020f07 76
    0x4991500e0f12600013515413640c0b00d110503030700038000b071951400c0303841c002c5081c0381d201d60824003829684581104075503600c07219130012200395605030760100400050000c094207071544128100d0b078903840c40c80d0078400200344000d41402002000004400110720b907044c09042084084010220758106550344180f000e041c6440c03004038080c9016540220302ca101c640122001d680800100c800f0320b1383c0f09003048070806211711080e40c1c00394941d007001010880602c11840760070700a82c0c800340c9079814030310883e810420650101421200401403031f008491400b04100d060690a10702044584880000909520100c0d160306620b018071014400c00200001d455161550303980d250b95035584c0d42d541000900c0e94100c83d90110b40c041000011442e42c41403140b01a40034030150011000e40d00c62000b00d007120145d44003107840c41c641c00284c020300310300d1000448d0f0021188411034038540c145808100d000394180f00e44146086004902c2d0115a40c03074050342c14002d02d80014a031078145070708007c40e8101c0c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 867727149 1250 867725899 867725909
    0xe0a09033e070f0e040501020d050108031801140a08130803091b19090b011e0c110f01020c090c0f0a0c0614010506030c0d0b09070315090506150d02090d0c 68
    0x40301c0044001480080b0340300d4100c1e002415500700c9546001120012402c0c02401142c46540c06c0040c400c0c0c00c9aa0300c5568040d06100005645900e800c401c59003a8003000004141440040010313440b0031103410048070121003c2e85416889507d4896041d900f21244610081088401004000d00ca44001507041c00d05079924500d1a89252800144942d112005c07034108502d0304480c2040c0300003125600865800c2c041031402c908516040c041900440d880b60036500000b50000034900180035240c248001850b0007101d40c7d071000070200d0000b075611490288440d000d403040b8030005446040c0c26056503401d1071501c01b07486d50344052110003003e029100c0e500720345240c640001e40c02c9400740138403864180d42004c0c110700d1941d203132950082c0554011106420079103854608ca8012901c4d280409800b030201c40e240490080b0103003014402100c0036800040b041803500042101e42e40e501c1c45200c0740c60341e102003550307038440407504241e01170710807000c2950700800d05005040c1000744000508003142c0f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 867728399 1250 867727149 867727247
    0x100c02030d111501030201090303050f130f092301060809030d020414131a061b07030b010306140c09010509010c0209041a090316080c010b0a0b120c040e0a0903 70
    0x314031044468000743e4207000c00790006501c80e01c1840042c0c0240d0060841440a401c0c4a0504408403101064022541c000613542206108204020f1000b400368160400e4003040721140041c1040140c861900d05101e1241006441c40c003240341c14100340125884040c8100c41959a0786e203c2640c0b01e0040103446101e030103032041416218150b0098410881d0040d882680b20030642d80e40810010340780c002c0d0755a13917100720b041d5480e24003827001005410003d500c00c4804560541c5581011400c8410754a540307840f01c46107104100684c03000c5012560814001d0814503115002c44004a41241d29075000a40110501d0103010a101f1142d040c10500e18000941c2c140c03541c0c442400645a002e00c1000e11800100baa000000049a42001e807903c2e1816070300004001407414005040402e06a0241030f5401d0000b558031090800180941c0d840140c442e4040e25251810708458803070000241900d0115070755880c004100b40c810a10b01703112421207044000c220305008454610000b112820b10160 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 867729649 1250 867728399 867728413
    0x3070206180d06360b100f0f15021203040308073506240d0e01060b0d0c090e0c1b0318030c190b030414030417010e120405100c02030d11 60
    0x1340031020703d4803485003140d031888041058a0b5071752495000700a00041035842c41c02501080d000c00c25011013000341054508490b00514105c1070245a00302c1c1d5404408641050308054248503d2000b220740141d414039188440781d41301542100d02c11400780707030403150440c05c160224410081120040c4c90355020030041c2045c2c1c0340e8008101d0810004c00b18015a0304003100380c59214158400034000c442c0c0358000200e204040f0b624110b0031218503401140407480c1c0414a03198502c05071250843c0f220743c60902c24525414281a5078040d007008000318018080011500e021140348c440d010402d0002508890300c0304a004000c401000890707038080d02a21440804800d03900d84080d240c04a0340c220300c0c0d86040c40d802c190100440d6840240b09a8544000b40011684640e00300001c00042c030300c1042c0702112040c070048180c25100d111502e51069800f58051802c88000c002c203c80c01c890089948a20281401c42c00b6035401080e031038040e40c10700403d0342c000496900900141820560340e030a940c1c00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 867730899 1250 867729649 867729701
    0xf2709020a050d0206090301020c010e07090c05030f1f180e011808130e010e0103060f0213051e0a0b03090106120f0204050a090206210105030f03070206180d06 70
    0x1121850540030798025460700c002c01403414940da11009a600141c521850b0005c00c10109080e648068140741c502c1c1e6646540c5050710000340321035009407180c00c4045c03000000383c0100910070f000c0602551141d07420800412000c00510f0004a080c51040420b0340e1290f6075040e6500e5450b4401440081e41801e280710b075613a90f6410b201e00514800c00c6101c1c0e055221a5485250094000d441d21011034031946801051042a119005000303011005042a841d810340c9009800d0340c184440480c2c10500502c111982624a4421075054482c107031062804103141e032111510f0f5040140c07801d504100c0000000c191110351100131032142a410001380440b5541e0780710280d01d0514520050074000040d6001001403819400564210b11400004203008000c0c0d0002842540211582e1400312811001038400905404000e4010f090481c0900751100c540700b01c081c1c0300e200d5036500038450480090440b40000c0340000904910402034070444810f1018500540200f0483c502199410302100d24100303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 867732149 1250 867730899 867730901
    0x3120f020705040e03040b07140f010b0102100b010c02120321040203070803070510050c12070c021f0e0904060608010e07080c0a030804140d0212240601050708130f27 73
    0x840c15803413000862616240801254064100030400c4650f0700070740403400c80090041000800d0f00103404000210300000c14006841d0400c440340d075059a0f410714100c1c206a80e000640c41000030340584e520125050940c401e1030952051041c4a0840250f0702c42c1040300108159440388624400c1c7d041340d401075181d000150741c0c2d00880200400aa00c1114181000d900c9034104075004014180d402e0300f4040040d5048404150450301d150000d03aa44100005610301020000e06e401031166110601403505c0030014000704146484600421210380400e0800c000355002d403004000c400002c210243d04410820b460b00030700e10031b8264034401c0d00c28507440d61904d14060f10031280d02c01d0b2103c0c41c0a2809164160541d0380007601548100340307410300c00150301c51604081024071104c011b0f0044020025507a1710a00c02504d01c04803100071070040008030790b0030030100c078050341d00603080685a5170359284401c5905800c0d08141000b41c071039180080e102e5100c1d4000761849181c03984800301d14844c410600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 867733399 1250 867732149 867732161
    0x40f0c1103072303070501050c070b0609010e131e03020703020109080f030405010c05011b03051e0408070206030603071a03070f0206060a09020a0201110f0306010806030a0308010e0c0403120f02070504 88
    0x141400b1240985800796243c1514000c03075000302601524208041c0b5150746003103580480707010344401e000203000400c10030741000c51544401c0803200d006080d4106001c2c0c0a40d600010110950000d000c1080c10501400318004410312602c6145641c6040080c81c00a454000d240f000300d02042190401164201001c1142d0041c48112001182402e2a00f0011204001214400e903625540c1d03c000e6050200510b00d0002c0b040901d880200d82ca0074040b514441e2a1001d0445841c030004442c248030004a04900307c0d5151501107882e19220388504000a050080a900400740071050040801e4044e07c108003540c4aa041c68865070f480052880b0103036160341045501580c0b02141000504c500c0305250b02421408420388000281c05030034121558041e40005800000e07001c0110030403100d580d0059800e540b11070150007074609540c0e507540141c00b000042c040d0000d0704000c01c0005142040000586c1d0003503811482c0750324200fa0300100501300105030381308030005020740803020800381890302400b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 867734649 1250 867733399 867733403
    0x80a0804150903110f011103180109060e13050c0f0d0504050c1519272c0c030c0915190206240303070614090c0d120305070c02040f0c110307 62
    0x58413064100010010205200e1580c64103000d02d64031800f007006401c001801800f1030504444c0640d611010002d030146090303900003000c01c0b40164070707039585480304644007203800e106420100301a220008200c15501440009906030b030404100c0610129003504118040c41c0500d00f500c440c41700003020f1101060b121004607021000401000604002c0d8448400c1c65003421301d807052501400021a20300c8840000c20040684410316050050011610110441c1d200103007054020100245003011000320090246801c082c02200164002c0c5144080754110721006048a078522428207c0703140a0b04140c881c445400c81800c10390781c409000180c01405416421221100c5094081e00f05403c4400d00c3d200c80d8050200b400040c0015030030f130144130341236000824000b0042c81c1c045c2001e0f25010400c3c4010380f088004904000c0400c003810910b000b00905071802051aa4841c141907908000208000790421314000300140700c03112691040d0110b211a41d5010000038134070321501d03940d0140c1c80c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 867735899 1250 867734649 867734663
    0x703090312180807030b090313150c0204062c04020105030a02070f020904060e060a020a09053610050d0206030106030b011b0b220b0103060213080a0804150903 70
    0x14404a00d100a94004441080c0b600840003181001e1503a003444290f801068254080c02c000d1041121090442d54010100002141004085000580d02480078440d01e0300240400b040c2c612124801c2ca030340501560003400501c812955840b1042c0f008812414111011000b094417400050554440900898059460303c0c1140c4884081c00002e50080904070342000552402c1001a11070b400150310a81c085e035000103002d6603007120b190810030004c0c4414600d41c4100b01e18142190021400320a0318010b40c0c0901e810780c10144801508a070b04038211410f122642c1c005c050000e0a00890340c0700e48403019001c1c002941d22000c0c01920300310400700a42c800014001400708074400c0e404003c0f920414504002c09281038880c4080d01c860381441900c41902081c108080c0040807032096081515030426105101c5150725007280d0f000e41800003c0076280c00055a01c444207015443d03001801d40c400660300710103610f00d00070849501912901c61541665a10410541d00035008280bc40340c00c200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 867737149 1250 867735899 867735917
    0xf040b0a08160806030c310e16080307121224050406060507060e1218040c0f05120c0903010c08060301050a020c070308030601050d09141606121e05090a06110703 71
    0x801000031a2021f4841030103030700449040350030348030400d000d00c20300d070100e00011910f0506141c41d0410f54480031002140c0f9070100308008aa81c000f00b15001e40d6040007503812400403064045030300da84218000301b41c0500b0001c0116001214841140c0c41000801d01448100d9440b014401520702520442000c100705200c1c1d900882d0094006107800d0450100b0703128000a9101c070380350b00790060070441c0402d044420580200342041c0c480c4070890407485c100a0009100903600800c284544180c030841d4003090004070b008500755100b55050300ca0024000d200c10252880c0080120b50b00301da040d8804c0d800d083c003042140d00240701306c40054511201074250340d4210303121a401a40054002d5042102c100301040a0106620407030b003c55110300e0804201444031001c0c10316018002c1d49020003100500800c200703d0307030800c9284d003002d4803900010440c084e5012aa0140368060f241100c0c0701d0f0b041408020003450042858010f140c8951000c000b80300640703000f40c0303550003003c0e40100841c50a03d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 867738399 1250 867737149 867737173
    0xc0a0e0a14191d0303180d0302030c090d020a0b160c0509090c060f040906090203060102100e0d0c0503070b090601180605180a0905100c030b0102010b150f040b0a0816080603 76
    0x82c1019840ca062000c00e41c0b900f400000595107150700450b000100100200e00326490010203105443c21043d040c5410b41c02d500382101940500e01c19444420702c2595000c1c0305c81c04544501100d0001003049410080c2c9400100501186220501c2d00444212800d600c0c0400c0d10725004060358082c2d44080010407403e080101030004942c0000c601d40c580110501000946410724050320740504581c1001586904150002910f44500800c1c172040b442c1c00e1040340e072480c0000040a202d1820705140c0f205910328942481401d62041c00009400c801c13006040080c620400544079040b0b86001d005030743c0031000300c1c442000725442070150a40c045100c1500e1301031449034182a40c0c112807141000558240f00d561550300e0701003090b401c89051503c0300701a68465404d481400c4044000b800240314845000b0b00180310326800c0241d25091150208403510310000400c150781c060000e42000590b5030840360006801c0301000c40e41100907061601020b48960b208a000d02c0c00b41d08081c00502c044a424 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 867739649 1250 867738399 867738401
    0x70819020103091506080d030e010b0d02061606150f0f030302100b010912141204050a05040207080f030702070519180e100908250302100e0c0a0e0a1419 67
    0x15880c20703038120014001c0d140c94420284203540c001c0c01030b00d00501f40015105005000e4440c400300040960345000b200702c00c0e81c6ca4032140c4180d121f6040700d01d0390341c545401c800c01e015102141c8000d810f044c40c043d0f2601b0150045200c400949901030b225044650760f851714002800c1003400001d0040c0c122041075146c40c0126000b083e6a10310504103005030545504881c407411403819010340b03031601c8604400648543c10300c900c00d80068030491141c9010b051001043c403080c001e10943c2e0141342e00103064802e01c07403a1000e1b140d145442400042d81c0e4180010005d6403900c0d98041d4620031550150103004c2244a020018100d540340c1641c900c001401c0b48054000307065644c001c19403805414009046008144140c4001d94807800141d9110405440203a00320b001c070580c10958240c01100c0e460200340c000508010382100d800011a4458403804418285a1194581c0307030403c2603840301050342c1480d1080710344940c247c00e40400c20715105681085e1134850655035000703050307510030103594a4022 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 867740899 1250 867739649 867739661
    0x21305161803170a03050705040f1403120712090605031003020d020d0c2909032a0a030b0726071803120e15090120010f0f0b03070819020103 62
    0x49444072051040c2c1e01e44072061009800ca402d101d501000107561007469801d0310600d0f8200c4c11615103641842c0c10b04020f00c41162050280518a0710381012a41c1580c1d000c200744940090303030341d0300d00383c80305407524107414400c1882040201007280c1920103c0c4991084050340e20400b4454002c00b44140345400b48030000400c2e010a81c3c1140b1290b010f40c01194968860800500c0c0741d1562100501510304103140348004a80305da03620400405c081007907a50300140c0d0000301c940c520960706000f0308598000d20000d485060031074229009031400030074401080c40040c85044561540641078500d0704807540d40c1c0c50076074480ca402566030408200c034148114410518580310545c903001160300c0e925001d03000071102d40e0303400021708004542c1c0342c941000d000c07914260080443c51401e0240040000c3c2c10300141c3c040300c62840003132500051000101b500300500c2035205c01000c000803521001002c014209081c1e2650103449106000100110001060492220f0742c46813101140901d900441c007400c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 867742149 1250 867740899 867740927
    0xf1c0641130c110c0126091e010618020c070b160b0f15010c0c0e06040209060d06170703030e04020d0b0907020601030501050115050306130f02040e0402130516 70
    0x600751040c030210780e0701c41c01020418a0720781a450340c040180b814506100940c00c2d9040003c2917807540e1009400505d01c0320354180e829000d06a60b55a808a686810070320300d000c03100034810b8114022101c10660000d02071b40d101c1d0703150326101554800640c09910074607400440c603501c000c03000c1020260300346c0606064a6840050315030500661242022060161055241c0040600034080c11301080300311000075080030300b8140c40015031501c42100410b450b2040100c013040681c0040c2e5560b44c0c0d07604452490000400841c0c0f224100000200100480e01912004040701050011003a50003e1444101c81d8503035030b206040000281070101079041701101d5100c441d118110044295905e0000c0d600c5660302c0c1d2f0060049600d5818050700f5500706034440c0e00c001105a1092032030503400303400c4a030b0005081d5402e0203103c214036440002040d5106080c41d90380e00c08100800e14002003000e440c0150700807921030a06e2629010290200e44c2c041d107403c000440c3c4880c40c0b8400c00d01560350064101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 867743399 1250 867742149 867742159
    0x2010810170708010b010c02090a09030c0b0408030a06050a0b07060f0e01090803090c18070e0307030b01080c1503070203090904110409120807020d020607050f1c0641 73
    0x25034519a0010099407000c441e016a08601030600484900b440740c071088103801d11341403280132800e8000c904a04005062404001d8030b0391500c0051500502403908001c0d446260a01c0c0c91911b42011040340d0025121074040d1403c1c4076001507a45001c0034400b00713480000200314504a42691110010941d1003110483c1c942c07298001c1d030f0081c600303100d90700d4020f004201d016607a1504005a81c10107400510f803500c00c621000b9045400c09002071940c0d0b2242950812005204180000903c7e100603540300402600301e80001050382e020110750541994001d49507038151a540350541401c80c04111030f0710006a0090040001c94070741004003980007409500000400000240410f0a50b02c15002c2070360244a2240e40ca42c44070343c8140d10942c0030302d8a10260850001610340292285800740a0400b00b040203d81410000090001c5400d03409100142496080007940071801400c0d0900c1100c681110610b00306466420f0f2007240045101118461010b0980c400020400001d141c44226001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 867744649 1250 867743399 867743431
    0x2060703021308070b130902040b0412080d06060306080c1f081b0a0e0901140d2301090f03111501301109070c030203030a0513080301120501051012020108 68
    0x2030710701403103442e01405c1a50306190340ca10420401c1e400102e840d510190742c00d0f10401003040044055000c4d1410303180705840c2d9440c02200c0d4144220340e802090b8031910000d28101002071450f40641c082c5084072180820b440c0c0d0320001ca0100503660b0f074220112662002840e902c0385c82c032845405c0c2c59600008146120803503101c0d840004400d80c00412036440460001c00380f80800b8580400d8482c018040f814209080c40940c0001c100414a1010020400081c52a2448150110640b01b400801303101008000c44001810180a2228603003800c0d00800c0fa80d450940241034081404080c181d646241a01207900c3c00341c9407254100390500c00c07050007030b12410300e5aa490451081e440c0490040701d06a158042e10820483c030607e0107407041c0140505e810782c980002c1e4011096aa0100007200c0004031a9200364400303003403040c0d40400400c800400000410010511904c0150550160008000310b039242c0c1d010044c50380650103000c1c04040034002c3d030401980b080d0080c543c8040e550400e0040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 867745899 1250 867744649 867744659
    0xf04050702070b041e15020c100e0d0506041a01051e010512151e030a08030a110304030f11060c07020405041502032d060a0b070311030a05070302150601020607030213 73
    0x15074200750041c041d620b2602200e00c100600c8400031700f01509080d0b07100780030304a0b036040c040d40d550031001303501d40a15000303200a02e956000700c241911001c800390625000070428504141c84003001c640441d8200c0504c1001e0580389000c4015505848000d4a66503190842c494001c80d10801240c20385d0400c1002c00c04000c242000080b810700a54032148090b00c90742041082080c1b810420500798001104500940100da070f0000d4006009070300300307000d80d60341d450b40300e1807201400c001b808450214800005000404d90301111140820b03005580c0c42e22480d407100341140d150342040d41c0c00c402d40e00003030017204058549948046c1c1c000c0c1c45140c00841c29008143d41400360f0f00b04441d004034510417200c0b017942501c0f0044a44501c400d1341c401501e0185000c0c00016403094440c0a1004100da0100b609010035001c0c00c2c0d800541c2002e40304803512035a004030300400b194841d22085005028042c0d101d00d403040c0c4400340303a026120580203820340b9520302e0400ca001f500b0407400404820010000020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 867747149 1250 867745899 867745919
    0x8071208040209090604080a0309140703030f14040e01030206030606121f0e010b0301030321020d0b040e01051308031003020d0f1b03080d1104030204021206130b0f0405070207 77
    0x1001856151a0001c1c58140100300c0100001884503000303411003410080020780c480700301c13800d01d41642400900a00581081c18451042400b800990f101e81107021042c580c00030181002841c40c0d03600c04003100c02e946906082030059108910344d001c03070000148014504180990b03842503018120b0381c105400100c9002003041c00381e40c490040145003403129000c580200011001c1d19505503080351a500d0b1680700d0ba0745110510014080250304c0361003003406a00c54402441c1602d40840942d01d400300101503000a02920101c50f00c51850302107856141981801020b1284180410b00d2084145070740329800b5907440102800b140c41100c507800300050b0381700070030400c1480c080c0803074801900301803900c104c60045004070792240031500a0104006800710048804008490b9030120f540768410900c4005405640c100030b5001c0e0010030310700f24075562030480d10f10818088600300321400488201504a0391a1900d05401c0840410312031180d04150300043d81295080c41114580741c2e403a81442c0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 867748399 1250 867747149 867747173
    0xa1e080f1206090702010e06040f0c230a0f122012010203090c0a03050d0c03050417031801033602040e0a05010c0f051902011508010f0f09020315040807 67
    0x80501c0040c10a000290900d0144583d201069000030400c2c0d10051180c20b644e03040040c401415001d803070347e01000308105d895400700204001880900c0c00101400c2d480d00d240d2a860580307000710000340f0001003100910b9000c0044806040e072808810102c8d80301d0050041d00d950188010400000071090540c84401c10340b500c2c0d00070b0400042e101c0c2459078440303040c401d55a410030700c2284900000c0c4003040c0d000ca0207100362619400c1144424045160544641c011030340300b044001c010307030900b01040d0303400b1006104003007130402d13000701440c18800107400321890000c03441c000325101c03208000340c0c01c22118404615044200e088801080c2c079800902a210303644440c08190300310708626003c1150900820780d002080e810901407848481c40c0080c0702d8000d00702c260f082c1d0241c020390421514002e5210214904c00b440503403418030303107030100c1074040c149008180649604c3d01d6400300086c501c600c54038000550040c06410003400c0802e20003140b40c4060001c1e24203102c10050080010b01e6100e0760 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 867749649 1250 867748399 867748417
    0xa06031401021201090207080a2015160f0503150a150c0b0f0f0f0711070b2106060a051c02070f020112021810110a05030c0c030a1e080f 60
    0x26a442203c03c4070810014410b034860f80106005011140000f50300a090340c8072202103103492004180c0d4150501295100c1104018803401521005e0152071401504203105001042410b01c2c41407820301c04031002d06107490b851000403c1400403907110040c00c408008a030700010022070007941c80c0c0d1026440c40a80820803400304011072920801c016001000c00d5100249010b50401071402002c100c1e101d0b02c00900000c58229039600203580d942c007912150610b07185140c101d820182d101d031340ca04c400d940074820391144c2124402103036045800b824459841000040c0080e818404c02080075030301600003d0032501d010303180011002e04901e003480542016030081d500c03100c09a11a0002402c91005103042c1d40c1410700400107a560301c0c0c0c52a00941c0000c0c01a2030300414410040c80449031001010504076807030240c03441510501a00002a1181c164901e090b28a40780c40c0804260343c4030107803200100800c01c00414bd15040c0c00c519150240c907800341754801d203803000501c03c599056000b40b0f04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 867750899 1250 867749649 867749651
    0x30507022e061d1e07020c190b220519121a0702010938151909050c1306030b03070312020a4b020d0c03030807081e0a06031401 56
    0x42004200325400100d240700c1352240101c1d014246440000c0d102c01d408502d0318014524950038012955044a015006203107007000c0c1520303039440c12917070344a00d80c5044580161090805011840d4540070440e0410240c1001003200c0840c54a5060010207143c4c1074180c1d400790b5501c040c104040d60341c0b0301c04c62040c0d48540c00044c0d11815842e21008440010903500c084541b40002040b4443d1051881c80e03c0305501c00050180d90f803001c00d039001c40070890240c0f9401181d0b15800c16009007190300c0c00816a50004001d1102e075071041894036280c0034400b00404003450001741008440e0007944042d04d041006000e56000a841c0c0d00c40e82c42006480e48000c0c01644041d10010030b000740302c01862484883c0d1030165442c06844c0c1d050600d500704c0011454407545e800b181a8a003607080402c3c81c1a0b055002e80300c1da40c01003850070072010603403003844150042442107001400d45c500c5456068810401103c1c10048452685854008640c0081071082c84c00d41c2d44401001158a140c1400000e10710400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 867752149 1250 867750899 867750901
    0x4110a0f060201060801020a0909091b060e1f051603021612031704031202090d060609050711030705030403120c06111b0f1c120c0f030507022e061d 65
    0x70000d003110420390100100381d1041c0b119203945ca510007d4441210300e90341c40420044414205007041d80c20030411043e95020441c0001041c0e50032021001c806801110900e048114081d981c1e10700301c6040300c1c16000113004000d42c952000c002c224800019000e0b02c11115440341090b001404000319801c808005841c034400c0c0d10415600403d016100c5a0a9004019504084d64068021a014641c41034455000308849910b612a881c01400180c0c1100c03040c8690b907621450071009000640d071017000035800d1040c00c5820030f4000200c60320150302600640c030349451a01d076200d426808500074810000b8414038100030442600a4801340c00b03031802025650104e040340c4422140c4040c16400f910703040400074521944001c51394481102c6182d1520130344070054035040303d00c0c8901200c01d002840c901402d88a0301d95100d9550092140541c4003003045032105a42a6580c0c4610001400340c8603800800885c6603002c40c170b24103a4400c3c148000324010743c644001400012010f0040c4400c1c0300880 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 867753399 1250 867752149 867752159
    0x2c0106080a05060409020906063f060307061202030604020c01050708061e0a090e010b1003021e1218100e0f07090c020304290706020912010506031504110a0f 69
    0xc4902c40d00078400b182c0801820842c0c0c0e01090603a0801007805105150214040040c0001000c400ca5440300440311000505401d00104030483c1c8005d510a10b84504070000070528140001e914080d141380e515400f80714070701c0d09107400195000a04a0750410b8090102903501c2d0024005c45001e0852520b6200440c0b6181091048503030110390b500c0c000c90b21308400303041207840e132035100e40640e44614000310307007000581c0c2282e025026030701002d5002500912034101c0b41c1d0f0305501421421080707140120007000302d828140e10902962405030813070031044010907140e9032050f9000080c0256041501d2000f50b404803044c2c200d9200e180c20103c540c00110361160b2480041c4402005080d9040040281d003500e040002c1d5a4022801910018503000724004180c0410020081d001c05142482980e212428030300f541c0a50041e1070300a001c0d00086541c0d8981d9103041c021b051040302d0180040050034080e00c0d981c1700c00700001d001980c10042040742c0707921a48800b031041d00a00032020520208a00d04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 867754649 1250 867753399 867753401
    0x601151407060e07360b011d0d020a06020615040203070e060d09021c03141908151905030105060a080d03110d050106110f07030b01050f03030c010c12060602070803042c0106080a 78
    0x4100c1d01d150301d6140401d0f44085a0304230900514040345c1102951054148002003001c03600c0c4900d020b90300141900d0000303043c2d6800960380d44114591601c0041d02003141d001d0000341d00064400c600441c000c2c05480b4024101174001e04606001c0c080040b135507000c1900422410312000000e0011788007050b03111814150040b0100e05030100303510300700d86040030f10a41900104075282d00070082203071140c0410342420b030000500d401110001c200340032049001650350300c4010a0306c1694040e5007000000350041c40c00a0214044500880c0a0110f1260402c0d00f18028101420b04020080702804a88a9405130b441032038080d040301d8454000da0345801c4500780c80c151202c0000101503100c03200c2800040c0746207800300e0460304184c410840990303110001a0940c000d5600c09203403586009022108103a0040f2050341420302513408009032901d44404036103440007400380304003030b90080104000b04404101c02c160380700100c8110030002449030080c850803104c2070b400030b000640808140100342e112 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 867755899 1250 867754649 867754739
    0x30b1f0b0903121602151e040306060b13290f0901080f130201030f020903030705010501060f02011a19030218190506010c20040e0601151407060e07 65
    0x1055284500301081803021940d80ca01044e0024000c00c0f8402e0055844003401e4150b03620550911021041d0700c01ca04200d18694003c1d00c010358480d070806400040c031019000464004003000c890340e6440506012036180d920105000240c0c2c0390050f1742c4c0c4002490140320141000180740071a82c0d58544201c0d0004190110140c000c1000c040d10400b444011455003e041c0b0201780d080c00d000c103554100c411003500034014a0102d83d050300000809100300318042d400325068030110f80701d0020008074610100d00b210004600742c090003c0b44005108249400d00c100000c4140b9038085030816a01c0c1d80c089107460140341d07007c0e1040d0140f0700a00c8500ea010400c1103400400c04002000740c1d251483c0020114088060050325648480800c1824025a06001721540354041c00c280101c028107507806584e000d09224078800c4040d00510b88640c0f92044c03803200c04025000e1401c50030600540c075054001c0200a000800038402c0000014a281620001040d44058180da26548109149105141c600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 867757149 1250 867755899 867755923
    0xb03034e070f0e0a0b0429070308090307020d050309030d030c0e1c0f080d2003010e060d0501020406361509090c0503160f020601090905010b0301020f0a27030b1f0b0903 74
    0xc400e01c81c7c0800415400f610504c98151410b5081500d13400003003070035440b900f48069008540800c02c0700078010008000c103400078040c1e044403400411100100c04a0344e0f4542c0d24400a070130282c06200300d00c0c0c000c0c1d0a240307c1c5c0c00d0008000034807049075620042d00010910071209481d021901d203241c00414800c500010341c2c2d401a01440c00c1e20782885039020b10050196055501c000004140716845211411148030350002c000c650355501e07000050b010f005406d03000c0c040ca004000e02c20980451030314515a0360003e41c0c966800090030034218070900280081d96504008000b4000076401e2a40d0180041c081d49984480395a820300103602c2c00e070130700c429101605005003800c1403a41c480d40061854112207500b0b10010310740d4414074060b8003402c1c1040b04c0540c5580086907005008034610700829520b5400d4403881102007950350305549540b10741c840403244d01c01c1914104045048142c610b40c1c030004c1c0d071450303004551001c0d600c12425481034021059035a80402c3d07001300e90a040117640c041078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 867758399 1250 867757149 867757199
    0xa0806090112080d0c0c0f0602090f04020f03070806030f10090c080a0b1812181206010f0311011e09080607021f0b03034e070f0e0a0b04 60
    0x9105480b000c00500c44d031400c4101c0389580c2c40c01c00d00d0b5035118284401c0c44a500101540d4541c81600b01980a908069682c2d88118000e03101c0c1201c51400303201720b404020b180d01d10a4150358840f6410b40d581c5e0001400c03135400d0701441c2590110100e05129140e140d020023400010f0031415070500745000e44068100c00c0c000e50088040d01301042d0041091503201c0c0d01c0c200d59509901c00c50400c64201805800c07001411b0001281c09001002d045c1070b12500141c050b07a04440c903e081412541e5200401c0c800d022030403030b90313a2007800403503d028940740c110941030400d0107142a607101000c98103e410401030f4005400e21005101d0480188142c9400c020a840140b40009201e021780320081c8123460003504940d5100100c00484d20240300341e030001a40d51080440c42c88030300c00383c040b0150b0880d80004187d00901440f484802c011041c01c088213101044071031143e03940903020740d2441486911502400320549001203c1e54031415460f002e8911030b00c26503101c518058120030034240c04003c2050316 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 867759649 1250 867758399 867758429
    0x121205070c0f1412030a051308041404150305010f0f0204050117040c0806011503060603110d0509010905010203090a0c05030d0c031805042315010503011215020a08060901 75
    0x80c0c0e5005011800581e00605010180324142c504100b040c80e680000240303500481d2940d00c540448680654442e061100080c005070351030000c075881c8400368040c0145080828881031014061400c065000c9000c05400010a0580000604448142a80200c4407691940d400003091941400b82d80011021640190b00301401c142c0041c080d804a0781d42c024003000140300007000d220711030100310003d10400c015900d04e943c540740b52074251000d840410340481d080034000200d50b0312134464241a800c8407600d490915a0003041c01014100240410000e90340310b105690226800703100a40c0a651903c000703001d00380440c80c0c2000100ea09508c024442c1d0082c20203049040e81004024a2040d03041c5401140b465502c648210461100c1d000b058100707103801007500941060742549044c0440151001136603603242400d042d010403c042030700e0300054040c8010803100102c420607400e00c6104000d85200c049000085404a3300102c1c1d0307020000701007000380030090034282c0b50340e4003401807081031240d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 867760899 1250 867759649 867759661
    0x242c1f091e1e0905010f1a03120a050d02092409120a02090109020c07030f082703100b01030603050a060b090907080d082d040506010b07031e1407121205 67
    0x12000d5403045070034450340300c0040c4010080294018240946c92000421030303080030200320140303804c40f00345042c000d204540303c240b0108541e4007a28200034280da9141d2815100501c0070001c5e4100d4848140c00c1641491062580701001e48010000e0900c80e8949403990590b00801c45614aa0420125140c10464011002d600d4142030b40d0305444401d540960384002030b00805141c401544e102410711200581c00c0300c108000030000f440b0f035051102040800c80151005140ac82030340000044d4160301c80c001881e400e05803600411016681410001829580c3e900c50300d040c40c0f407002040703a40b107584188186051401040c21908402201c00625109041c52441e82c0d99004400ca600140002c0c5000183d00302c4a0b51075106c482c420245084660b030500903048040014203950495041c094800045208840e4809a0b130043d601980c80410b4101c504009000c0408850345241c00c025162009007088580b40c001407003403d120b10540e003000c80c40014018142c14143d80e1580b0068200030038041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 867762149 1250 867760899 867760931
    0xa031e06030b1515030702032a06041506090f090c170a03050f1b0114060102010c020c0603092b020d08100e07030f242c1f091e 56
    0x380c08074400202c081003500f944005640640904c1c504144c9080c008104001254048050b00d480315074400320305200c0c0e0600114148a2050885480315a445040050049240002c8100d806003e06400040581d11200c600c0190b42c0c80d65070501825440341c5200041004000200b0001c00ea0100b0040080c81d1920b0000e03280c10138400041c040000104014000d0002c800c1210240c01401ca04c0541181c50003604a01a0201c0c840d04c00c200704c1c250002076155401800703140c41c06403041d0b01030a40740c4000c500b0054160000341192a071882101060302c48501060b21042125102405902c0d11019200700246403491250021040280c200b040c4400b00d481141d0103429984800c0488819541e051070440c01000482100d803081420711b40b0540761410001d503812040800400c01c240d0042d111000090842c1c054003542c50a9821120711108440c012046160484110411481c4045a040008042c19080c8d008050702550301e54040c0340781c411072040318050303609082c8144001458002144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 867763399 1250 867762149 867762151
    0x212060603071704240c020730050313080c01090504020a030e12090a050a0803091c050d170108061e090a081305040b0603090606010318080a031e06030b 67
    0x28051000071001c03030030a5000303c00e000c01e01e41030765030f9088483c40c0c2800c142c0b04841011407035140380f0042c00c6503c41081070500a038121403a0a80007001e2503403030700c1000c1203503082a0722008142c80c00604020448032115083da1081809034004546400c90041c4046c0350f0f040c01e50114443c1ea200c08440340499030081c0f501d0040380c2003120016200d020105c000e402a02e4407001060450061080c42440c4150102c05000d0000050b15080340c09515203044c00821945402a9082a44103201c0740d6407524280903c100a0a101c440f903c03803880c12070b0307111807403c0700c1c6406a00100e1b1190b0400560804d0001c08135005144a00040007507003444840c05038021440c4030704190501c01c0703d0000e091100c0070064225031076400f8000039a601d840e0005e08054882c103019180c030507424400c80c08190b19042003628003a0804030050115602c541e401500103291118960340010342d5501454049003031240a41120f1210351404140058101003c4400c081c51903507281a2034038210050020814400fa02 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 867764649 1250 867763399 867763411
    0x2060106080a14090f010b0a0e010b070c0312050a08060409030e100509030d11010b0301090c0e090c1c020a32060f0412031205040b0a020304031809090b01090212 71
    0x1910740c0d44a0840590140944041c0c00304580d525038103100c591203002850844506010000f0010004490100681209544192004148010300510202201400400c0c0c1c1c07521170107c015006503a5503440752415180e6880700045034005c28402002074209911691041048400300060407032940c1c06080c43d041810b031030303004101c0c1c0107200e0340044c012000c50f03600d20001000c070341c0c08070019040204420328424a040d155400c1801c540c509080c1409054529a8800c001564050404128148403000201005402d200d8640407012a0712030404500d8461042c04201881403202e00611442c0c140c4d56002c1000e0400c80f40ca8054031507201c080c80c1521f4500d0300715500000c40b040c030006040d40200d00e0581c24a000028000074000498442049130714400e40b9204120340c80c01800004440003160041c0808100d1400a2007032491075005650040c442d0408880c0d8485089080d214049540c001041903941d40c0000c1c01805001001180100780381c0ea010b41c50203070b17114056041b012000e890 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 867765899 1250 867764649 867764657
    0x31b0a081803010f110c01150e0714091306080f06010503031804150f061e0c0b091e010c020106080303060f040b12011b0921030513051c030f09030302060106 69
    0x81d06400799000c1d000740d0011984403030f06000c1000b41d000c103801507074062046c0c03150961070400c100d5540001844800101c840b42c400711811a80c40e03034002d82c1c401c00c000c207042201880422450709169240c400303202c164002003a001584604010302149401000f07424a81d591340300400401495030000111103021403400c480701104275010010401402004d110301c51415400100400c4c055100721942d01210b42966840034540a1102c806c9131110111103241c00013048202d1140224110302c1d10560040200c030111a003003240064a4841d65060070340c0020310743d448004070f40100d9424000c50006d451004088c2d49541000c0e800103084c000c211101c2802103807542408540741c1d980041a04044240e100203200700074801781400c1140300c0d80040680855408080412100b4401c82c070200030101315113500e91280f0341b50b00d06032903a400010300c0108041c0c1c0c0e9038001c1580d03100c00701ca0f203614920003500c4000c210124500a829015090601410440d81d100c040011950000708181100c0d91820 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 867767149 1250 867765899 867765937
    0x90f0409261605010f180c120c0905070306061211040e04051c0e01090605040b03270d0e04060501050304051e011814070801061401030e010905010e031b0a08 69
    0x9079041040c0a122907510000305140c452005001d0190080b15400c828800c04105012071122441d030b6180025001514007490304005100310350100d52002041800340d0780035080f0665868814096540c2111100002030300c0d014200041a00014505540055080700380080d03108260741500704d0266204514905040c41d0100782406000c0c031400d1440c0099540d01540200783c648060800c40c602810140018803c02c00000c1041c0b054054400303440084036100d2950300e40c402c00a02544040780482c6042074400540c0b451004104044c40c603100c10390700c0318030354401d01a00308021030b200c82e40041c1c1880010010880003c8010403ea00d89031601880c03032600c40120381490340140f451400f079131175581c0c50b20480d02c1804422130001d8a42401c2408450304561980380007801c1e40c0203403203001e4007900d01c9400c6c444c0c3c660081d0084d400c9103644400018065103c0e4583c1825200b000c0202c0b107aa0f0800a1190840d0741d03000036409082d68180003d004040555541200521030700c0102003015200003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 867768399 1250 867767149 867767213
    0x1602150c0a0b09070e010e0a0515100c0308100f0303050c0703020607060f0b1905040c0e03070f050907030209060706020f1303050c040c020106120201081801050c090f0409 75
    0x210544125030403040032101a005245000d08540105a414040d40d100d58800012220000d181c014140c0300021040819512005405000741c100074102c004203045000b04034055440354003510110a11740d64540c0341e0b41149041c080c04503d806040381d9076000d0941c5040c0030140c4000380c10811243c0c9464026174458070610068140403990300000c2d4450f00008584060120507042a0350718510118100005602c480411030f10124081c0c5048086816200c100994601503001258004240c20401d50b20444200001e08040c8950001950505029010300050034550a03503680a4034900341140b03000c0c040c00015181d0701840c24010f100940000e0144605144e81c4240d44200319800309030400d558980c6401c1d03440c3c003446500030340118030f0700122040541c414000c00003141c2d101c2c403540903072014036001141c910000924088030041641032441c003025091003280c0c0300d02144040c0d151502c906c0c004011103402d600e403400c2e210b54201401030b0041a841103100284003000343d071811031b0f07100007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 867769649 1250 867768399 867768439
    0xe0a080304030504121505150d110a03061508061b180609100903030f18050906210106050f0103060b0a12060b071a0a0507050d05070201140c090112021602 68
    0x6031700b003120781d6421207116208004000402c000c64501040c130501403591030404001c0500d40060100340d111191644010205449c456040d0240380301801c4858070303c1d1a03480d5038080e0340b6200c00c10740c0b4241c42c02400b000806400d11403980c2051584450f040d808441c0c0030f02c8407041c0140031010f05003400500084007203503501011a142e240002d042c80404182c0c1d510003070a4200b20303100c19000304035100d0441e103103a446200c00c1c0c4160f1100200c0d003064241080c081c442200001083c554008240c5041d0442008010480714003080b003060001c1519400e001c28010000400300019060509022060260143c1d00d420303111480203602d080180001d09038500030240c49554016240d502c00000c1020a1024041d000040d901407445004a152141200705045030000c882d6040041d5041c0b0040000e90b0190300b1441d0130215610010a44e101e07000301c807051505058481e52140b8a00180034502c03940c005084002c0c44954060842c1047d010b02001c00c101e6140b12402403040001030140c1c918400c0c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 867770899 1250 867769649 867769657
    0x60d020a0201270b010503070b0403030c020411070c08010605061c1e050108030405011b02060403031d03030a030209121612020117070302090a080a02210a020409150b01030e0a0803040305 82
    0x580341041144140e000d030080c25101e100c403c01d4030301800c03910002c2003500340000c60604840e421001907103030500c1c40d10f0407981c0015845049070b206840d02c6403920441e64000207414094040c1c802120078514082c442c50869178140d01c07483c090b035800c2c0300181e00c024690baa03a0720468441c54000c1181000142903400c000078525450038407038901400030440342c13000005032054030001c0e01d4010751681d01548030017601c001746038001d6014200f0041840028411004d82d9903480901c15040790400441c00040d081da00207000680020b5400b192402c0549818410307903649001140162081c50000d40900401c0042c074040c04a06a03500d0242d40c0071a4802d05144e201960b1480c04000c0500b04084010040e50203900081e100d11a06103004c07a0380c0d4000700764125180c0d8010108800300a0f11054211540c00c42e0040e00070780d00480001c1c60158540380a0303e40c61500c1003001000380760b101400d81c0111005c0c016003034101440d010409403a000c00042400c400ca03000000140c0340c0d9a20724040302d603881 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 867772149 1250 867770899 867770921
    0x30b04020d023a02300d050d1a0f0423040c060809060705040e06150c0d121512020f1509151206040f1b111b060d020a0201 54
    0x10009001d26050f01c10500482c0419510030301180003001150004010000810b40030754410126480b180704000510400d51501c040c0d01540040b01081e5180302c0d040c10284070424000c01d40c00203100120719000d00c200c1003a0f000030719100b0103400c201004160300e20009035800740215914194481030a0a400816607503895070003108490780791511300305482c00c80520070b84011410072408240340b00c002043d030f240304120b20b68490b400d091405887e140368034405060a41c00c518000081b50072103800c00b000301446201c1c0c400604281c1c4240200810281105a000a00300d1a0054801220307090001c000101c82c10f03203580580000090002800c90b5440b8a0103503440008000a580500400e001030482c0f50740840b840c96803400c48c0c01b40341480d4454a500c0c540c820040c00d00281d11454240d0044500c4052078000150715406080018403071040c2442500c0400c0d5074814101c0100010070071440801900410042280078000c041546030207083c142900340342e004941d10280074401d500000c6008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 867773399 1250 867772149 867772159
    0xe09070504050d1406070c021f0909060306020339090406080f0703060c02010b090103020d050a080a1d06090f0904051006062007050102030f07050f0714090106031401030b04020d02 79
    0x8500e1400c500b002002c4005000e0500805c40003400c0c0d1805018491016900540102c0b009100c00000704820712140f01c0c0001402034a010100c1c01460764402e65021303510071040143d480c00c0000c00350002d42c1003002c4012001581d06425135004845e82134070441403070301c41103294540c10b50100040180045402c101c0851080c1d112844510a00040581c100ca024950401c5010500074049090321820641c09412080e120010401404e10020206905000340d003911038102d0170b0768070307108036611414900d40051503190400c003203042c408a052860306411641c580c581200708000caa0710844003566248120702000004090207001d02154500010104080082c10f80341ca00240c84900819840395851442498034400e11800095050540b04160001d5003828004403500c179955210410881d01405952180041002c1c10003d803400b82c2032000c1b540c891224103205010aa200590020003014141000e40290010340703030f1803506480c1c20143c45075640e5102d0020580001c41401c0c025000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 867774649 1250 867773399 867773419
    0x5010f18170a022701031202010e0106060f0f031b0c080c0a05060f0a0b1e01030204030203061e22081e0304380c030403090305070603020d0c0c030e0907050405 70
    0x341004110310030380602c02c48404048a05404840c1d09035807428061350b00300e00c0c80100610109000340f4846154001601c00461420241c00504c1d094940d113500240c0480c0102a40d14441c5070052480440f032642d0303140c10410100014112005140c003141e020007407007100d44240c41440342c800b0450f4044400d40040304d41d0294980703002135540030111070380460440c24030082020600c1d81c0c0223980d0550f50050a0190b0303000b0520703d0064407080501c400381416800c220010040c1c50070300c400b51044a030480c503444070000100c1c68040c8640020032940d0400d0220301009441c1e205040e0040e0741507007000a0305e8072660806045410000301800400d41060080300304010090405902c210345c06030381500241c040c4c1210003189202095048551004140000198081030380c000510703030150080c07428040440e503a480701414110203401002c0000d40000300284480ca65008903c400c009601e09040d4009613502e008058000445003540304180c50404146020701c80c0741642c02414008080c1035072 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 867775899 1250 867774649 867774689
    0x1e02041d2d1b091b0304060c030e0d0504090b01030216081e03011403010c0801230d080c06070801080705060409051f060e01030e011116050a0f030905180105010f18 72
    0x14020390700b903445043c28000040c400d100e141e400715000c0f0000c1c1812400c50b01da0f81d41d070303a028058980020307080580d6172041c0130840b4400c10000c50507241030f844841d07072075090170340c128261740140060506160041154005004003003801c842940d81100c5a1529040390129084201440d0f4045d6010440048000710301000880c00800701540114000c22402e0b0000030184d2383c000c001d11581034200b500c9103031080d0182c3d198402004010000304503424044103950784a0440d00f100303540c1c107650341c0804208403903240c00c81e00b654094140413000f0031f40703589854000385940c0b00358020710044644a00104485d100b8200c007640c00c541c3c5080c00044080d840c0d2800402401440150340d001a081842c002c0030343d00188070300e10342400843d100d42d16240b6008268600d910007110129110712032020000c0114030960400660548280d494901091400c0100110352590b000120086168240100001d07a00f0018010b10601c043c1460304d0548501c0c0c110300d0f030320000c030b0740030301311f80c595018402e25 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 867777149 1250 867775899 867775933
    0x1e1b030a03060617190213050a030b070909020f0f0702030118080d060906050a03060c171f0b031e070c05030c0607020106061107120804031e02041d2d 66
    0x81038500b141c4d40c0501a004051510201d41c00564590b604460340c80d6001c0b8600c603841c1c00030f14008000d48888003c6603518004181c0c9203009a0003903944100c40c030140a8225031283c045c00c004c00c10004198101014040b441407144503005206500c031000084050031910b00303401207064000c80c807091886450f400e080650b080d505c007120107114240340030408194144e05101d4072054400252070340e0000360650792007500a02400011505100d03504034420031203060214814440d0001c3e030320940c03680030121201c85200d0815040074000100034020000c1003042c410b148803414413a100ca050160702c40902c103031021451940060158040040e4a185000c1c00280041c01000c0a074001c1164590711001218203007400c07102e01d40e081d00316842c100485038403008200b030014002c5040c0e80c60950740c1e5440c803006290020b042d0020048100603d007c4d4542481969164644404404564440e540c0e030300f074950000d821480190600040b0b8041000c041028004607038000c0c1d030807145440440181c1c61 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 867778399 1250 867777149 867777161
    0x18020405040b1501050a1709120d0c02010c03020c060a4a0609060a0908090a080f151e040c03020415080105090a0c03080a140d0b090a021e1b030a03 65
    0x9100326840d20403d660340d5200b2000c0b00c0d003400c020340d200f0000d00802088200307040401390a524036403184410000e804c1c4c52180003092810030f98000043c0d00300c40214080d007034400042403481070500c180003020020001250741130744200707007840000341c1c0740a901e41680f6a200c019200d00712860030010b072804900008006030301184510f1a24070850304074002e0940e07226070423148040b250300320714082005507440e904030400843c459199107041c5140040454075224a641c021916940410a540039024051041d6000d100820014071300c50b03e44600e10f011905110305001182808210000d4240005503c0c404c2c061035000341300303100003094080081c141d8030684c040c4a00552030403010a071558400551100311503072001d03444480034034603124102c8507003202e1203084c01d10101503100c10180c035850000f411169040b020000710881d80c8414001c443d0001003c45400902c101319402c0c000985003003052342c280b0f80341000c0f5510b103541c0c1e05140640c40810201d480501c400b003082400c1c560550841 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 867779649 1250 867778399 867778411
    0x50123100b1c2a110f0a0314040e0f04031e1d010c0525150e06031806071107120c034706091608090a050a0501020c072718020405040b 59
    0x14042490710b01d100c40c5d0301d0300303210107116126a0010084c040028000e080c04044102d2010302181456510900d000f10701d0400c4401c46000c800140c02c0108041d040141c00c54cc541c40c800031110700a140b080c026110040041004417180c1c0344405507240c80e84514002980e407940101035442e0482e214160b821000c2c7c00c1c200404841c440c4507030100b003e40340d803a03106100c5031180e65151078100c0d40d1003d1000e1540090400c012800025085d07009000701080b0141c041c0c5555a910440c01840c208140d003009d0700c2d0382281900540c4041c0c0000401d8a4100c4101603e81025400103042c903035070f9400d110065031000900c10b01440200d14001c04c05d4003d2032000c1c0c03500702d0140d8100ca0751851f0811402031002c03142d030f02e9405503c0c8214580d01e0310a03007980f80d1124043d0103d4090780e055807240c501d0800b000c0300c200c840d603400041c0600c09034410b000740b2000304102c450840340300110301003204104d02400c07007c00304590748824040306120b201a9035804c0c0380d0050800c219504103800c1c04110900100e880c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 867780899 1250 867779649 867779657
    0x10323100e010b060f031f080a05101d1f06080a1202010501060c150e0106080a0c0f050d031202280512150307170a050123100b1c2a 58
    0x801601d810040d0840300171405c0d5120349031655445002024103800c070b540040061b403589503004500707500c0810140d480c080c000c0c8011f15807c40a0104a02505c07004010705540c40300c65000450801c40001c2e240702401c24200000710b58409516080707000b001d071640b20031818410300042c2d1080c010556202e0b042404140d00a00083e80c8840c0c0594881200780e80007000451307058a8800e51140da64001c42c06188040000308501d503452044034a0300b441c1410540d00c80049100030802ca217251040d4800800041c0c072441650340e61a28082d2030f4250950710039845580000720b01542440c0b07480c0c0b06401c040f20340d8441c025a07400d01c2c030040098100d490100c2c184c00405010591441d10b2011340204c2c0c4400400602d40d007818501d145100c0031030004000e4a0340310742803d00c0009a400e0094607219528404120502d0300010102c1201c040082c5c42c1c0c120001d1010010b01808001008448110700d101c420183d507100d0050b0100001c2c0300712211060908207850303c0e07071200351250904031040e10540d56 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 867782149 1250 867780899 867780911
    0xd0c0602060c190e0f0310020903100c051b0a0b0c03040615230d14010b131803030e0f010606030b130608060f0403050c0d0504090c02030a08010323100e01 68
    0xc0003180d14030860b003d10980c0f0003070128420300580305259060030b021014108008500c10000440d250888122030815915008952103625080c2044010003001c0310072000c0c070000003501e0b40035045101d84030a00640702c00c907488001045d07004001807400143c0c05044001c841c0382007000e000584e04141e404540f402e042c05600f0302c582440100c4581a01c0c0d402e081c4549005e1a604084070402c4d10903511500302420307a0950021899a60300303054540d1200b00082266852402041824101070312001c101c0351818042100349503000d80c011501640c14100040da45d06034000c5070f49805032603a610341c0b0a44c207080e404201c3e00e0b49070700016807800085c1c43d26842415901621002c0c0c500d10300880c40150710050025550101900704075402c01d009003800c5140403201c51a0a042050400203c0c01189002400b048410580e20680389500000c0c4003840c204240540014196a010301c0003406010320305200e6516820045486e00c81d041c0080120340700408078400b0103000c0e2040c104103642a51900c0c07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 867783399 1250 867782149 867782161
    0x18030d0b100c0b06060a0e0402030c0705070f06120b040902090a0c08070c1a0a020f040603060303080106030e0312180304060215010803040303080a18020a06022b200a020d0c060206 79
    0x2108001802c0d5010340546065030b2002c040c04030315084491980100301041403d16201d8440d4401940a0029020441d907a4043c5003401403401405a003c83c08042e15020104841c40c0c1c0054540304441039813038041410baa103100024007400c0300b0360b0080c1d440756070703402480b6001d26540c2c0110004007098a0b01007071030b0340d501d10503648503071070b014042d1840e00840014001801d0050504d64002845040103040c8480300e020340120741c0043e00101c0200390764480c28014541c201007824010585460144451400c070350a103622030165a0540c010b54000101143d59515484500000e4480100880342c9032569008000e5548409120400c1e031400000000314030120040101d0f801d494141d219010310391144481c00001b0500f03c102005050418014800182c3c2d403464002d0040940e41d005255202c03121a158402c103807140c809040342c000700403801034003540105010041520389100160420b400c50000c50600100d04002580043c61400220030807031045034440035210254202c40e2555070711 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 867784649 1250 867783399 867783407
    0x20702130c1e081329180c0a1a090a0b0d0213050618010f0c02040207150b030c03101e0f05010611070f1a12090708190b0f18030d0b10 59
    0x35103280d003940000c940c600b4046000010b00424405d05010b00700d4001c418200d01c0d20090a041e42c110140401420714180c8044c01044680c003e08402c8403094034091424200300c000240705099000e40160101e01007200ba0354003541a0f00034030b101c4006554030452028080c000754006000c02e00e00302060364000c00c440c10242d0a036601c2e01072803181a005d920b130341001900c1d03015440c2c00407400c0000352441e080058039035001404000303100342e0500240c20300010020003030f9640c401a16000342d204070921499a580010700b05500480348400107900f40c03e504640f000440414850058142050081000d03200346030f0065049a9281d03480d200b02e5141265421f0310b40e9002d03c0f400b181c0c101c01c1403060100804103810039520034002e90104d494103550721182d184542d000c0705c110190350440b89040211410070f02408001c1c3e440d418250851924a640d040c40022000d00b000501c144c10000060b0b0440b440400548400703214800c0704c2d10b0b07a0300b805084001d0700c0c003541018024000140d81e0100e89000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 867785899 1250 867784649 867784651
    0x10031d06010b0d05041e0302030306040e0604050703120c05070f1508190b040f09050105071101020a12051b0705030421030509190f0303180609080a06020702130c1e08 73
    0x84032000b901e0480750300701040203488060011b0310b4510000d905c18080080110707825a0540c4290051522850090100b2045036502c0c0c05004141e0024010031000a074040ba204040d20303440980003618a1788410200d8282c0c1e41c41000402a11500da004900061a54000d400300d50a03005c0c0c40c96051703100d400886902806803204918000d50b40c2c00c07070590316005e03000000c00d140d000d04009020000d00410005035050307004103072116550f610078440c50607444604510b4004500f0021351402d00c02c8a40100045030107000080b5540e955004120000e6054580c04001c840b1031100c140c440d010740c2006612580903110740600c80c5050320340309400d420b0301070b10004529095169141000c048500340081c103864803006140075060300e180450407560600e092009035010751b58403140c1c500c08501c101428546c1c0d8124000740206a2030800103101d0024134803000c0c6900002c050f80303c889910210305868180384071a8091030400440742d00065000758045212480d00c1e10121591482c00000c0e164208 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 867787149 1250 867785899 867785909
    0x50616062406030e010227040c0206060f1e0604031a091906090c08060106090602191e0614070804110a051c080f04091506020f0c12030910031d0601 65
    0x800c8404028007402544807880120103540003502c1e07c0304424103072600010444071005901b287c04846502ca090610a9242c2e01001d40002c241d0380c141100010f9190020300b240d148074503914144103a40c1d0350b4004841101c080094040c50f00c4640fa072911110380e58076101409418280c6c038000510712103001951000700166441d010003140002d88585003c1c10300c1030307015903980302a4803002840c0d00042002500a04090303942100d45810200000d0409803401580002c280e00c542c041c001280354001404a0b003000f448900907041e0303c2d850800060b05404078912000c04000e001c1243c6640c0044d00c10b441280325984062808011404100e203058607400ba060700903000c400000705075003000700201c610394000c0402a003040d541c584044041d5103d600426a0141c41e420034072104415081920080c01080c006040c000e401400341954907280750103080c0c46003554100d24844500107000f210075000e405081140316402d5139801a000e440d0185640c801d218011025901038000440e015060351 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 867788399 1250 867787149 867787211
    0x30a050c0d0c150e16181a0a0b090d051506090c0c100209060f0c0c01140a0f0c062306030607140f2b0f0c1707030f0605061606 56
    0x2c4030326520020b0290f40c541141070700c10040002c4143c1000f400030402001d00203524400740806d05400c1d01039824090600b00c00a0a81508030965550191810265000040c0d01500d034005500005c03003805000c103029155003e902d424a8071182d050380c07101d1240000380d450300c1c1c0c19141c80f41c04d90390a11440c0340b550410303005100505000d50098000340400c1b00d0081245080c4034149140340f40d1030348507014841003503111490b921f4165822125144041e04a481101c0c2800e000f000060302c04050040c1c0c00b420048440741c00c10401015506c20480500e0228841c140044441e242d1145c541003983c07030611900c5110700203500b062092119100382284841140d0a1500302c0101c40c8030707034124205040501d4a030703900020000781c0c10016562034a50021001c43c004104014013c00c6900c511080410000408403000034980b000c95107640094551900140190409003140001d000582050b82d000300e002034088101078502d411626010300522040028088811100180c03824010444c3e44003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 867789649 1250 867788399 867788423
    0x2010b061204260406020115050607030f08060d0f150e0f0705060f1b060a18020108060613090e0d1d030a0201180b0d020a0e0415180e030a050c0d0c 65
    0x244180d080c8400c3ca00202c03021000a042291200440e82094102d180140c1d550082c80d0740000c00c0b5841000100002d9607854906540c41c0c40080c280c42107403150506002d00080440c400c0d0721240e40c1c440e04d0603041400c0d0605013000385824081414403030380104417241031610b880804032001c241c0c0020440d000004001c2c00c1e24103800d0000e640c10082800303030b40c2c1d0800e0004ca800151501071036480c015214001e03000e0f80c5085080d2104450240c00701030940030b003015401c0c0051f604200d4250300034000719030864540602c055406030346491500b0580c040c0d41088010344844d00e0002c0c4d100c590102d40d403501c00018496403460382390030031121032155156002e12040c80255000b50020f58004680962000c00140c03030301c038040969400031001c0580036038001030702000390f580080e10544403501141c0c144240070080043d801300700464092112030902031805000403d400d0750007940185120003c0d02d8962070702d00c00c007030010f401840b110002405803000214140348030302d03041c0c50525840080f441c14 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 867790899 1250 867789649 867789653
    0x150703150f05010e010c020a0905010e010e0103030203040e06041b03270b1501050c060c070303110c06012303070f0503010c1b0602071a10080d03060302180a06120f0302010b061204 79
    0x101c144d00b03455250502044101e10340258980c2c0c0c00d004d0127800444c2c404102540b60540261a05074141d000c807120156640040c0000380c0c1c044103d500b10348804080300499100c2c40000b81c002c01d10503e480e00d48032802c0d4800c101e0203415402034400c80f018a00242403007884c0f1400c00c81d0607240101c0082400c24140c0004501c801e42c04da00c03010455041c9442400e01c052000900d02d00001a54001d19040303000c216501090340c540501c40e5101c1c41a0412420094110100c95a0f8070040c0124150b0a8181c0c07031100a000c0d210120108001d8000d00b19132099907103003243c0707040080e01d010f030302c1c060f5013807003045240d990003107464440716090070300901c8807000320b0f49404001b508095000c076410a009481441c0d240d059203551401350030111403543c410303071900c1802443c3c44ca0241418081c541407080c20000369643c0610054146801060001d0560b503804a010080580b50071a66012483c1034200d0113110780c0e00550000d142c420f4008000400440c4100aa2800394407000388001d0480800500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 867792149 1250 867790899 867790907
    0x10021c05091305011a041d06030f100608010f0c0801032006070302010c2c19081912021b1905060c0309030106050a0605190908150703150f0501 63
    0x204200a14045040100060004074492491100790441d942c8070710050008100340c03d003032060313000c2441c619881c0500d801d9018407504ca4120095020056a10003e442c2c1e40781446103600e00c0b0810390550b0f070303c101420362000082003580100d112940c644641044205080c0c815081d215101c0d03282c0500582c61917407150005e007035000071031141d180c60300980380702078039031031f010b0441c40e072098002180d04d030b401010080a01c8440031004610740c000035081e421f00d4210031441001520203440700d8411040c9211844d274038038020f91090072244125000c0c070304882c0025000c01d48031031142d281c1458040851000326a14105c284010744140c9007100c0c100ca0074640340300b10440720030070003c911030b01036500d00c0010900c0d008078950841e2904009064401484e0030b22860001d13003822140781440c5400c010008119001b01074400d40d01035561365021000074000c404100c000e003007030401c650032564460b4030085e48078402d0704d500020900700703d00240c441c20310380c000700250b480251603007a80d07e141c031004413 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 867793399 1250 867792149 867792193
    0x11b090e0105042a030605100e0108160906052109150c09091302030c100908010b09090c0d050f0a0602040911480c0109051207030204151d090c1002 65
    0xa414596601030005032038580f00c08e2408259007503199007448400400000d045001b004115290b000d080d0510280c1c501d80211070380f0151805440c0141d100d00040c2c5100e00d115007980c010803c5041200c04218030460b00050004000801c91600013160302c030120841405c2c004d000e0071750703031001095000945150100c50b199042d00c1c001001c555441c10b00f4004251035084c0d82c95130f2000145190402c0c00108000d010394080584150341c0013100e40750040c00796440d000501076a52041000f102044107001e81044025041c2090718180c2d0300f203464514105c4000d6100b0f1154440c1c05003070600c010300c0b468401f4141c034812024458804546091210348500164151032203804002030782d29522480c800308c80c01d5a4944800310001c6c0602c0441c03c0c0003501000301584a54424072030b1101e08020340ca404154001142c1d07041d24041450700c5085440b501e012480c0c4c04c0100d14140c0a5200350795a950854194090300c7c9006c1500e4000c0e00070418000f66075481c213180c50150303200b50004400081c1112100b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 867794649 1250 867793399 867793481
    0x2210708120a1d0307030503011703090603090a060501051c23030a0c0213060302061902150a0b120f150c2208010c03020304120c05011b090e010504 65
    0x900e2a0400d0703aa054040114161104016180c2e82d0805036140316031440ba0680c02d0140c20001c1d41020203a81e0001e0440c4014091892620300c0b40010014031141001521282540101102d03100c2c07610036100d6654814204096902c41d040000020b0340b400d1010300b54020107500da00d18481d41c00140c41e2802c461850800940d0700900d280c3c080308140350f0520151144016070350312500f5021540c0100100301c042c4811135210350303150a01c2080180d40d94421148800c0b02100c1c140010b0039000030a9080405006050f8294036010041000c0308801d0b81c03016500550480b080300c2090000201c00d80c2d90760403000b244034030380e0001e07075802d1501c100b0800250b84400c0200c1040c0c1b40107c06a80d0342c20203440d883e01010305a2030210b0034401c00600f03005255a040039483c0850039807a154540c0a0a0b1b030113074412006009902074400d041c40f8082d0008004203d5035114203505034403041c001000c078240c621512080b801510004501c2d89090f000e0a0540d0b000fa106001c0343d2500d800141401010381014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 867795899 1250 867794649 867794663
    0x3070909060b04081e03031303030e0307030509100305240d0f0302060702070e0702031c0b0904121b050c22050a021918090c0302040306020309070501020d022107 71
    0x40050001014000c0002501c510010203031200e281000c600e1a04a08010120b00c0600900c00380c000c611002050329803002307014100004c090755034142900101010381c080186800001040400d00d504000200703500c28094540f084028800c0318106c04031201510040441c241041d0981d131000480f00049402c0100203003240000711007613444401210414200700c01603008482000307001501400190010b01504d4483c0b00d80d0301d45410000e4507407049002c80702e04d00a00c555444403403503c91f40500c0180d07601030070440300c505207824142c4c4200d151100060020f50f0303407180b800c4980142172201c84102d5100004000b03ca01120030846070300e05403001d240200e0b40d14003240c05612024007a0718040c04a00c42c00507910302c20b81c150100c03628118072900301802685680c1c500c4000251030f500007180ca0b0160b001406241c4e0000c200c020348034540c80506080c0c00403090005e480c002064400840744240c0840d003d400b1602421385e102d0050401c0b440c40d02d070a030b004c8079001e41c0a010080c41e00b144a504 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 867797149 1250 867795899 867795917
    0x200a140a0b0706091103071a070303180f120905090c0901021f050a05010506030c031504020d11121b12130c080f300705010b04060b0d060b0f0d020307 66
    0x8544207190000ca1094694a4841c4121030070312103e071024404100d01500506001401c1200b104c0e00c0c1024210b13584240708000484600b418400c3e480750403e49400c2a113100407181509150600d0301c00b040e404d85580c0c0015240c448400d0040040c002150800782811311241d031190704020094120148250560003190040100e0488001504000b07581c0840001480e0500600c042c08861050300018082d12081082c860095007510075607074005481100c0c0f100400382d28020401a0007000a21810113003011107080c814401840039050041e000d400e0074a01d6078841d0f881c104504001c8580b20359000c0c01b040000429007540c000e9990290200070500714078445a5036458680606034003100558200d400d0342c03081c0c031409108215031040c0c81d8a000101031120f1480680e07211240d564480d61900002c3c182c0308000c42034020158042006000b044001c0d41d03001100c1e0b00da0b1001c40446031080c581040440c0303002600b0160f5550042d0300d5000390800d0704240601c0c2c001d60029100500317003e0600b03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 867798399 1250 867797149 867797159
    0x3090602130b0706060510050708030711032b05010b07020112060b2a0105090c0d020a090509030a080a06120f060e060c1b010608150705040f12200a140a 67
    0x441c0c20052448440711951064181803402c100c80054200c1849101751100003002c0a910034165070b000340d00401001d039203495204c010344215641469590304d502002c0b81e4050300301880d1030f04008601001000185112900c582c078011510240942c586440042c468400503501c1039200e112040c1d043d800005040d500c0e210f41442d00e40020038101c200784940700c007200903489070070720020418044000074011790078080244c548400c43c210a80d8003c080caa018401599945c194150080c111940200107034100080416100d5100c00c0c0d0b400d000c036042d00d0100c0c4060082740b10b80422151100c20040a0300e5240c2c0e200d004600305e00005031142c07900c4904107150701c4020b000f46801030003140c60060352503102800ca0410074040c1c0040400f01d900d8a28200b040f030502003011101c8424800304150603664000c003c0e00c00d13000d544c006840d020800a0003040d01c28010320303011000b6020f48051540c0c106001c11003650804010703540d54010300005030801810009101148040308018201c0e0025130710b034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 867799649 1250 867798399 867798427
    0xd02071a04081810090b0a271502241021020a050f0f040f090507140109151e120f02120604050f0c091311070218011503090602 56
    0x25102514146400900000500d12080c0d9050400c1c400343c41a410031018944c001c2c03d0030105100710303000b401e00040c059002e248070f03610007500c01e40f8008400701d2030840003910407996400343c01005901d0400070a2902c51500002c2d513112038440640094000070300000c403c42e0002d0000d000d40c00d6843c10f074080416000c1d4455100805450204151000390480707004005048459501c400d0140082e14501461031b121014551000321003607a000c503108042c04070701e40050107000c502a01d640549080412015000c0d85a10000ea4090b41c41c00003076074689028a1213408031043c041c0c04a40300a6034590700c1241e024550100b103a1a05289076007c1c1d0326010042940c6000441d4003116500052102c002d07991803102030340015003990100502d2030a2519a5a44e54020304141d00c1c06601040000955407410b006a0000d00310707000500c203c6000d01c1948520760841300d0102c1c071410f50030038018000e01c11a42c0950495032019039122004116580c25002080030b820161a200d4080081555555036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 867800899 1250 867799649 867799651
    0xc09011205010b121b0f06070b0403021b0112240b0405090c090a0308031503010911010e030c010801050d0c0b13030c0902130905060613090519110d02071a 68
    0x84030540032020300d90362908900310f403205141030744a400c0c885181d0441d044002002010003494402941c1d12911441c0055281124845d101758000400941042004840d48031140120711070703002c480f09401e00000001c82000c509102500146807030000c0074094000b074018207a85000c0e480071000355103840342683c003841d00c01e0700900c0400d44009820072050410718952039200050740340117418004c8c07000000726100401c0c07201070302c00f04000c00840c600762901d401d803800e0700c88010020440602540351919041c4404450a0b001c220f520802c80564140072400b0030800c0d0313050355a0700c9280e00789000c006c0301c05e4112000b074411078245000886c00502910042076181281c2c8030b00407429103103280500041c020f603007200071840d0041c03042d1041c04006504000517200c05120100742c0790b44400115143d806005091002e00300e031607200041041c02036100500030103130344201c241241b8000c046001a00e080e81501c0d80689810402c610712044264003501806110b111415540071030300f8a03807510400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 867802149 1250 867800899 867800909
    0x9030309151a0a030515100902130603180b0a0e0a0b0907140a0b0a0c030c05011404170f09040507200609011505030c0d1106040605040317040503060a020c0c0901 71
    0x10396465010400804100b070040000401c4a64014003400d43d43e41907111906540b8000341c0000354404109161040c00480001d8140c01034110748482c02841e000106a045220b00d01c046407401030300c1c02603042c030701420320344664101c4041d904644507620440028400150414018080c4002030000030b6144000c00f8095032002009000150501c6105801c003a00300040324400c916000c3d0400a40603100c080e100a00390700e08000d0513211803404c1c01d854070701158400401c103510f05040c13481008610310720f50340240c0c014900d911348200400b008102c2d0b0f2089640d03005201c1418440b40001e494690401680006245004940500020701c0316440b4922a1034121294001e1000c00010390400d1042e984409401440c5c11781041c07512002c207441c2c9200c0f07001e42d4010200168600f0501c8010001003035000000f0f0b2505958640c0c0d10801080794015010446504007119641c0568440701411746040d520010044e01003900ca460300700e0300070b5014a9441500b03001d20030b0312540d107a44858501e80208 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 867803399 1250 867802149 867802151
    0x5040513050108010c1b0f080405060408010c0e01050a09141305182802090a0e0607030618051b0c070e01060519020f0606012607051222060903030915 66
    0x5410303d080c082c03c1d141070040040401102d400f080820145020400b03003103d802c4100322020941030705094a0794822904074580000780000c0c006801181580030805070304041e034900b10200d807008011242480350000c03040c0000c030999010701c031408400c8120354190b48020448210107280b28042c00a841007101c6102c0b40c106801c1080c20111018084000c10910030340486c2441c004445a580071640391403006806034002d2f100241c8c04000c95403041d039000800c031089455a1030500c400030050107060159032102c41004010b40c40c0c0b500a0b006881c050f2402644074805441c081101c00c88541000840c1191403188600010f14650900d040b01d005c3d0015a9406568101d440700034858880140f4a8004552160480c40d0f00424040fa2303207504a0800d00c0c00390004140e0240150780503240c9400b07003200c01c1d5902d091008058004004000b1013103481c0f490a0165108400040006003004180355501c00302d4141c2030000d681c41c1d0243c40400d1203403c0c00100d41d607250b240d03c0303411000842150f50305 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 867804649 1250 867803399 867803401
    0x21c020c1003110d0203040318030c1502030c0c040203090304180209090c1c050a14100603060f182021010b040311060702040b120303040c090c0219030504051305 71
    0x18101030710040781d90754a504091220150508100880f0711071101d078525800d50100209040520030030440c4916404903010500107a2a0f00b03004516448503c910389609181c46006400140048150380200d000d20004e421940058014000a58801042d8078402e0208010204a40809843d01e000b401c0d900100180c6030035000c0244084c1d50005447c407000c400043c4144101800b200d52450300c0103680a00100b51034540d5081c8002030300030785d04401c840e2900c0c00200705194900c0e01c0190200c41081e0b40034000c450350b0b1011005012420b02900c06240c101840d122079a10064200004610300d075044d240e02d0011294184841c1e070004402c0d61103106c0c0440c100250100c4461900380509408400700c0d04d06455580c40316010701c0008081c501030b0402184c010f09650b0faa44c0b000078111405469007420a4000307200d01d8481d0f0013102c1c1110f420810b180c0205410b242480b5025100d500c03500105591001124050408010704000310304005c010000840ca07078403241120004e0b48000c440100351 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 867805755 1106 867804649 867804673
    0x40903050418050619060836060406290103180206042403090209070c060b0301061217030c07150f022703151501021c02 53
    0x519451842c401c0700500d542c000714840e80d402c440d42441e41c220b5001c0384401c00c0050040c0b1000500310000503045c501002c0c07001001c220200e2005075100701710748441540e800b520182c15842e800582c2070104108130b50140d100d04041d1440d11001c000c8a00070a4551440a10680c604258892000b00c80000003500c03103112060b005854165260344409541d040540640b0350040000021019426414440d10481c030b150341e4000c0001c2e0a682352a80100c0359018108010b446503661060040b04a5409118106c001c0c040b107100b0b62b49010807400d0925903c03004007401c91b030f492010000c1203030000d1450300300e81a0725480460030000080c0416000d008000541e4190240e51000602042c6024142100a0382091100c503206c0c1d04145072080c19150710120b10780d4040c109500c0b0100d144c0320343d00341141d09645410710440e8028148103403580c0b0303900421001c18015802413680011 = true := by decide +kernel

theorem cover : BRFrame.Cov 867625899 867805755 := by
  have h0 := BRFrame.cov_init 867625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 867625899 ≤ n) (h2 : n < 867805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
