-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4657
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:19:16.232998+00:00
-- url     : https://prove2.me/submissions/9bc34691-aed8-49d5-8ab4-c14a2cbb99ab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 837410071 ≤ n < 837589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 837411321 1250 837410071 837410129
    0x907050c0a110a0f03110906121c14070b0103080318120903060f06090a15051c050d02120a1b0b04030c120e010e0d05070f0308070309350c030304 64
    0x9404d00101a03070003000050510150100442c80484443c0b41c280d4031135010480000e00320660004500451004031805075414001e07114207800c56480344505502656650582d1145100151102244400420010f40340d0401560f00c2242c08004078000981e08004529140e01d001c40f810b15021701050101041c18100492948810000c00d00022420b29201013050b1441c042d110521a0380c50340c40100d00c021061010a0051001816041c4440300b14041540c00e41d802c18000c131440d0285204100c0e50500c00101e5040340000c51549078500007280c582520404103008001003031060413007001d00418902100310b803107a4041d444d4241c45412602d00100c0c04440305981c6018804c0d80000e54200b42d83c014060f6005907800e0313038541105105410b140e45005a144c0c40480500300e801404402c103c400405010103600c681c0f5180b40395070f100c030501811032070000d001c10250440c606400c00c441280344609680303916510155107500b0f0907900407034119403054015000c070310300219800701c01c0c3c0350011034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 837412571 1250 837411321 837411329
    0x5060718050a030b1312210b0906092d2205030a0c0c050d0305040515070215180405040c141206040305031021032601050907050c0a110a 60
    0x31041541031200040c10075200d800054010280b000c000b90048083e5800313283e1564004909940b09100208000e010700217060502e640720200c500b0320715200010b40180382c003e04000b807488007035a65003420b016013035078020440c400c408088840030020000300c0c00101d440403d03030240d01100d440e050307144055020040c4e800b03207880d89404d4600e6011a00100c16100343c0c0d0701c5072910200c120100e081c000c103000900e400075070340050002220820103401000074021204d0640b01d1414507001c0c02500c181c54001c0c2807000e504401040c0e12207840103004401000d08488030390080c59906c410101040449030304480071070b0364034403c4005200705940846e0307100f500b41d0121000c0c1a0060745a80554903040c2c090002014440c2c00b0003c40c880b40d0103201c1303c4018001d024180f101c05005000c3d0814469120b01d01034020810020320340340800d92800d490000341c12a0301c0b807080180d01c0c0c40c05100080d44020200c808101003480b1417407141e030741440a481c039903000380e04204030780c03130300780c0030003003480f011f0340c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 837413821 1250 837412571 837412607
    0x5010b03040c0b0904060305070b0c0f060709050f060d020d0504020f030102070807200d080a0305060108010803071202011e050117010e07030b280f05060a05240d09050607 75
    0x400c200024161014450a680100c00f485445650072004207001e044250401440390140d0640810805101d9003c3d0010400000844003050004891562940c809803884c00004084143c00d024070b092203d0b00c0410b0050141c00a403030003c031110058102c0c0c002803980c0140b16110f000b80001e5283c8003106511060701100218585030f5186e81d01c072020b1052007002068001031481036601c103803d00541d424194000343c15100e1305d000034a0280100d074002a01d90000c86d01e0702011030120351290311420705a688800081d45444034940315101a02a0b003d9480e0856403a0740c24031070711007407118661403a0984010042107a5040a00c4014a64100e2220f00020f03807400d618440d040e40001a07440c00c99400407004c80250300c440c440d030407040341c007112104030000c0b24030345c905082181ca0348407800380400c50700d04106c1600c0341d40800814101500c00c00e135200c26072224200610020b200700440c800741d415042842d0070304084186080d180c4e03c3e035080d16990444410084d00907006004000320b407450070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 837415071 1250 837413821 837413827
    0x60804140c06120a06030b041407060905010c03110f010f020424090e09010b060f0702010315061202130807030506100b0c06010b0c030d0e06061207140103020a0210050a0207030305010b 81
    0x64080b030043d01501d210040e039040d02e0400f250441c110790344210059030700001240d2081c505420000d920311401400e041462092203000501c00b03203d9404102038410594608161a030365880840e0300e410500c0454010340100402c15803941c1c030034800d041300764240300405601c0b40d1810303080038000b550741150aa00082e901c4000e861590703008040c482682c01240e810105a155001e46a0042180103840781d0400c3c0300103882140030004d0000740071110b100766414042000c4000b00c04004268911500f008030f101d20003141d440c0b0701150081c009299100d03520340075495944801c50702c0c00d25503038404d07901508072809000d800c0c0c071204240001b03429094a01442c010304141d03031a543d20414030445410800c0825407040410301401214101009a0340600030081d0904000e81c0391041a11220710503024807040080d0200e020490404a0703111a030111982400d500064010394400500d0b10110700400c81e40004126a07440344c940121900400142c40d880c061401400b2104180c0200f00149024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 837416321 1250 837415071 837415093
    0x3070932100e0112060e030c01050a02120702030901120c180b0c15040804060e151801030b010c1e03050c0d090608070e0607020103090204060504020c0105040501151a0f04090606080414 81
    0x8608070030704c0c0c0707034088800140e002420034414154003400c0118001c03542080c2c24002a40c0b8250042d00c03a6004c00e2000f01c1c042e484009082e41e491040d0500c1c40c2c0070400040c09407022000c0c6501440004086040c14800c901182c4c030f400c2111f2001d5000411415400b08502421040c00c00a18940c210030464900c040d05003512040d5441c0114406c440400c550858454201c1e01c0d403034501001460b101c1c82c203544603000841c40740200c60b002070a0f240020302c1e02a02c00c05540c8101030055059130000030441c0034020183d54200313440544681601402006c000d0300c40c0d010b0041028100355141540e80660701402c2120090030303500e010b42039204010400500c0d100030341d110700c2202c2c9959824240004d00e100c151000c40d015145960100e58014400302e003250011300c06402c00d901c0380784104c0003045040701e200400070003520b0500414110b40c0c2902d0340410010034010003030001103441d80225003043e6a07420325400380c0c1d446402c03c2c8005000710080c402006a9510700000104814024001d225a4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 837417571 1250 837416321 837416339
    0x603050a061d10020f04050a080c0f010503060a09090503120c030406060602033c1603140f030402010804140604110f01080903180d0c06020604020a1403070932100e01 73
    0x8203442d0003d280e03030008481c1c2c5500a41001c0303d006010151148240f659110040d43d10750300d91505442c0110307240001b000e80783d841001280c2c4142001000407c025080171403100082103c000304030780c90708c41008036480144040701c41b5882552841010b5560749402e03d0254242d500950000c0155801405510b80f01c1c1d078071461490110301c19089600d002d00309200c6000300308907140c11524076580006440040c410703a43d22200101e90081e20f6490144051134507032509440b4051002c0c24904080c0007190042d03104120f41c070703049030042486000803015000e040d4101141514102c801040c00c400c81c10b000d0406a105103000c403024240001c2c0d900c2c152080c10340304c1c03141c0d40404801140d50051900d8075925450f4103d0595004050756841c01c0e2135010282d902c50341618117910a202804000a82150700710300450892005030160142c42e20340100344001e08100c13114035208000c0005400d00c1e40210200141810140c46000b030a6400d1903182280c002d942d90308030000d0949114014081411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 837418821 1250 837417571 837417583
    0x9050c070213020702130f1509240b040303030c050f0c060103110d02030a03140417100e030c03040519030b1e0907030f0b0408120106030207020a050a1401140d0603050a061d 76
    0xc9003003000300e50426000c04803002032160f0700344403125007234030080855920400d03880390000c0c080b0000903100c1100000c072164600b100d14400d01c0d4604030100000d10009200c0c0d04110340b401c9882c282581000d071036184003220750b0095404100c281e40090010018008208a441003401c4c0c2607801c54254601600031035196070f0031200203400e0040084e503458029500804a40082507101d6095205000c600a6161658440103444030002d0038007142421990f00030003110301c074024890045141601d48403d02100104205c41c5580c00ca03400c440000200d103c075003103d4412034840510040d04c0640c030032100c2c043d44000c0c0984007070380d10401041c030008038989050381a1a404c45002d45260b83c561420014ae88108070080ca221791000000041041e00354028150f458801c6840c84440340d1100184500840c0c0703403252140041d0015581e44941d4050401c8848820f14694007618280301c0b2051841907807684d91045500381e1040c03001105108141c4a03240f0311002441c26280386445810245d41c0d110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 837420071 1250 837418821 837418849
    0x33507050a0c060b15070b0402190605040303030c030605101205241c0203010608070e0903180907020111210105100801062001051302122e0609050c070213020702 71
    0x165242c2c4d1042ca10b03594031034071030302e0301c526003104503510115840d004c100303c8803d179002c9029113034126680c0541e442c484800030503581030742d580c1403c1c1440e5840450260485407520418075036102008611a100d404090100c80d9580c2c42c0d24604d500345070b046c602240c5c0001d03c2426414105540c04101d10a00c2c0c040b60110103040b520100c02007040340c0351140100480600940c59031134050002200a800324201d401c83d926110307015050b40d2515003d40d168803444100c20711252041307040d0649450708402480d080306a030700c0002501d050302120401c940e44502c0c042c0120284141000200903400074000b80942015a070030380d0440040180540315030010f001c2e24091080d905104141c3c00150b4061049680c9080000d0000d400d01703040401400340b02e120b06074060500900101000640001c3d88144006812801c4800450442e800c030303801c51100f0080c03040c0549402c800618035010f8020540111507401403640d03101003d1040001ca08042c865501011f8014040301000d0f80c0c80078862701e005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 837421321 1250 837420071 837420083
    0x100903090b1c0513031b0201020a020d030e0a09050610110309041d1207110603070903030e040603080f091206130f0237080c130207033507050a0c 64
    0x39001c0c10302c00c0c00c40510000075400756515000030040442c80701201030714800c2c0244c5501c600591500300351030b04911920000790240e80524074220040c2070841003111490f00034a0325054542c403180002c1e80320041584080081a00c980030b100d0b032441c007044495103102d00e0f070a0400802040c0c84805849000d42042d9510884d0b0b61115505080c0e02c0b042a1402c2c95011010381d0842c20f4640d0320f4004035040114160340c40401e0942d01459800c0c5401241d000301407503164040c0f035518503a41210380c1003c05003000c2d04a40c840400000007517540003d0a60703441c1442d80c0c507498512000c01d009400003a040c0800e503640c0305505101d03029010200344401142c1107001c40c0900c00440c00464440074041c0c58036840b2510b504580707808a1601a034010040d0360401c49850001c0d40d543c4160703a50340c1820920b9a0007409000400005800307540140f559a04c607003800d011318042d4408454000701c828074045000304100004c0d02600d82c0080c00e10354802120f00305103080c0042034000800d0201c0b0f00000a180b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 837422571 1250 837421321 837421327
    0xc01020c1e1903030207030b18030304020405091c080105030f01140708131e02041419020c010f051017060f061002120f1305120a0206032805010602100903090b 70
    0x2d0722101c00844050440a520310101c41d901e150007951540a4401515002841c03c04100300c190071f4200b005e81d401900b001982191501c0d001c000003010040c090300c1481c403c18246e00b14400c0908070030086000d49445a0401c1e6240400317144c14680c42d143c030418180d240c128120300200d0158603003600502c0e02d00e0550255520092074404081c40d0400140c10081c00440b01d05c0a0401078101c0d40c0b03418800e580604c102030138603210000c0310500340c03900707240c2c0c004070342400340a0007040c0d014100c00700031103002154801e1002460400c41d00161441002a1b28811702440b07001c41c1c242d240300300c0702c0385180281294a01100100a0706d880940420b1060303020500145c034a1303200700200c800280184800544d2520001d10100e142e900426a0403100300d10f500d000155460520002008003da80c00034007000303001a42002455400100301b881d1111041c10044c11586001603044039520410f40e0015155050040191a0040804058410070304009030307400040d6000051404071000461904c0d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 837423821 1250 837422571 837422629
    0xf0e070614040b030f07021b031c030b090103060902010206160c020d1a160e060c070b0309280b011e090c050d0f0207020f01180b070c080f0d020c01020c 67
    0x1d6882103034841c07402e402010041c402c141400c005641d00404903038080f900b40c0340c001440b52140c4041000519070680142e049510200700c040c200c0710000d0050318002940d02e48800000314052070a03001692602c0c0c1c1d8140c410b0865804011440d0800c0002c030420294006084004011070501c800c000c2c0662402102101000001c40f0940c80c00e00103000d51140510700703201c1d1050321001d8503200e02c1c001a1200b0054899041900448442c0200c140140c454035040c03a0513400c5542c400b81c1090602c1c814464192964402103000e55100300a02c03160203501010fa0a001d5405d00041e0003082000700d2300700c0186403201c002c6100f40304460300041d0200309000e42c0d81040d14035014810885401c1800c1a00c00d4003196826070043c0511340c070032220a04007240000044581c1d0080080c0c0b500071841c203960034000b41e45054054802d40e4400c600c2c1402d8240c44181d00741c188407260b01c01d84010703880b1b00c4140c440c0b80c1c0c041c440008024402c1c0b000f4494880e4000010f408409a0701c901c1c4803245a519042d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 837425071 1250 837423821 837423857
    0x90b030a09030c02060d0b01180e0f041e0b07030614030a03080726061908071a09180901050a0506010c0308090111030c0319111b070e0c0a02010f0e0706 67
    0xc14032a8000f00360907120703046444090050001c0c18003060000307001c8100320a0001d44c10702c510094a22100103d85190383e2f010030035425100c09003082d184e00d06002d54062100316072074119010984034401004003424044006400c0d640c86401240a1005d4000340000c0b54400280d4144d401b5098601032040b6181c0c0f14040d80c0c114110a21164081010302c00303400002c41e801e8025010720780a80c0e8506510254040710b02e1901d449014106903a001b620007000004420720314cc041e9010314454543c600584000050303015140c2e0b0481c0142400454200b0411341028032480e03500010b02c1030144841d182401c0000c04d4141040e500030144a03040000c15054030095120825140240e51844d64a00744640c1185541e0400c0b6590300f00481c4200c5103150320401400b5000e81004200d9045003800002e5288000e081c041c442002c1c003a00c509000000c4001c405214030f402a0782c2002c03503550728070107004000e094482c50b00458240c20f003031081e0760000c0140024000100c07520f070724001c283c0202c981400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 837426321 1250 837425071 837425087
    0xd06120f1b0807080d0206060a050d0b19020d050121030e01111c020a0c15051902150a0608070e01031505060d0807030e120a0c062703061b090b030a0903 67
    0x7002c510b01c41c40e900440c81001c005030305001c0c15081e408407202c590b10a0100a940c991600030b075900a0b6080c5107890014095103c07290700f10045006800042d1504420042260094100e5440640e2100c00400802c1c2418a1070782c1c03070f0400ca040351106030800b501c000d03200311300014140e8100280c02405500d4401c040c020501e00700038200301c520945000c0c85c00207540750261101603520010055000035003038951a1244420384060301c03518200843c0f4460003125602d9140650150f01401060083e4058140c80325481b0706031084001034154104091309107000140c1d004030070940041401031010402d0308040d240c1c04c040100c4086074958501c80840d01001103441c008241c130340080f81d540101a005041640540d20070703216000f003200c8140c6090b92798050500c021348070f2040caa600b0302c40144260555910b940c443d660071032488580c0c4e1002040700310709900a54646942d01455022441382c00f41c1c6c0d003a01c802514040030b00a00300205a11309120282c91100a140d0700d031001401c1502500c0c103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 837427571 1250 837426321 837426329
    0x4200604240908060f22020306041202120915161502180904020d0b150a060201090c1413091b0311030f281b08030d06120f1b 55
    0x500700a01001401d8140484124204000464410a4041409900060b0844c4038100c10140114191502c0036a44080c0d455481c10081e100325940060002da242004198040c0e841000920b4541d0341400c0e000b800c10404100b9003503c400d0810820030281d076080c0c092124801042e0b6038030798841c1c0c1070100c0d00303400381004001815541c80b0744110f44440910340c040c100c810400041102000b90072410002400012240254000048200c1c140817801c519a46d99000c6511006103028080c00800100c50b0005640040d005079107135400340007001b41150509c00140180b91082a0000d007640000d02444001d54510901c03583d03400c020028002103640407460f0441501002c960680c84e401c0c1042c480c402010900d00070710031010500d1600500040c4081110400c076040c2c1c5407840080c904040000340c24005441840541e021a0f07aa00a080003010042064400440e41c603590f054501c0c081d10801c1e403101004244051403c4003040034200700c110365682c08402c0a2814407054006c016143c0f460304 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 837428821 1250 837427571 837427589
    0x180905060f04051c08040f0c0f0b0706060504050f010b0706060f0f23011e020705041401060801080c01080c0a20010522050714060d1401060806060304200604 69
    0x10700c007a00080d0800c0c14000d50054058503001300300120000340e0004006002000101032800207030103e00e4068003400203e21814040842956400080303d8401d41074210340300d0047c00007500c108205461160800800051360148524034262421540c00d001c14031404455400004151003009410703405880542200482c481449071595030310900e58a180c064810950000300c0000c6454070804440800703244140e644124018001c1c00ca511034010001c00203040d441903401c046901d5076640915004080340038020b0803a90b16115000708040070603404060b00d50000200c10700d25990003040c0603841200342c0c0c000daa40300b02c46030301111988083c08003806103103030540d25a0074421307064004502034104d20880d180380c0c50030207007401d130801d1070070384020260b0303014000400400c1e8038a041000c000900401076420040c2c9d80e00b05000391280607041801c05d4192800503c602604005415013001e000d4521a04520341940c6224000d0040d220110151448440a0001e940e817141240c020b055000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 837430071 1250 837428821 837428833
    0x4020a0909060b34080f0d060b070501050c0c0a020d020a0e0405010e0733090b0d0e100c08040f081e1e092b0f03020d110105060a180905 60
    0x7100301c0d6007007850b000340180d81c000c03822820902085101e00032010a142c818100d0710881d0b4603201c041c6d1104015000707040d0144a0001d4202c00b0380f1600c00204000450b29582d88424a0710368210307000180050f40b0703403005001c2041c4d014800a840241d4990545601e41912030754000a21028610744c446a44010123100308000c201064011034412030f0800304544a8680340c10f059a841850502450060300d40c40a4111031441c0c000d0140034104000c2c00e0005540ba2180d03411007c4d80e00088400e00401c0d100c1242402c007a070104401d09001c0e03400d0030304005407810000010301c040b030060b201a052104007280303002030040c0310f8203c4a0041e80501c038554400c1000d0141c9090b50032021502183c0d010110a20481c201d001040340d648002c000d001111074074000489020803102040045440304480c0042c0000500406402c1d012500030740081680009045004210a404640ea104a41d0605d014800700b03449000f01c070401d455a881c403551203c922520707039200034200c181000d4690701c140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 837431321 1250 837430071 837430079
    0xe0f03210c16080c210d021b0105180c0a050a0b03060a0b0c010e070503060403090e0a020403150621080406030b030c030d03091403030403140708091009141504030204020a090906 78
    0x1c40028500100040152404080d51286100c505103400b501240c42c1d017010008450841c0e03650b4020305094469400ca911481400108070303003100c504550b5000156403042d2075170000740d4204550161410210b400c030200b1410f12012035403c036018400e040341200088085005a6210401c00002c0c0c20900b14080c0c450a20030300c43c501801c03444000c0c05550140840110301824040380c0c080c801c90f019110318442c18548542e55a024100420030803009909201c040b0000701844290130f501d0842c80c801282c42c03400c1c0742c81c501c010307a820005400c916602d40e00150000d02c1031025141107580c0ca050000b01d00c011940481d0400203040301241e03043c01080609071420740c05501109d01c281c0500c4000f04020100d4485c20360307a00c0103880240104130420000c920300d00c11000103000c964425039a26040c500c2e08000b1840344840320700c02c032010482d111024009182003420300c10800c4403c5509840c1450700016001ca036101e103010281c0210740000e2120140d6004d441008000e01103680200021503075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 837432571 1250 837431321 837431333
    0xa0219020102010e120913060b0f0a0c050706050310050306040201120203070327170c07121e0b01180204062106080f0d0e0f0f010e15040602010e0f03210c16 69
    0x10142489104111501d84207c1d140c1e83c1d8445c20043d2410041190b140c8200100302c41d0958211111013020040c410070100000b89080c0a0305005240743d40b22241c40c0e04041a4600f41041d0340d402c070501a51101042001603079124441d40700c502d042620050ba6600c030039004070040c00058400116a03203000750310001c0582c007000141a030134040c032118851909000b0f200021031281102c400c40c03a612400b410300c104a0781c039052208052107080c002010f144e40c14410200100c54031015161400400c0040000b080300701c54440c02e00c05200411031a07d0b0a01601410604051403240c0500c0c100100100e0300c0d0000340c0c0401c021306200811144ca08000000260b41c52455040100c00034241d007a000c246814507070b0310603400724401030802c9014031002004540365806c10030480d910034a00c1074000855a100c60085c0083c0c00e40d81e00109105003501e04007460142031046410860344100100000b14540860000165220f0090302c6582d84403404030700e64600030101d032081c89002d0100700d1070070080c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 837433821 1250 837432571 837432577
    0x618160b09130507081602031902030d0c02030a050a030506030307140a05010c03180f020f06040f08160815190203072706050319140f0603060a020a0219020102010e12 73
    0x64110b40e10031084941e00e510000380c07034050b00c4c1000480c41c00030210381e4a11080c4c0032030300252450302c1100e091510485520f030f0001c0f44039440001503000080c1c0800c402105002d20014646039000561401400c044018500e00c01c18001804159a80b40441d107503a405200329045140c0003180c00c015002c0580c0120307202e580d409000c4030710750b107490000c3d45003c0c043d001d070401c868102462000d5924081d20f5200f081504880c04980c4001e500300c51000d1540d90340e0241c000b414903002c0c411032050034a8200c900c0c0c40440c2046580d06c1c0100309041005040000d03880364644060300c5004603c2c0c039040050308070040000b80d100034646c00401040180703036000c290180341a008000725014a44c51040c24040d68882c1d008100c0000c0c410000105601131410104001c2c1480c02c00004050394104005031403c0ca0690302190381900b4241804200c5c42c0402c002c07500708050140851802115000107035a40b102c502104d00c103c4040c036285419607000303601003840181003030241c0d554244078055070140d0f64 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 837435071 1250 837433821 837433837
    0x50705011e23130b0601051209030c0f1501060e06070827060c0d0e0d0b01080c010314101203090b0a0906091208070f0809030d020a0b07110618160b 65
    0x2205060141e41e080142e1807855000c1d1056080070541202581c40c0c0c0700b01441c0050240e814020304100e5035243d56280034006106800500243d616402c81c0d204140c02e1600108800c0c4003540110b200721068900742c0045811500795040100b40c420280b03000c50058004c0003009402d000b0042410b00c80d0181003c01c904000c0c4490715500c00300e0555004000407805400d2108916620040400c90300034064000c0c00c5840c07030b00030011164a407040c0d07540100078109802c00d12960700045820581941c00d4040c0452500284211307262500e4108503003040c204503881905802462154818141402200e01d0070140030f01c445020354480462001a0000109108480014a1401d0b0002e1a940341c0480494110b6001b07501502d040119226850056407189040e95002d50401c00c06455a40030850710342c25480301d03000707000701c10583c2c02d01d50380550b00200401c06011024608000b035160120f02e45502c0042c03600c8007980d451081030158074240356109400ba05040c11074004c41c00d06040000ba16201c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 837436321 1250 837435071 837435101
    0x40609121707050333030714100302040305030f0a200a1b08030f07060b040227030105221103010c050403020301051e0402060d0e070902030402040b031b01050705011e 73
    0x41d1034840c400c440500c4200c4a407115912603200d40381016440b207103203195002d402c5d8502d0381e03910700710320000741019002d6100703c0c0f4030391002c0350300f61840c1049605840c035800310b400c0442c24285191107582d06d9225221070b141c1c11190000788035165174010000d0100c0c90f0442c43c0c00c3c04601c8801d45400d0354a400544068078405a1040c0381202d41c03050340742c134000f84d40d01d40d8082c506040e001c05c1400702c19003051070b045480304d03203d03400319079692035504c0940302040035004e0102070700c041d0304941044d0f52a01401e090003a410f18041100d080b0b0a641c5241c45402007907601480382c000c23403c3c02c030340004004101d10703415403c10703141a003560303400700250090741d000302c0c000c000c45e890350545182d20384000f400c075040e40f03079101000030094038082c000b41250b8543d218005c00e141000c0c41840e81449030a070406500c2c00d6011041c0b1065081601c45c686510400798000c0132105020411035544c111004121410818002402e0b030803c5402c0d00034462102c4940b1040d11880d40980382c00000c0c0c00c21401c003100c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 837437571 1250 837436321 837436367
    0xf0509041a01180524041a30160b07140a030504092412020a180515010509130f060918060c090b0f0a05121e01050a03021804060912 58
    0xc40a1111126202c0003103001781e580300540d0740302480040d1084040010307503500001540c400d10f031a132100d4082c01044501c500324540480e07030448095001d69508266269000b15245420309041c80c20380020703182207140f03558039059285400902d14000502040b8a400364070102001c142d041000341c02940d543c0c24091250185024900103119500310100c1900891550200401c80b03000b060414898009801220001c0d10340003078400c1d60341d99140b4400c045588108000c1c100307440440c43c401041c42413a065181102c204001130f50030745035460443d03085a4807100c0480340895540204000d00d4801c205110706033f8071900744114009a400140c0f003503410000f440420034429001501500c00041001d400c00400384000c80590700b08003828014000b0401141000900304112103208080e13a400300741490500c01c0c0b68000094060780168017420308000d041c0010384d5015029052a003120740512072640c2c0e2420400c01400d1480e0010340b0000d42d054440c5402e56001243c2e0754000302d02201411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 837438821 1250 837437571 837437581
    0x1b03280902010f1d04020904020f030718090c050912010b1002010203010e0105030109020901090207050c0a080c1005030105100e0316060c050d140702010e1f050a030b0303040f0509041a011805 84
    0x501c00310b540b1a40019401d40240c824145c503080d800341c00c086202800050034007454000380001988262090004a0b16469040d6000b0003206008000381450032810f010b000b4249a01400e20300450804038402e041182251940010940c041c1c0d1148400a0002c0600c02880c032010b8000d51003070181c03102c8000404000315142c281402200074580c0d02501d540300c0b982c03078880e17030000940115500b12210f010324482d6819070355401d4a010045c040c01c1028046501c0305000b0088050380442580741070003414001000165034001c1e00742c040c40503a042c5050f80e0009100020304001c400060400701002c414000300301581d00245200d242d52161040f40e0340d11051000c1900c44880c60b805000800604210250065114100400c540f40c030103007180021042c50130050147c204403803009000141c0105040b621550b05010707200302040281c000c0c514080c10803d605111400d90f024140c010310098001c00c0c200171a9000c104120080d09520500c5542c49014020410401c01064001503043c500412 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 837440071 1250 837438821 837438827
    0x121a0a08010902010f0c030e040213140907090b0a050f040f08070603020708030403051606050a05101205120a17091e0c010806100e0d080304030f05031b03280902010f 73
    0x110000390161141010300700e00741d104440b0140b4044003201009900b1000c2300301611103001406400070a407505995003400d080d00c0c10b502030f800c6041688101a04c0042c089443c0e00b00c0100000c2e89d01d051800c0e5179070510742d80700f611548981d22011601000000d0006400240c16941100703a07802d00050320075903582e6130310403001c1c0d000704200580146420800b19000a014100a104011450340880703849480f41e1184012201c08035560401c0b2510b0303104011048007000030b41340145c0302e81710105541c2402c0e0713120030341d45044450040300c0007500021002d002d81c0c02841074000342101090401c2c402d142110646403502420003040300c51401b140074000e00f50501040b41860488181d461480c00d6a0302000c02a83d18a109011720500502d04a20b81e0107031507042c00300c00c2c01d130302441d50326945c0c1c1080d18009210403061078001080020500900808807402034801079121002500b9944036194400401030203801d8914909034500c0454841d401d03408150880c1c44028000d0300c9400c0112401c55060f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 837441321 1250 837440071 837440081
    0x32603010b0405040b01031121280b0409050d0c061a2206080d090e0109090b072706020f010b0603010b0409090c090905031e0711010f121a0a0801 64
    0x2003400c460144400c0c41182005d910045c0c400307805140c04500900410b03400d9116511a9020400844007402412180442c189241e0b40000000000d0001360b0f0a90600f00340140c0300d4603442c041251586000720150313895400100c02250058140c0d2a924040100980540d005040495141d070800c1d040500d035100309445a2032510000d02020006040000c110350b07484d0200340043da80c1d40c0d80d0b88010956080421072284450440c2d16602071543c140f280303000890034141d1005040c2e50411380c488001480d800704840d000b0303416042a1503401d01110744001003610951280d001c0142e4818001402580003030311100d8540014001c1120403003810601810380304c01d01a01c0c030300c99005c000c1040044495403280d0301b498011040c00c07401c1911551101c0076201c106000b07441c0f992000c54503c24038050381d80040c00c17002459250900c1c200c1c403a91960f02c00340c0100c800d64107110019103603008183c0501d48030081c40400440c10086070240101c03000c070a200c0010041e01a040020b40841c1e0a40140300f5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 837442571 1250 837441321 837441329
    0x2030702010e1c06150302040b03030405030322050619030c020a0816050f0d3b0603040614160f02240c0f0a0c06050c090d12021603260301 61
    0x1810b81403208400074407009408066078400c03445182d02103100820704c50320032200303640006400c0c01e8020b4598010401941c03076910000d0310a13041000b04118581c1d000044807040700400e540003004104107120050749840356440750b0741050001038540c000e11001800f000070a0066141002040728807070049946114540d0010008103081041c1444e10900c4120081c0343e40c0f10b6401c468141e01c02401d410b040031407142a580c0401c080826014104c903040382c0500070100c0c000b400f60102e003080303a0848900396902844074059407000001ca02031140503000380e171911404150480090901d00c4882d80c646041c1e400d8000001e40340203c8411040c0701180e0704c00076442c45150210311801c1e40203503100320300010703100034007080c010420f4080b40075034100038003010365540d2181c555004031400c03c407044d114001e0a425401c1401c008001b00380e502d00703006901880c0c01c078000e078142070100320b416440c0039070450044030107281400c800020002d14001c00c984d00f428880c04004040010801c00002d03000c2801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 837443821 1250 837442571 837442577
    0xc090109090c0210021b0703051615120216020405070903170c0615120a0b07020115050315070e210f06070c06050c0d0f05090d18180207080301060c0605070203070201 73
    0x341c0a40081c4c00d030f0081d2501c0c907480f12074032002c0307a00207170858070700b04440d17200320b4041e005041c0440c00780043c010840000d21a9500b240c407030081d40340e0024946d540b80b5844035443ca03030215081500426941d46005d80c1c40d400740080010703081400300075200380110b100440300c4141d4881c02c00017940401e0140d55122507008024003480d25401c1c80b42c04101200e0352400c0e000902000034607410102040713814006401070f82c120303459041018000b800c1d500b207610040c0300c641015500300050385000800c60a944c035001d040c0c04017601c0701e100460761081d013000c01030b030311070000e101042d1001c4200b40b6900f0051440342c101c800341149459295202d00086a4560101d80140615401720300107810003035010002500702031801004a03521000c07280c3c3e075480010403540c2d500402002072001c01c0264941e900500346001803d80c10540003d0030b181c4c0307018503859030900350121340040b00650140d03071010398000d55003916581c640200030880e8488072400c0d20300e1405c00c1c0c0429a5107001200b11003000d40c040c0c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 837445071 1250 837443821 837443833
    0xc0c0b090f04050405010b0306010e04031d1521150a1509030f080c12300c090301060305031227070b0304050c13051504150e041a0c090109090c02 64
    0x102040003c1c41e000304265925502c6090384146541c050000501070803411810b41014280345c20028501000d0702034035801d1021980c1402500c0d501e01181e2040850000b0000341d0750000e200444a01045e02040c41403452050700600020b24111440700e40d800380181c88003001d05960300f181c071844054068100002c56202c02c02032000c5108901c19206040c000c1d51814600b044603144075107801e0003940d10b03045c007103000b0400c2101d103c207040c1042010f03090040100d414241e50740040c0790821026044883c070318030020381885991029002000190341040c146c035102e6658890414101a007110010103a840000203c904a06100b1003c402410458010201e490030300800b20340503440900244c1d2684106407440c2d160740d803110840054910500b402180509201c02088420540c1c02051481582000005103030340700c0032820241240c528000169036500c80307050000c5a12401c40c6110f49607103a40e0f0070840006c9402d00144071061003a0303192050319550703050036400c403051000c140005030010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 837446321 1250 837445071 837445099
    0xf03021e070503070507030f0b0c0702090a0b1809030d06060c11060a12360b160504030f0506060f150901034d0307020d0f0306030804060c0c0b09 64
    0xa0140c441584a441100d2130b0940503101c1610b0700c80309900444111801c80040010060301720240c90f00141f40900050801440340e0004190410091070800740507518003542101c1e5540c20f030312484a010404444403a402c00c0d00c1c00075240c0e480f41c44003900c03203070038a5400076000e44500d022031030050b0400e100d044503c2134442007140a134800000c0703804100c0214059608040188115a001c18403900104402c540d1700b1000440240400001400d00d461840040c003c1913a083c1d1184c0c1c4201b000b823003414004031198040d00c4a00642d0809080203018a011008210000900c40c3c040c00e82240c41c45004803030303a41004a003011031440c06400360002c1c440e08407194029000006403e2780e44140041d070134200b000103410405003407031003e1404611030460b41482000707001020346040d41040c06245242c06c14000e591150320b084611700b002020741d0340c0300503240300c0d07400311019561042c00659100c1e512403009140403130301034061301c01281a403400130760801d0f8201102c10804018000528000f11 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 837447571 1250 837446321 837446377
    0x405060109050417180405070905060906160b240a030c140a080d02010b0405011a030c03090109021305010e070f090506130f0305031b0f03041517160f0302 68
    0x640f04a03080c0154410701901a003040c8094042e0000c0c051311003911010328010032080c0e40d4054442d40602410413010301480d00ca04c800c4502d22002079840c0c9030395402c3c00803d909202c2d0f840c130303024004120402c140110258180b2019910110582220700c02c03a0710001004820340891100529482012030204422000b4840305402aa00100b400b06040e5130303240500e052150030f080c01c0005035540c1910840e80e113403520659024182400c20007030b5406030380518444500c03015007c041c02080c00301c0001c810010175000700100340e0303001c3c0402d42d92620655102010305030038041d120800680200080704544684c07140c07500b411103692603201c00380c906400c0c00055031000303a400140349003104012613100840f03101c002c000c507c10307001143e0703810b1109090030303030140c0341c0d68811000e4126115a075550b40c0f0000580d070566a001c0b855184051604a06070f40e46841c04000c4444420924104060140008c00c64059100b090b1248804400604000c0707049100e603590019907007403400180d101d0701c09 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 837448821 1250 837447571 837447581
    0x70e030d050a17061f0201150e160c0503040306060312080603060402030705120c03161403150a0203130209040f03111912090803040b07020102011d0606041104090c0503060f090405060109 82
    0x2000c1c10089884028a48441c0f1703084848121201503910342070103024404842c40700f10010411800c01c6141c41c02c080343c540400c00010000c95040003403100b41c15007172000c24812980250341c001c2d01045002d640386030101c24003001503c80400304440b58000342007410081000d51043da4001e002d03000903403c0800700020420000f940301214130804d02c120360170f038a0801500700d410840c62100c02c2c60514014550122001e14904640a90440390921194408150800c2d030414061000961a9519512094021080f0550203940303e0040c0043c4801d03c0520354091040500a075202c460342c4c49a6603d080c2d43e544450041c1c0c3c16840c68402001c0410780c1b04000c0b1901c84000d150441e04146d45a402034070f15002504030039a00c59001519908641e024499002c1042c021754403400341c86405080e8640354a80180030601507a00c515201c00c924400346c0c11140a00b060030001c0044560b80a00103041f60030072240710f401849074869492951400820880c4142d60000041c4011303800d008548026003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 837450071 1250 837448821 837448831
    0x4020d0c0b0d06090b010e09160e0a1205070605040b090906060706151415041e03050601060207090b09010b0a2a0b1f0b0a030c020c09070e030d050a17 66
    0x6000000c010400e00000401415250010703240454294100345600d070032241c2c12442c0c42d05120010300701c0141900c4511505031f000c11090102c2c0404022078406440440304420b0241d841144c4400200304102c01002c20352500d8015801c6503c0ba9403200d10076551b61240b4020700204881c144900b404500e8003507401a131050025102d01d081c613080d5a10101510840c81e2040c01c510081c140c1070105416016031030008502c110740c031000007041003c00030303880d100c2e41c0200c1c00c0007401c141c1441200c04e80490700d00001d603030203401c4921545e03403124000d458906601038a200326060205480f002d02d0900301207410380300841c104500e081d040d280183c1e5240d500c0d4442408502008401107006071381c66a44000d1270f0700406601c0454603140310408602080b10a0200300710f6500a07050124802d48810744602c01c405007070015800b02d034994103a26001220144586c810312000400108907801840c58101500c00c0e02260040f42800c48156901d0003104141030004121000b035607010802c01d040300c0c0d000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 837451321 1250 837450071 837450083
    0x8010b04140d020d0b07272312061f14040209150703090e09010504050d120618061a04080a020103050a0b060d0c1808061321020c10140304020d 63
    0x82c109030703804910805502d1100341c581e000c0501c00c101c015600308606c02042100129408112080c042c000d03c1640150700400030300e00002040c5a600d108016400f90aa05000700154060074243c203a0301c0d40c4800881c0c0102c66006400151000e880c80d0a00d9001514202d03102408001550300c1031000a400400180782e02100c0c00d9499610741c05014001e000070350107039461180c81420112801d1007480c01914110450785072404000214001265140f80a40f16241610301c00211502c6d11003e07207910f0308142890391505161066624103a800b00d030461743c600350032000e0180d81e0000c40c80309005610030340c0c0c8650014004100190300c81d43c02a9400503800304001001d0081e800450300030b0b0000780d032094904c0d5451000c0d41c1c1c20f90f000000c102c465820f00c42c3d500b1a56041c0305150741c40d90070241c44091100880b040030010400d84400d400e001e1100c00070403000926203220020b540d1024140c0301400b9001441110007900e10444040801590440da22882c588490b42800318008280780c082d910 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 837452571 1250 837451321 837451339
    0xf130308070311010605060c0327120708060105031c030b031204150801090c0203070611090315041704060804080904330803070b0613093008010b0414 66
    0xd8040006080304601942d1110861410381070114212802a00268422582840441c0341803400004884240070111400d03d044c40764000000758149081c40c289a00c40141e418404150000103682421158444100d5030031780d0340c440a040d101e020310b04264540780059132251480c00e00941203060440c0300942110304404220051030b5041d000380c0c0010900b43d00c040d24441e082903109080601400e81e2100c108000c0c040e103200a9501d104110000741580d0f101c0607103442c60082001030314101c12010342558110a051550610480c10445048506040340400c942c246180001600c0c02c0d520380781c40b42d400c41d4880e40c80c0c0e48660340001e49825070181e11009010500e4444541c44090544004404403001ca004c00e4414507103d00d940110010394014040440841d4a8000c50364100c8002d440285801060490b0751b0041d19400c04090300d01d400310f08090220ba0040c80381440d5030442e09000c000c0140080c031049400c103a0038840d0b03c8000500707100078014900c0caa0b098001c80c01c002007036100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 837453821 1250 837452571 837452573
    0x102190c180509061e060d081c05061519111e06010501020c1512090f1c0e030a03090501030c03060e0a061518030f0204110d0506011b02060f1303 64
    0x88062125080074003076496209000300d00800300a5940c10400201203062514640b1500b0040113000902c41441100301803107460601034100215000120340c0520b030f00300c0031480c01d04000541802e03070701140909400710b5a80a4040d0103400c0c0c0d807110100000c5d0703c130001c4d08502c007103400544403190340d00c15000d03000016000358230720254404802e00d160040c202c1c0758541000a41404001c140c107038001d003000d084900164103000202d45038994110508099615a600c195180c007854003e121418815000a122040d2464212a150484a0f9900c10580b5038410a00d0380790134441d500100846c90091017400780358082d80102d101c0c600d00b440c0009005540352801c94030b40b48156404d8010b155240d405009a0004000d0161035001070306001d0b8560910241c14081308406100180024400c62111030846d9504d810079a00003000e4811641c84075410068803006003020343d1145d020461160510312079216160f4001e480c2500185480d040c200c0c19800740c02940e000b08520104e441301040044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 837455071 1250 837453821 837453839
    0x90203070e18040c050a030b0f07051306020724080f09010b1e0907210c0201020d0504030513091a01120b090414160b04030311010b06030a0b0315060102190c 69
    0x402d000ba500a405250400d42400c4040e030b10740f50000d80c002d0030206818000310340f80c028030079001315448091050039642c0940480f554002c2d0020b40510b07800d81d0b440060310f6a40050b025007560602d00c8c042a01d01032492010f1440342186510901094190b40090898071a064841da40101c14000100746030508200051902e07080a40c03407102e480345a0407180307180c1440200a0707400b681e9802c0c071114485c169180d9803001c08050307107100c003025150126206824801e40541c1d15203031140100317201d1400c06180c007810980200c1e80140520058880005110259018821000708200c0d040408200c0e1030004440c2c5680d030009040e81561550740405860710381d9204a80318901074590365440241e04c3c480c2c5400c1014402c1805c1810042460500c05100d068040b20212039050030f103e0042090a100a805400109030141c0d015002000b0420214403d801c08803409904409584c014410400f4621002406590180c01688500d20840c00644040346e000ca206008100d41c00043da070b149924 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 837456321 1250 837455071 837455089
    0x1501030605040e010f0509030c070e181002070201030e15181903020c12060408090607150906020a091a0d2c160b090d060c11100501050a0f0b04090203070e 68
    0x11141c03a82d9504c1764149070281901c5225000450b19010754608540b2035446a601c4819018985086082c4008101100346d0b009403d04041800c0069404103180030083c7e0380250000c500c2640804d0a029581c42c5001011855208659017185c25140b140c0354103c0000c112081c91659074150b129582044a07000c4d8102400c440c0c0b14440d60003015001400024015071003840300900c00d1307990104081c000066505001e0320303402c11b0140c402c82e8a0b0002404d04441c000a041503030850103140000c2c030380600105400802c603003e4581ca80059003603440483c0300401403008107070005003c090048804042c680e420540e0700b40340e0003c0ca96844010740040b070f18102c803075219003416a031100280d000c2d80e0888845002c01010074281c454201040040800c114000401000341b0343c655820041060178025080c4490a840900840da07144070209190001040c00307005152040703000090018850000d80200c000340c48440f04071608080c50301400e4030281d040604403109004000d0a400815140c10f409 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 837457571 1250 837456321 837456341
    0x1f08041a071413090207062003040807030e0a03140c270c130e130c0611030901030e0f030c100b1c082d09010906030b010e0f030a080a11010606020312150103060504 72
    0x1d48c80c003130b242410000380c6901d4a915110b420502c200404601c500c41070720541c6030542010281c144c1210300081d141e400321703040100754007551800d0203040040047e4104002405803003019881511203100350605c0b8048070258110303032110002654409414014007020450a1084400140c030f0345038000d00303804d0481d110345145843d260710b4070921502801c001c004002c0c0b8142800741140399004c0c0754580c40b440207a60705141e101c50380f00303480c0b040401ca0004070400090603603866181c80b84032a81c840b094024048052418441e41042c103180581030f007102c07441000c1d84072090043c2a03454a400750429542c41d01ea4101400d8541e401100500361003030b031043d0780201c859940721440c0024013002010342241c801c05180201c03503003050342c00c03107070544141c48100c41c0200340c1000540064a05114404000c007021750101d61151100e4220451a210511102c020f000c1c103515880102c8c0d4038010001c0007510304190f1408034500c0c1d104080481046139040c9400310301162100c002c00d01350794041d44 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 837458821 1250 837457571 837457583
    0x61a15160606060f14040f06031a030304060c0303050f070c1202030c0a030f1205060906150415050301051e0303120601030912051c05060d020f1f08041a071413090207 73
    0x3c1413602a9520020b8030070b81c1702044900c0ca0400d410118030811700c080a000310001e02d60744100210441071180790039191280b0050440c0d9543d515020018540e440821003200460b00f0400492111485008c4a03880780b0303d59601c0b07014240040c4c40d68940100780581d00015400300b0081e07010707840c00610460350b0050098070390000041800304000d03c119080c401030f500291801d000d0010540c2d030700d6042030b009101160b1016541552540030540b621480d030000083c480c407510380044031504100654100d03a0129011222800000c3e01020030204000d0100e9154204110341c41d0040c1d01340039030036004881850005000c080075907039081707040a407403002c03004103802107208100090514a42480c141ba10340c420b00c01401d01a02081c55a503c00d9070091045480c0c82541200c0e071200764508084600c0003050502083c1d00c0400908444410b032001c0e207030460401001d031318203011500c10a01440482d0344040c8181c08071059036400303070000951845003604403a800603032105140041e06001d03000f98 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 837460071 1250 837458821 837458837
    0x60b0a1505210f01140a0b070605090105241011160e060321030403181d070302030402030c012003040306020c0c100207090b04060f090207061a1516060606 68
    0x920001c25440791100042c03012200d4a0400c0062104059a2411201c500c500c0c8000994100d00090b4120020340203990445804501141489000d821640c00b030320000c0000c11282e25402140202e82410401c0300107074070520100000c00e800c040303c120a44100c1d0345440da00c00400750590703508140e5038851400e81a540d50380180f015207440c01e55a0b03080304040380204820b6054003a100303609080d84601401601c0044006400c0c90b004034000180c00410440300310507982c450030a410148030f00e10081c2d02000904c000924640d0182c401ca03402142c006009203c03426851004481d50444c41800c01040c00c80580c0071144503d040018201031840340300c3c05600c560113400300c00e1a0030103100f0020301c10722040c201421002e402066072401e03110641c50110304c20f584400420027600c41070784600a0701266042c00208001a81d0140074050b104540a003c03002e048140305400320346c41c1c40c0703155202c5081d42d0100c00c0843d9400040000c21341c066542d001c521220707100d120807a0b0b025445400483c00e19 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 837461321 1250 837460071 837460087
    0xd02090607060e0d0e011215050402070c0f0f12020603100e070c11100c08031003021005040302030c040b0307090207061401060206011a0403051009020f1e0f060c0604060b0a1505 78
    0x9100e1003110001c2c514101707280707554880000b045200d0342c80444001a9941c4607440d2810710305100741c4050b240140080d551107403640303080c0d090702003a4400c5450354818030381e0101d240b00e21000494105c0b1038928016803070025540030801154000b81440f07455109540700001c5090030b00e9071051040480d510f80815003c054200300071400c2032030742d0080c803c1c4000154024100d0f0010200400030350400760050700c903035440f03500903400340c640e800c00b0f9403041c00940900d50b080c2c0d1240041043e02d00c260155520115100240815610141d03030f45175264010400c00d0018000a9015282040c013403200400c2221001c0000d404c120000e80000005030401d2005000307071003c0841640401c2d10005030145080e1842d01c80c00d498031010036801a01d551202d00c3c0106568940c64000d03c0034400410352001c001c1c0c55950041100303842c0312601c2c05604111100c0e50310f440d04400f0b4484649031039000d804550760300d5542d80b009210720301d007007a4409060200443d05e000041913845110b401510707129030300c0c859 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 837462571 1250 837461321 837461323
    0x611150403120b0d021f02240a060b130e1003080d0e010605061201150e12010e0d0309030507151d06010e061f0e01120212150d03140d02090607060e 65
    0x1082200f14007030f14400c0c1103000142c40383d403000c0d0740000551301215140107101508078208400c960305038403292102201d5040304000c144905002e119420020040103540d1030040700140a280c000040021503601c007004051410920140c1c412440200c5500c0300b6104d81c0c42255079000a198429000d0359003d42d401c400b4424401c01703000d8603003203d00c103052038941d142491401c01c0c140122800341058091958030035024081301050108010205401091140007890091805d120542c1107803003262000032555003e0300c80c003d0042e0b0940c1d5018981812901d0721b42d030a0111888035066035585c0d1151042042001c1c0c202d100e418500b0b006012594035003030051600304006010390b03115914086d80e1580b20713062010540d50042e92424070aa584100e5001a80d09500d4022401d0081d4000541d0029112144105074400e15010043d0704111038900280302079840302c114000c2c04500e040c0c135000c0041030b03060080c0074007810492016142c070000d8408204560004030045906076203484044a003204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 837463821 1250 837462571 837462581
    0x1b0803040f14060f030c07050106051c061a010207230319050607031e0506130239030406050c03210f090a030e010f03060302030a0804030b070503090304061115040312 73
    0x2c03086414034180f0581c0ca5900c00c0c50700c00644020190040041c904c420400c1c203410480040000405d0070303015212110b07210b034031280094011600340d85000502e50198038401042954800181d000307104003801c04644e80c162a41402220a509480880c0700e8465502003011074040000074080c201a1021413404071b1806602420400c00d00d800c000960301c1c8000308144400070442402004a281c0e140c01e001714206101c811104401580006811a468171044401001c00f41c00f90301c0481d5201c1c580c81e400d20020214855003039090304100000c1180a20560240c440c0043d441c060304d02d0aa124580c06c6081050310864091807102c41c8104545005103018066200d0350413000ba2220108030782c0d0040c281c2007088509030600c12115840800948660312071005194040c2c1100d0902050341815040c0e500035100031070340d0314401000102031510903070036240204c40401c0114101420103409862420600c20201c009125800d49180340400c490551401035000e911807401000f1503200305400e1314 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 837465071 1250 837463821 837463859
    0xd080702070803070b060402070f06051005060f190909091a07031505060d0f02181002030406020a02130905150621060c03040606032306060a0302010203071b0803040f 73
    0x1421101c0100320840000c012504103507800140c54405903200d0b0f002078000c1c0601031001c3e00800c0c2c0d41a50a0401150b9840700780560003402d00355400d903641d2800c004241c4240e041409014034103010300030b40114040900e0581c0002d80c00c01c800b00787d48440400e02141c0f0200300581d01a61000c01034503481c052b851031203800032040c0c502400380c016100068411051603214190050800088510020400d540048802d480185080d55142050303841e2a00a110405095110348803d4202d1070f038907400081294100c824940103002a14215003c0141c1c500c4000a200420358031016200c00040d0300780150300300c0c40c043c030010181505011080c400740b403164207844030a2803510061a0103041d000500c0c42d0b841120078484c2581d07560340c2d1605801905950b80014030480c1c00c00019888290354400380302410704007038100c905a903036000030411050a1440040c0c0503803c03c002802c0843d074428101d1090725040c40c200c044c8240d0358240705155520030780c000d07912403802500c00d01400c258058070148030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 837466321 1250 837465071 837465073
    0x61104030201051c0b060403050105090c1c11030c060307030c02060f07140d0f11040603110301061407050a050f0a2a050613050613080d030c051b01090b090d080702 72
    0x160941d800a0202d2260394a00180f0710362044060310180040e400c124840c180140c080d0707848940e6440e205000c1c210a80d50488103008400b0348a40d10304001b00c00e48015501942c1d003508d00303101503e0b20038074510008038641e0103000d500e84034081c03512410300031030080b8140e80e4006080341e00d50310021309051000c0d10f0b031070211203094244000c0c4d55021019044011480c41d4007660340b00100d440c1402003c4c14090110b0050a0411a40038850f020002d00125400345d1820300501c15040044629403100340640000f04582e240c0c6c8100403400c0d0009003102c14411012030303600c40016200c082c40c02c00545075030326003684028a4a0100031401010205445019855080740c440032043c0c040e0340d401074020a40a108080303001401c00d001003001100400b4003405142e41c6207041010004010b4a41c05540450301c642e224049020b0300c24030904152000c40d668007424800c101c06900002c40f07503411602800d649520b0308502003612030a072030f030041104000501c9429003900000e060408014448825 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 837467571 1250 837466321 837466327
    0x60102061b0307181205070515040b030703020726030702190b010608071e030912021501061206030605180c12031c0219020a020f0607030507060506180c070611 70
    0x10419001c03003501d4001c102c43c00c1150903600e80561340c0c030a1031199403150b04000044050f800038844042000010398809968400704100203100b1094a03100d188281ca820030320400000d05158440d03405070a03014031801800060301491542c0318610f240380302d2011180e002c0042030000382a0100020840c03111190f0080b03400000a440c1c0e04022041449244103010004000071402d911481d61505001d03c0f050b0003054911425000a00400d10284200d42c012915007003113034041d000251814403040030041900603030b803c0c0b0f4400c841c2c0c03010389140450324680700c40010002800c0ba000d142d124119203484421030040d02001c0c54680840440d895000301c0380c00d130341e42600c00d601004584400303964400c0705d048040740ca400340d4024800c45000241e20a0300801a00c40d041e808100030f00880e000300c2d030700640c0100d410304100d50351140d2800207010171020440040044e00c01d4002d05d512180042c0300c0034030307038154041c0051100000ca855a19503c0001030300b400b001510703ca0071807e0344000b040c09007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 837468821 1250 837467571 837467611
    0xe070602070f0e22120c020a050909060a0c050408070e2d0a021c0608060a0509071412120a1808060402060d02130312020a030e1e06181806010206 64
    0xf1a181d406894001001ca1045a041d030040b8010000554180e01120351540f943c00300c000140720b078809000403031103070304a05c2d8005020b16090361014080c0d80342d5005841651240751105000340340950855061003001e0000181c044000d1010800a100c0b80804007060b1a08180c1e04040400032480604001c0e40b41800592a0404003070b226440400000300613941c20110152012040d003107014081118241080030a41c1080890714a021b000d40300014000340d191140d81c1d0791520b1290050045007032051801905a16001c000c1d40d4811041c0800c1d0f5030244030300c241c180640c2d4000d8804501080c2070404480740310b251411100010054440078104e9070402d0b500040c528400d00710340d0140c2580105282d21050300b01056100210703400705840f0080c000585010751540c48001e070a90205012210f4a900d0382403031040c441000c41c000f4a0f60410781070440030041c150304802e8014200d01d4120a000d030054030b40c94221200e02c42200b0785940f8a2034004002407600f2401402c0c2881f13490028400c0d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 837470071 1250 837468821 837468839
    0x301090e071208030106260a0204080c040902150a03021b0304060f020a030c1103030c070e09070f03020604090c11100912170402090606090d06020301080118030503011e090e070602070f 81
    0x241524494906001c12955110aa47c0e45c0802d10004440c404803440038031660301510743c014000c4495a40550b03195070800c804100403104482c4c00690000700421000e0b0f00f80044000030729144607507040050a0525003102c00d03030b5600040490000607480094140b001d079402001c5251641e00c0c0b88010212580c140c0d5005140310400071009112940b00c001e01c020359074007030003a28072458680c2d04461005030b03209004101c500e420f4403a0b1225024000010515454900114041e0f03a00a04903030b20b050b150010b410f004020550440e420001c0880d8210900d0000748003200c0b2a10340301001007000d00c09030901654240d800e80344101070010f0200750030000f05d51103001543c0150125000d4000d6030342c410104449101c1c4000481d40200c1c0c2e0344c1542c0c1000250b5010714141c40984000300880e15220135081410900628080c0104000340b004001c0e0203a400344c1d10041514441030084074598414003101990600e482860701a001038100f480700340d604000e500000c20b6200c4c4e40102c0301d89445941 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 837471321 1250 837470071 837470077
    0x90e1005130204050d0b040b0a0207110d110d15050a051510050f0d05041e02010507320f010b04290d0b090706030b2b0c0302060301090e071208 63
    0x4a001d062a480c0caa00090140e506072001000003401c0e84004a00e50710307149803042e004907801c6540132078860125000040c40d00c00d55214940c801c4841c0c0c15480c1c1d0004000c051a00c0c43c804035540303100d10360758001c1626000c8079803503124402c3c8206e80003030802e079445100342c680c01080d050185140c0000c106605600c900d54407001d20081d40c070a0050071350220110361a11494115121603003000880300300c4172070f00740d201500c41d50145099100da030f18002408020002c4416020380066000d00000c0040b680500d0340003e00c403042419220420481d00b03200008503140e0310b410906400402c01240e40c0341080c000e49800e0300b4110303010000c03c0e09440d040f02c00100c0c41c901c101242125001950040d80741d62103080c2c01150442c1074002c583c60700e449520341e2150117015850000f81025501847d908060044941d003101940450411303440346003180c2001a130100099845c1035010200201580324100214060090200d02042c55241c1c0c01d4807514056850344000303c03e00d0042f4000012031008416 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 837472571 1250 837471321 837471329
    0x103030e061206220e0f3d0e0d0806010f110706050f0c0307080405150f0d021c0c020c031e0303072f060a05070c05070b0d0f02031501090e10 62
    0x60310750840800e0043c180c001101d00302904d030a62408540401c0d80b440064000c80f8800d8103011145146c00c1001b004030550001e51b0040302180303114024040346400c190000c00100c904a41c0060035140c43c0140624003a80944081c0208410506010480d41d000e8031006089500d41840d041e0b0410601400365150f1141c481c000070040003241e00c041e804024812606d8006100e400c81e51078807070a040c42c80c49039010f0302c00c4901c2045500018402c1f15980b100f038805140713000c850079061a16071031a1001035400400403140417008011004001c003018803d05003403600e03030341c02860b8291810081c0b44c0750810344034000c540081003d5506589000000459034404000d2625000180d94041d0340010102e503084501c3c580001100c80128031600012420311072a0142020300050311844400d8031643c0c0200c00c00781450b089082c05101c05d51894000f40b14001051600240d00100001d6081c2240c000740d401414000e50500404825a4800040005430804803141c0d1494188a01c06100011062107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 837473821 1250 837472571 837472579
    0x120c01020d050a0e0a0f0e1e190609021804050106050903100b01090b030f040618021c050c040906150803030c0703140403021003050604150807050603180a05060103030e061206 77
    0x45482083e403007039000410000d0003030000340c0c0c01626030000d03169440c0e0601902d9210b00c1c0c4400002c42c0c4a8503da10075800c0f588051003000552507100540c0500a450242e91001944866000030850014801081c0c06140b1020400044103c0c000b004161072301a070101040200a00c140c005d01d40e0302041d1181d0401d90184002100c0016400580d90301a240c1d1105039400c1021042041002d40d040c00b140c85544070340e50402c1030342c0f10001e0f11007000d500316001030b40100070b6402152040305800005854680207604540540c840b58001400b5140e1a9030100d801030340711402703030881c036407100040c0024110040c045c60642c603200040c030042e8094020b001c0c040010211954544083d80c00448002c1c0d90007810040b000c040ba440040e0140a0607502640140d02e44017248900e54601041e5500707940aa60143c480507107000100b05607504060b081c030310340100c0810040c61000d403c01c40410094401c20103060503625508014001c4000c0300c003928084e107010480325910a00c0a100c443e44802c0440d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 837475071 1250 837473821 837473827
    0x120a050909130c080f10230709050406060f0e06030103170711041a09090703230102090a0e0403090f0305100c03020910030b0a05060408060c0a051314120c01020d05 72
    0x2541c00d8032444807810142052410000120304031401048903003417009281c048820040300d461105003101c80c50691500e8190031a065503207040701580f0599000307819441d048000640381d030005011190254000130114111a020f468001d41191445001c14002c0b58114290340c91a00c640081320303070080001100702c070005620740804c20384001488940c031010b0005c00c5070911050504080e10617840f9524440c150000000b040303800001490300c00d9a5001010315a82001c41416814101c485a807086031950280144040c60310740c00c011200401c012400f001e074904060601510f0669035400100343c618000600381301141c40040d49414011140c10000740b011060a0304034000e0090b800e24540c800d00301c40d180790080e9410382080c5024007003200c042c1c00780da80c0c640070000755100d584920360040e0130031000600307851160809040650b0103810304a00e82090007410b54002c900d2508a00e00054041040c07030420b0030030016500340c6080d214001c002000c0c14400107036072100f1400808081000c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 837476321 1250 837475071 837475081
    0x1802030f150d0507090204090f0207150b030c0d080d0b010906390614150319050f060c030f070e0f040c03021c0e240c0309121b120a050909 61
    0x1402c03000c80c9594011007524081603d440340c40380690b00030312404184130300300024a003504585108450031f4031741c0114164642005003055202a0150f001019410300031303503c03001101d0300c039486203040c1c0a115044059488007041210303800c40b20468011410440b081e0350510019410840389823403c5c01820640300111002440e02e1480d501c25140d50040c0c4514149480401c403058010690304032112070416125a00c000c0d442c00154030445036194143d203c00f41c07400380d100d20079244204680c040c80903100041c2032001ca1500e400d105980601101c034001080140d01004011515000003040c80c10388402c2a0400000d004091042e807824429650340c10080703481da000c1e40c1298091140c030030450043c00b00c60b2801c4001803695071005219405003104d89004e1144220f4a82c0540003218500100c6444101d1040e210f500002e0008410b4400e203030300900340103001006841c9030304944565000d50510404030700d0600106500b2410f50301c0c0c051010300781464100d0161600c0102c142c1d04420b00d50b5070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 837477571 1250 837476321 837476329
    0x6080a0f0501110a050d05060136030f0c1a070c0b1305030d0c03080c030c120403120f1a091017010b060f070b01120c0302010c23071802030f15 63
    0x2014443d010a08000030300700d22100d40001c09050b8441899104100c5961801c005480f50b110241005540a00740800004101d5542d40d07070000740141c290018070a951a0380e5021142d0041140c16168070100010402c20210103020000140c070302c4108070390601040780c0c1c42c28001100d038007400d6403071400441c0e119030340615490000001c01c0014215880307500c00358000741030004007c80540c0010469400074400050681c1101c0c025840d600103107180c118800508100c00c46c02400803001c01010f02080c0b0010300d520700030840e1a180000002410b01c00c214100100401c02e45911409084c1140030409003601c21040c18044651107050700d007905151146c0103006040d03001e84203a001030b02090b03401601e80c414003d0040e4130712500e49000d690340c9680032180f203c0c0d500c1e44000c00c030720240c64051005520036030f62040380b04c0c414080426120f2404003074a03030355180c01e414408641e0040c082080300c1c6104451035011004240411443c50600d41c0d000c0c0e2140a004000c0544040c48204140d146c0c2c032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 837478821 1250 837477571 837477581
    0xa1401090207213605010801081504020d080408100c0f02060105010f0c0b010b03100617040f240b010e0109121719051c05090a06050901110703111006080a0f0501 71
    0x1900000d030700c01009540350b80003c11044c0c802c464100640d06040810785500400101d8142e900b44030080099990401802c190b4183c0280103d0300314030303d031000c0c82c0080c00301c501420140c46920301420302035910b618071a0441e42e117000800100254a003030f81d410aa004030744c039410764000f132174048605100d044041da00d03c40c030b00400511002d105070000802030307805ca025500070078000da05040403e980790030854290b401104504500d415400116001a202103d41200d2038802e0340044124808800c183c44000c1581030314a41490310fa884800c040d41e0312a600400d95402401c00100860410108003002c0c205290b009021003086810701c800421030005541078541188004126442c0031940105107030400200a01c00c071800140841c40350046000f0148146910300080c00b4200258407244003070100641148100d56842a03c10806001100107142d158001d4030b51005906506e0302842c609642c041803107031424641502401101000314505901030b8100d140502100843e0804074010f003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 837480071 1250 837478821 837478847
    0x120903020f0a0c030506010e01030305040603020a0c0f0609051509030a051c05040c0602060604090305090405060a090e010c1e0e090a0b031506040c0e030309010507030c0b0a140109020721 82
    0x71090b12000320402c9032026880099030700c00c0c0c00751096640e03a050101e02200080c04001c010070014001402424403da01a20503240d4074903110b480d0302d0841d00c641c00501407a03041a03035803544030441582402020407200718813007681c00f82603e103842d09803c2c02c2c2e12806608004010000c000801011085041c0d100001c408800c120411003418546414061200e180c8200c001501501300003824915013417040000c060307059203d6a18088842e82008002c01d001080d0302d51011040720b0200f07503c07980344a074001d8000c0c2c0500000f420909110042c00c5003114000381c428450103458420b00c1c495104200400d41541582d4400c050b448030054107010700807d103940c0341c01d881800c45806e0100050000b80380103d2007a07604210440003030404071020300040743d607190513620411201d202c1d54030074002000780600a14004140c09103540d00d0160309241170352400a082e80b03c91200c3c0a05d0081403400d401000e03014811450061180c2c0e5090428000ca0000a94042060340e49840c0c1c60085800444030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 837481321 1250 837480071 837480073
    0x6100501050a0e0f1f0f05030c1602031903030f06081f0203130506072f0d051c02030a02030621070306110d05160e0a05030c120309190e1006120903020f 67
    0xb08452440c512801805d210701080007070001c1750403c907130350301504c201c03030144400210303840c60408424070b05115583c900c68100c1c1c045c0316456800300d4511086980401c031034429a0f02050340929604c40005640071900312000355001440d01a0801002d4038400c008090600c402603101d560302d003a512001610040050001d00907202040300d04c503841080603412504541c4004514050f402c0c18084140201940c3c61030355001d2100840c41b10300640280c01c04a040c04400d0500d1021002c1c11426604143c0e0040002174000c03080c0030f001c1c64003555003000f8094480801410406a107a02c580c1d5030f01c544000b900082c2e40d85244501000360760225040350190510502c01c1c3e080061311419000912100c610015428001c6402c0c54038010300d0140031210018001c0c444480c200c000c2195840130000340103074902c020041052151254030801c5000801d000c2e036195410310305048034101c3c0600410b51a1294030381c800034801e02c2e4000b0f00c54005402143c174002869809464240e103003001141c481c01e51 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 837482571 1250 837481321 837481339
    0x506070305220509150f04020409140903120f1f0e0420030c0105030c0705010507020604030f09060516020d08180a05030106320a0905040506100501050a0e0f 69
    0x505402000514a2510761050002c40d54500e95154070902154010141c0c40803c01d008102c480d000f010901240b00b400810000408091030001801c982c410341c044125a0348880103a00c0b02d04c0712003131195101c40030318090340c5864191820501d00500061800d0062410700010814010721022a5220300e80f91520201d00903890b0759181d40c84c41d008a40407961514011050010f8041c0924091a010f00103002040c6002c400030056566401c000d126010701c20090103282c020510034003880d401501c06402810b0a400c1170b00b001030141ca400300303a940a0003507400e000c00089a0003000c81d0345036440410a1002c8902d2803000603604400c80001821081d404586060f28020b02800d003614201c04451800d64030b9664400c0c542030710041c5c481d010241e0f034643c441c1c0c032481450a041e082041180b1404030074440740080060701c00c003821b80120081c1c40c2d8610411041140400911740c215a08811202ca0b043c50134000903c94424440080c0401050900089080c0c85510161000440051460b25 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 837483821 1250 837482571 837482573
    0x60108132a050f0a06050f07031110140717011202011116091d030301051507140105040201030501080a15020d1409030a0801122d080c1b010e28050607 66
    0x1c5094078040c5611500c180b1035803154518107a54890112003250310b44500709080801541d03105d40102a0681c00d200d82c05d8030000d01c1c21420b015442c2c0c100724a900004040400205851201744010848c42c14400450030b0321940e0706d0b400d040709044421032504030381e0942c02031004031100e25041841d64814861600850100000c8040300801d40e451200e04002c6201003400c0e0f0341460704a002d039590b080d04100b0060205e410107141c2190800600c4210038988601c1e17036030b2485101182c050002040c0d65a13418802103607418000d8600520740070004201c1440c00ea210300c1c20713101c1c90301170600449130300040c41402c6007c0380d0010480d400c0d000d0b101c1a0700e03140a0301d090351640c0c040101c05002a031010004101080b80c120583c000c281c04c514624140c1d221001d0a5280ea280b007030340351041c419480c02c100001142000100803c03501d0318054490340030101c00782d821520803100158140210310244d01000e0700d84007100b2120390b202e03078944035000c00b04401c0f5000c4802e03503401c8503401440002c0c07040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 837485071 1250 837483821 837483893
    0xe0901081221131e0809040c0e030d05030604140606091318031101060b040f0314030f0714010f0b0d0204180f03050c060106020115030f02031609090308010b0306010813 74
    0xf0889014886034100c100088401c1091300c84205030040c001a010300140b62942400c1e440a1010141c0b410040b03c40c00760400041d25011462740c01c10001103000040000d1f5040c140a18110710940c03091040c940e007480c10018083c2d0046c0340240c1d00821181000c1d98a40c4100e4010f00900ca07200741d0300c114400264117004102003403201240d2919030038464001501c079030306000c84040301d03006203003540114115074805e52401c64410f840180c9102c1030202420080c8a1002450b40d28840d0001080c00220500c03090b0a644e08124120300d0130303140c048240d0060b103c0341d090134410355049a0000721a80350544042d08000b910b00040e10040500e030302e0904041d00400100401c404442c100c0703445030703031b00c5104a00340ca94450a040c900807040307404100141c2000c0e98483d595100900341c804440740c00e040c5d480711000c80e030300c040c640c940c480c44114141600421480e0140030241002071035031800c000046c10b10700001d02000c002424829140d400c3c400e8031600100d28080c43d04980c221103943e65414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 837486321 1250 837485071 837485101
    0x62d061401030b0d151a10080609090f06070801090c03060f1202130203070201140f0103030219060b0d1b05010c0c0e04051e03071a1612020c010207060501060e0901081221 75
    0x461540e80b0000305000d928540070350b4a1f00804203e0303440340d29582d03400d07040c0300e001617001e0b040c0107003482500500c080f001c0041c00344901c0fa4808e666004019803501c4d10300002e40e99450000018945400401c1c030130141c041e040082940c0003d6020389040da500e0cc045030714611320240f0086c1e050b1011040c012816819084045a61950340460306d142d01c2d60179690300380c4602071200801580c07010000701c50f00744800c0c0140c24018010003000445254550100760360800040b02200c07222911034410412070780140c2d80001805082c41c150b03807213606a40d11502c04050300e004200341c100d0b51000060801008000d8508442d885961003071100915141f0300e83d4a8001010442d804481e000511881e2040c181d8218400c4464180704107218807903a10a0b1410a20206034030080d42e0204045550b1440074001000321500c00c0d6800107056150800007040c3c0c1240c034003030f1480b0740c2683e0300400841c40c000610400c3c0103e40c20440c0d41d11405440c085c40c4c216807120010120805800030428507a03114111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 837487571 1250 837486321 837486341
    0x30c040204030b1015230c0615011404180e030408030418060617070c11220506030304030f0b0c251401020c0a1e062d061401030b0d15 59
    0xb0211141c1c4511440c500c0021740e101d50390000315080702402024400680713481d0300180800c615483e01602c00500ca08001c41100c2c40e00b54501d442580c3c02d401c0d40d00c0000340e8981c0e4504c804036424281000d2110010504d46d5200300340140d2540030a403001d1a050048030b0080c140720080782d50307a642e507094942c42202d8101d003090310f1170b140c2400018042d01400708c04044440c03107030040c902d5a541c45001c1da07410700c0c1c05205481d0400c42040380b02c4151126144905d00401c5180e1420340012091544005e4410040105002c1c0c0c00a100030000200d014042012055208a02c14002d81d01c1c0e030307501244d500034504001b041d160050a074000540b41e6000103c0201d001d10b920046c1c0072031404440c2e090b4441c4d1400780070b10f41d01040d450400b003082a03c011030804030402c02d01942000c90307140d04068400342030b404030074450740100750541150300d01c0800f18006401c00c0b040c0803162820180000d088507880c0d8540c181900d0701252070050740ea2038500d880e032030782c810a04031340d054503450300500a00041d19 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 837488821 1250 837487571 837487591
    0x130204080610080313091505090c12011a04060c03021c0c120207030b1b040302060c01020a0915120209062701020d0309022419080411220209030c040204030b 69
    0x20103e03401c00003004850300c1840d040d0546282524100520300202900e0103402c140d84414040401c07140d0300e0401482c0502110b001d80ca4036548a014900c00e10703441030307000000604020038485a81c110000a0b80c04031b4141d828400d06014860406a003050301c07201441d03030054038141d8640541a00119503202c941c3c010034181c9600f9500c0d400c01da0340d542d92404017510022000c40014030700403012407140c41b2800010701003410190360303601143d01600131071035401d516500440d010f41400c0d07000c000d4000030012440705064144c017500f07024118241204100700026000151400d4545568088400c00c0b1081c01c224250020310443d400d418030740084265005000c1d407240740c149103100e03000350340a046e001012000c0117903505903520070509480040ca904514107000c03c51850401c550000c0e04424992500000c42c5800d01c1c1c4100401f008002582c03140c41780c6c12160204a658101c08408107402880060ba103a06d43c00000e4079022000180e25445030000502008000c00b5400c0f180c0640a090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 837490071 1250 837488821 837488851
    0x41e052a040612050906010504020901030603170409153b180609010e0c060304020f27060103020a020a260408010e010c020a03050d090305040510020a0b07021b0f1302040806 76
    0x4000f90544a040d140d0703e680d584a6001805940741550080c0401481414001092076a0340d40369042c07403401120024075405d0114040003020b41d0341c011568908104101090790138240146041410340a02840b202e06034500800d00c00030400302800504050107401101e02d601c0e0906a107444034010340005039681c0142c50100d000c0fa001401900000c04004016003401500c810074070042e40c2009006a03071003030b103950321904203031604079604454100b007148185980604001c0b0a51028010780340604141c070403c907070041a80d0200c1c2100d4040c0e40103404200c0e241d003075030015050b1400a40000701c44032000800003113400056002080004414009000030070f2040c00c144d865400507000a80480c004100c0d0706000703001c681c803140001c0d1190924034145134070b580104100c100403526020240c3c6c0040e0b403c0c014040030051655100000d440149014016005440c1280c1240300307000340506092814100c65659208092040c0ca40e24681151107580d00e95010f65254020760703200d40a01c00c2a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 837491321 1250 837490071 837490097
    0xc190f0b0126060606070312060504020c0a0605011e0b0c0f10020705060c0a0c0b070203070c060c0b33130e0c100f05250c23041e052a0406 61
    0x10503d54400c1c24028125418105a92802d4418810941c800840c42d5501d940100e4983c1d80d61003d8840414035500034160311a007460000101c42041e040003c6500904100c00c0a203001907805000f9174601ca88215192174241c1d416500e00940043c1d06003160065081c100441c00080e80680740f003d009004490150b02c405a11100d81c0c420071a0810020b960b8104c001d000c00d140101c0705402240d68412245030203403e4407098107484490304400000f800c1c1e04800b509000c60b400792a0b4100c0124954046581e1407004580048856005d80003030303800030440d80780c18587e030324002d11407210103040090100300701c0c400c640c58a45550021892203131329048030712018284960301101c800d40b4280c581c9440e00c240745174207002d182d05002259040c140600140341c00034915441010041c280d05014200018410221681071441c00c410340e030081c0d25100c0000c10481c0074000f51030071540305440c009115118803c11503141c00701d0b85240b00c0201d603444860301010f009030740184121481c541d948a106403031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 837492571 1250 837491321 837491323
    0x40e0c030d0806032109271003060c080702070510020703060608030d050c0703170c04080a06060e0105120303040f080c0307080c1006060f0e0109080f0703050f030c190f0b0126 77
    0x802288040079407041c04100c0107818141410350818607c00b4101d41c11809a5a0103211200101d492860741c03c03082c1010020402e440c0508038030244241461429403030a01d200130340d201c006100b403034811588a50440e243c00e0081c40140040c3d07801170010b0102d00c0d00c5a5425030b0302c0d4010121242a1864000014810300821007560303c2154075564052000400864201e64600040d00c3c4a0007410204400100008200701d08040148501c0780490118608440480f4280059110a0040070f4041c01c0c41b8a0101c084200e943c401c0d4040100d40001101d410031280034003641c0e4180a05200006c0c0b140d040c080c0c08006429916201c0040b14020200740880000390b4006100d850003050700702d640c0c0314070b1600403210f0999142c4103241840b4119a50600e661405500b015502c146821140c170034000d021080c0704030b440e600d440300000c5182800e602041a6280c1c444180d082d00e80948806540400212070340701c00076182c00660210300f0f5615410904020340002d25010101420030020611070306c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 837493821 1250 837492571 837492613
    0xf0a02091302130911031504021605010504030f080702070b1321051b0a1503110414090a050c040b0a1701030602030f06030c01051e0d09082d0405040e0c030d080603 72
    0x17990300d40aa043d074544140c403444010340310402c40c2d4802c0d000d1000350340040401518901281c020400400e59090a0501614941585440c0c208018a140402070015000100c11085609075051260b507040b100d80c00ca034201c10150044440711300c80d000200341d03915800c0c801d41241c0d4020760946002401e2004110384078156940c0264000340c1c0340c1010455026110101603425100f41070100c4c082d120011030031556886a080303a81a805040d443c0b42960411101c8541e00c00c0e03d801040010782040c840304c181501551141c12501000024240081c0340f1440000641c03008100441c0c90b0742d612480c021019410440310350000d000c0c8200001c88618000400034800390040c0c40b25481c04041414886000198001d4403038280405c01001184181c903102d8500021701500344035460b0400c00756a49020101c212881168045260f100c00b458440b0108a4007150003c580000b040d81100703103e9410f0504181c40268540140c0c1a0079084075088041e840c860b401c22020b40d85405101100840c2d040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 837495071 1250 837493821 837493841
    0x10803070309090c02160e1602030304020a030605070512010b18010f0f032c030a0206090303011d06120d0c0204060b120406150e040f1203050c030f0a020913021309 72
    0x24000420810403a041a401300c10030701c440344140e8019049440c0017810411640d0711512075802001c080044159554941c803120000c0c40c03002c0c62440c2001c7c2c00141000040c1c0c04098000365031040441d00d258040e00c100c03017141c0c04038407008a2a41e960402c0751000d0304a544c13143c8050f1070704941d58040d50320a1b01c00028942c00da48419140382c0319440c4c11001042c00111a410034071442001850503078800340041d4607401031307a008560760381403803200034140301340501202c00d542d00a00c01444141d140303040080501041d50850140e603550790f40001c50031540c66544801a00030310600074500d69000c000c2d031404500981d81440229510380300c4080c2d500c14006050351081801c404500000d0190308040340344180e01c0c000c0c41c2490340304c5900c1110400e0555040316000343c00c00c0d00b01c0800c1001d603105c4000c00c1441c01c00704454501240c80c5041444000e1028122143c4e002c009004250142d0644003403a6016282802d03004030348130080c00075402140400d0600040030f03000079450310140510303400b00d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 837496321 1250 837495071 837495077
    0x1210080a03050a0914091807170c031b1012021204063c15050603010b12010812043c090e1b150d110d0f14190902030a12080108030703 59
    0x2580c400c5081c0b40a8540e400c4c1f02880c1d4001c6ea000014055101d203011001007444034068100390036002e0030503103002ea00d43c41e001880350820707192000c559210000d80810704081d0428400907589e142040d0020301c1185200040c40c0d60050922040c01055030041c25425905460071013403030f2050000c000f85410700e005c1c002c0d4030300e401c00b441e200070070381c40d00b1916065501410501e00540c460002990603042600324052618002c0b0b84003008124407021640100008005400f87c0500c0750b003040070034415070160480701c0400100503c10a2005c00c0b46c29204a540c1c9418002641e01d0701000e2031140852050f8120303141040e00c08070700e0080120b907489481d014410040f000108010501900700905810544007803418040a04404c105000705200d200e00840841c0ea02e41a0300080c10447e0088000e1a52356803500a480b0440415504042e030440c1e021100a09202e42640103000038240c1840000d401d40526030b00300c400c00071407484808101a45403034025880c0c2c1c171103405030794900032410042c2c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 837497571 1250 837496321 837496339
    0xa080c0421060f0e210d0606030506090a0e0a02012607030e0f0f1504080f0301060302130608090a080c03040302060414120d0c02010f110d0c03030b010c081210080a03050a0914 77
    0x3001c0290010380085d00c01e040510f410011602c0010085600c035600003400301382c035002000501c1c80c0900203503a100d86100c0c1d0410104818070030343c40e40c612510100078180075046401c0b180d900481c103c958481e001e012410100340ca0030007c0140544650360300400700b4800c4004174000c204000c2003003e01507219a00600010a41c60300034040c1d4035019005445800c03007081501d1001d080b460046000e450b05440160352010002d0030009800c180350b0001003008068400d104000c000402d01000d0150007980f425101e294007042c003809c5205940c0000c2d03000b84005400500c1588440030080e02803011140d10310410020001151210141c1001a0011390303520300d003100542c0240b0180441ca03215203081103c2c85a05640b40d07141050307503401040480d80e4540c2090800d545801641c50740c44080c030786003189400036500c808060140801035142414128002480c1e40420342c40034006092120895104849a0402404c15449404803100150340d5000100c1c040c6030071100349003844400703408010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 837498821 1250 837497571 837497593
    0x2040b0f0a0c0c09060305070b0a08060103241e090c0203040608040515010b0d05160c0206071b0609030b010503150403030207060b120304080c0904080a080c0421060f0e 74
    0x880c0c0d07401640158144601c50301060040380340008900043c01c00c1100c0003980038150f041040c9042c2c1c4a9000503031500d010454030083c2a4031680d0617030010000c0c01c01142d0140f0700304095111028100c0100c0c8a541c90010004000b1000401160711030140410110010785440103401500d00d403612000141c1d2081104000191042242c540c2c000e00510940b02c840e8a43c2200c3c80701307081c080e03000e18004600819109003080b094860b581c0c00540c514100504480f0100d006003041c0809440070b4841c400104445042c442c20022901c140440c40101c02e400d03d44900001c3c1448a403030200b03a40310031000d4000300c0c00d8207002451884002c030b080c4588040380e85995040b006903220a1080311000e44520000a40d0784401c254091700c1203c1001450f143d42c00c10500c42d10707000766007001501c140740100602c00441c10b504202c804000e00340c81d00d0401030395140152196440745920020121000039105d0400c8070000e902010041c0c402c02e420711000c4254132902d000c1e1800303590910801d410110900b5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 837500071 1250 837498821 837498847
    0x9080f0318041401180b03030a0804020f1801120c090e0a05070e0f040206071a090d030c080f040204020f1902010207060c0503060f091005030f030d05060a1a1602041a031002040b 78
    0x14017004405203012881014540c0801d0070750300000303c82c10105080505000071450144101c1c1d040c40826162525454071500c40346a0880043c4904084000509001403e01010b860500c4c003616440f0018003d06481c01c00c91a600d03000094261a907015800d008240c280e0b010f001e2502440c0f4641c0d58002d01d0700c4a80030840c0710750080340c0807196102004600740d1114100d0078204c0c42103140d00060124220304000240540c4d03020400c41c4100305082d410030010543c4e41c06056002601528010703203a8060040c11b041500c81d04290410722840a01224251a815002040300c940b00d032000f8010400040f509031500d0100340c07042544145006008241d60034100101c1f940450081d00320760910355144046428042410003200c2c0907007000a18503550111805099000350b003d43d402d030040303803500d480040c0c3c41e21411b11000c400a0b002031102e50000a560711040300b07680050007000504821201c10043c843e00c0e8080368024068020f14901c41001c5200390b400321041d00b40d69915021110401c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 837501321 1250 837500071 837500099
    0x24030c0b0a050d05071b030e012003070f0204150f030c1d0a11041e1508011d07090e09011a040b0609040f020d11030a0e03160209060109080f0318041401 67
    0x200c810492041000e4404201c40041c0402c1c0303030300a1703c3d05444400d000000411810b910301840390030320118080ac0001c90800021240e603590800c01d600150002e52001070040e0410032400e0091000c407420101369010030503071440480c0d101f194251043d070358816204180b80700800010886481d01c60001300c0c5040e054105803049078203460301a18142d200c0031451a003540c4002c0003564006260000c0c481c07100344503004503828516080c12000380d8036240cad12145c05002004003c49012030100801c100a000d060080c0141c0220600c845140c500318407164000d2000404042d0002c5e20b40d0100e03a41e9003003e120f46000104094001440c04081c40c0900c8041e001120005c00e209500b00500c000c102150303c5140c2d140900700f0140c90707032414520809000d4914181d909801ca800401105445d9944881604100396040d50340c0702441e41e5031001a2091355a80e40152100d005181e861040e0000210050084d9043c240b87c05088646140a1000b1141203002d182d4100da150001840b00040c42200c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 837502571 1250 837501321 837501331
    0x20927061b160516060905180126060a0515040b01050a030e1c05040e0c0f090f04020c061008012304060b1c03051806070b0402120124030c0b0a050d05 66
    0x802d4900b80302c0e41d90301032510401c460501014101d00c5000d014555000f03101034004c1c90110741d00601c000301005400003101043c0f083c0819071004c01c1206184030410700920041e0405d620684903c0d19055503840050842140c80408055400742480c1c0340f480c061155007903010046e500c0c5401e040b0020801c0c0c0091258810404aa1080082941010300c60354124140041d050761055101c0c2d10b0b20036034451042d0040d00210595000340b000b21010075031a010344405d150300315840c20ba0100c100020800a00c690301405089003e0b44040011010700e0b0584041128a031400170000090740c521910309120a8040588245940c1d07008a804210702d60000b40009000410030514000c1070f2200c03d5070480380c4c0030220081540481e09030152042210300801c0b15109581e518038164807566008001c9000400c003d20480c50a2465031881500f58050031710340c08492015018044141202080c040304c40c8401c075020a110480860429428000e945044445444840c00c00013a200080d0143c45c0c0101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 837503821 1250 837502571 837502597
    0x8010806070206151813020414010e04111201090f12140f031e07090306050c0c030a0c06060f120605060d080307030c020a0c1502100c0e091003020927061b 68
    0xf1108000045c0011070300d020702a001012410400c8030710511050710b0600d2510b0b0a07504c00000104a8005400042c0c0c0d4040d130320a00b100a01c0c0d107078400141004100e1203401842d1f62070070580b0010060040d100c25101409191400c88618044e8011035040c0b2007040c00000890301400410b18a010140145801005e680036219400040d04410168004120341020000344413134800c20510a80b4450241c01c1104412924540011091403075900c0c441c8004110400c04031720f61100911240d90301035005001c0040c4049140d50392050750011543c0c1d130f0a0142c40ca1403038800480c65505d000081100400d50000b501419031ba21542d05900904007442e500c4154001e2101c00c800250449101c1ca0292003903105035520302d01d042800a1400c0b00360001402074a1801414020040d000a0000e406840455045400307540300e8030f240000c1002548001e4200700b500080c88051700444524000d83d1854080c4400c0701c0c90035124003582d0301c0c815151000030020f07005051001d034400070008d040c0743c1c038803803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 837505071 1250 837503821 837503839
    0x207080d0207051b090f0c031f0b09030c030106060e06070501110a090e100501080c0a050d06030302030403051015030605180a06060513050118050402010c051203070801080607020615 80
    0xd04090140e03404114115042d0f08800d4a80c69010045808086201e409444000440c5880660500c070560301402a81e808030700030001481c1c1190b17a1141c4003000600d040210710540d503d900e04007540e0001c4030418840d00a101c012192418144100e60488100da0b0354828254603603000e201da96030010100741d0300e554071512221b20746c40d004d40c01860440f0f56a6501001d1524244046540030f001908148a00007e0102000b26a9005201030f403c0540c1d41c0409680b500d40540c2540d0030f1040c00326894506040010000030701d80c004c4007600c01c4034003403004e03942d000320080102000c0720300c07120301c40009841011091000c05d0071540180c4e0b1200080e5095003804921005451a122042100301d503107603100c8509000d81c0c140342072020b440e454561b20070f0005504119010889051483c0303000c0113a5030711000103095a11850b1451070081d01f16003a10a500ca120306640c000d54022141440855840000050003000001d10704d44207200c180d01611007521048408501009071008075913020300c0c61 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 837506321 1250 837505071 837505087
    0x623011b081315020a1101030c021603051e03030c070303150b030901050402030d172406180108060a12170d0c050c0c060c0706050309010f05130302010b090c0d020708 73
    0x40004112501000444640c01843c0c050b0320300002050001ca002190003807501d48000403058540242100001d0901103102190701100328500a40740c0851456201101d07400070034070002042428175203d10f0201070b032140000c0f0b000903540e840203940034000308008001d0725003c030344281d0081601d0340322002e088140300d030f880101600381e40040e14110026559041444114901082003090181c0f05041c04d0240f203816a07410b800da400001c01c0420030014207101c0d110080e1101109504070000281704a442d1840c8204201e1000030898110b404524000c001c240176240c54010b0b43d045174801d000140c582c103495603408003c2008c05840b000485c0c000d01c1580907000b4580a4030b0211a82d0b0b503140390f2915040c1182c00e00d4260303640b041a014540c104156030407020041008400c0e1341e09030034020740e00e4840021043c010521942c041600034640310030720400b101a1401c800c1014007030350080c00484c000f0420008184002e40304d490f41c8000c00c01805020f503a05401400314140921181d0341803000d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 837507571 1250 837506321 837506333
    0x1d180109110904060602030d1b090b0d060503034014010908010e01020a02071d0105010c0f050d0c02131a0d050a0204022b02030601080601050c010902031e010623011b 73
    0x545c02120240c0c0001c607002c4401000c0e031050a03542503600c40c46800400303c00a000e01003038518011082e200d800020303280c42c1d8500350740001c0000c00c800780880c4d948604015a4400380204c0c0310f200328122241c09545407242400e02c81c200d0100300305c1c1202c1c806440c41d12915181c40c85400d00c0040c144404100c002541c002c0038030802c40c002c3c0c05c500c00035030f440144490090400f5034a4010591151101e84c2c90000800d0380070505054500a0a1200e50301d072a0341800940844d10b040b0041c07052280703174048840b0315404414600c0c5144207803103605c0f0350f00b8840145c006540e181031002a5005030300c0e0b002c04d0940340190442d00440d01903029600151070940215040c0d030310045080400c01001c0b0342d041c088590f02d00c2c007200725030900030342181036042050008140210140207541004000300d20344036900002c1d402081400d50040803244a62034039440c1740349914481300c1c44c00e4a9460302e03400082301010b0800c58840307080c504800c413030701480c60303001900c42c40b0000c0b200031540e40100d43c1140002e58 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 837508821 1250 837507571 837507581
    0x2030d090f080102130501180909120f0c0b060f0117010803180102030c3a08011703040f0b0d09051204030210030e0312060f03030a1d180109110904 65
    0x20195114094107080411440031200603902082403a881001803c0b405c0382d02d8400a001c1c0e6a0910705032042c65481030034550250300a8000c1c0704082d14203140b031f008122030050a00c030300c90002c0c0c071040302c200c850400035905c88100b00e5000e041c4002c144009895460807041e00000500b0504040a000b091842c040300640026080354503941d00c0054940f0042203101d01d0092104824801146460340d0007020640780c1d450001521440b0000181441c1c00c40721441c920705a9810040c40b032646401c00d01002450b814080c46410801e81b10b4003070f0703140c070900040203e80694a00c1a50f0200d59803a00484d490a07a000010301040560740300e0b15407001070b90502a65483c5101103901c90b44640c2140100402c070310200091790103051412403500305c00705001c0180c030308060007024a0030700c40c0e03920380105012401c4c03002240c0d2b050000244442500360030421900c41445400940000b5002c04011b001c142d1148020200001020400420038450160041003050051540c0c190403d086240400d060b16 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 837510071 1250 837508821 837508843
    0x17010501271716081207110d06020a022d0318060f0c1b1f050307020a0b011e05030105090c13060e04140625051b06010b1b0d0807050a0c0203 62
    0x5040f8141c1d80c008200700d111030202900700e042c0980000d000000019126101701480100650054070682603140e42d80e109a85056030414002d640e1409c0d0000004d44480b01244444440c004c60650000c509401480840b01e0780c2109009600c1d08503d40700ca03111109010340c040b94400c44c1004410f1000d0b10301000383c90701400050092250140d100901e4401e045659041806081c03410002c00345883e5042c1600c070500282e0410581c0c0b0348030700b00300320b04200e100b48014264408120002400c502c0d03c0308413421420782c1e900390304400c644960400d030030b943c0240c413110544c0d44a000a406a40740524006811806a04000030001d540f20640059844129000c2d01c44c6519108103107120b25052000c01d60150490021038a00c82e0240131040d00d040f02c40c84c40000f041000303e844040d501a025145441004000481c2d6448da9104080c042950041d050a81105000440896182400901c013607815000d52121101c542da5810704540741c3e00a4043d036000c2001e56425000540c4050164203024 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 837511321 1250 837510071 837510073
    0xd020a030c2907080a0309030203160c0510030e070e13060513060b060a090e06150f0712020a030905130b120c0109050f0d12051201080c01170105012717 67
    0x100b0b800301d03188000850140301c007030b42248040040f0000103202c3c1040304d5540605040001e54242c0d1070804034038501a03c030825141c800103511990900144042c10400c40d40704403400e10030101d0020080381a46d0099414400603408124140903404104140503030000030610480400c2c00780c0d881d050b01f5142d041c0e4607a0b80842002c0030a10901075180145a49290165412482d0400c1c039400203000041d14451031180c803404001280c445e56070440002c80078640014515102d01c0900c440741455404901c00316050384541754000740751030001c540080380319055111941c1b11881c0c1000c0c008110028054210755540e40e851604240d920307840c41e6144000c0380401861f02c40b111000151590300c003604201d210f00346041c507006d000d50368020410701c030302d901c441c0c0c03e08412155501603910b80104246100c1c0d04410b4000404c04010000c2c038481000001d0780c0300303501b24504903e120b182000c2800742500181c084c246aa41d032200740600f403044480c99040c0030449694584003041c2903600702030f280c039003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 837512571 1250 837511321 837511349
    0x60f0315040203190f110105160c170a0803130203010216060209130218060702030307020a031a0a050705180a180608060108013308100204030b070c110d020a030c 71
    0x30350034201304041c052000c02d088001ca808080e16444150103180030002d01d40410800b0300c40459100f42d040c0c0d1482a4680092440e020503458102d4020a040c01110a100041038901c2000702c07000035580300180e00b0299661650702c541551004400380c29034260782640d000c0207031000b41c002040c01418020300803d001610b07196040100305505200d41c0400d400d460040c400c1c030f11024801060380010020444490740e07108000d1012074218001c2d00301c00396105004a40002c103100300115040e02c210002190400582c0d104e00c120717000c0701e03020b50b06c0c040052014414410b190200e0840101d0308680240501c0070b00d503990582c0f2000c40300780d520b03510020392666000c01c52900108000ba01600c4860000d10900c10b42c007040040e1444026600ac540c100c10103c02101210b8203030b80c8401502400098464407080014604069441b520049800340402c000240c1d00f01c1c8a000c00c01a20f903400502d800440741034100300684c08400800c2641d100c58008030000c00a02c134144500700802e091060015 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 837513821 1250 837512571 837512573
    0x513030c0c0e0f180a0b0604150902030901021c091a09031b01020d0b040504020607080f07050a061a040b01090b0309030f0403120206010e07050405060f09090406091424060f031504 79
    0x421304a034100d1108496109003008800581c09185803070b41b0203002c1c0c400084040310301808070401043c541c8014034841c800002d0202700601034000b000040c180036841d4042c00440c4c009a8102c94010340043d21500b0b84681d10090052a000416003150800701102d041a01c0802d00f015084100714050709070740c1d80001c1d42c600c0e41c10180a46102d690044504200c146015008100d040c81500c6004001d03050009444a00101da5802c0d140c00640107812610a1030440c584400240710307101c402c500c0341200090b100340f039203040d014030841c10b68103030345504540c1d00c0c1c0001c4070304d00c1d007028086003002e000c103002e26010f400c040405400158082c28501541419000300a810120181c0202e03c1783c000348800c000b40d498000301120221042a0b6000c0c2c1d03a541811152010340c001c0300482a844010a01400144840b5411002c1a1030164001003c0d00365a0b010083ea00c45d14020802a900e4000122001c0440603621a80d800540981a030901d8059a0006401c010780c00c00e04844982000c1e003404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 837515071 1250 837513821 837513841
    0xd0b0f041407180b041e090605060f2d10180b030601080411040f050c070c0f0513091b0b03070f020307020f0405040501140c09040f0513030c0c0e0f 65
    0x900007040000e060720604162150f0240300c00c04803a80b508035100e00918896460700d90250b540081c0da14081451503c060f100800600b06801065941c41d091030003240701850403d0800d003c2c2132740142903c08021065030070862001004480160060b94080c03192143d07142c01c0280481040144d40f41088500c1c00040c20180c108a41c100310b400391014001c02c602640c0182d026038102e0707048403900c02000d004600040261501103000c40c80c01d405c0c4018440741c0e10b4000090b00c0e0640c0b00f0089542226182c240c4000b194885205440e0301240c640701d0a1240f964a90005402901442c012940510b10b003819241c0102c640d4401c4041c2900007040110059100e00e1030061046c66102443c030f040c0064001861b10482a038000384a0390303403500032404204096003d0000400100380c409040d20385040d491403103821802005020b207003800580c04207900d182c4503480c4503041c2030703805600c0c0380b00079201102d0416040b6412900050402c40103d00d0b0f58001000a2043c03a11000040161400524107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 837516321 1250 837515071 837515093
    0x41103150a092c0604170705030c0102040b2a0c040f091a071d0d03051c0e010b01021203010b04030807240209010e180a240e04030206070c0503030c090d0b0f04 70
    0x5801c03941c00c040b003170000142c07960b04c0b00b02d407001c1601030103521030509040640c15485061611249503100160004c3c0752000580945100040191a00c100041c904030080720296000031000307198015400c46412498994005200159421000546200107070340d0364048914030210100500d00510410840e03507407084031080090340000d1020104071020000c10f00013258440700405004001c0341c0c01c840d03c00c039401030810803140d0f014140248544034400074020031500340d031180180545004101182c000604490486810600c2c7c986400c4c83c6d5160390356507800c505021541c0520310700c40000348110b800303200d48081051680c0140d1350b003824000546081c07055031a15003d0448105501c0b080781c518102c05501520008010800c942080365203800d064400e9611548410b514201080e007075088248103100307620903000c8402c207849da000c00741c400c105180c1004119520420000e10600034520240041c003102424410104c0c105030b80381c80e011002268416074110303000c070811050041600403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 837517571 1250 837516321 837516401
    0x7121112090d020c271f060516060b030705101d0d050d080621010524030d051c050c0d0f0e030414031504150605041103150a09 56
    0x10408402c0441029485051201c140c5200385075880402c24801c1c04105c00101c4e068100705d082d242c91400590004816801101005545c9080f030380108045000d07900f1151100c1c0e204121460440c00d40d80d43c400039050081c6215014010001c00003410348400d804400e403038070180c650f0b2101d0007100003144041201004910b1003014000d209501050300840c0c03110325111140b40500b0240e8a0801041080e414000202c0f600202302002010614040d4051406003002d00700e0186194840b403d128042c181c88041c0a0341600000000c0e038400d4081c038020401c0c01c0c4000e13801441c1825503c5004201c03803080f0791030151310310006603480710b44082d03104802c1e010610040c1000504264011703161360f40181e014120107009500c040510300da80401400c8442e0b0b404030800101c5207401d20b440903082904915880140d030800001044a203014003400e90300f461041c01081c00c1d540d4800308040c2000080c5a803580120080e2408101990b80307010b0343c0062a4081030070001280b00060710702d80c43c1c1c00242 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 837518821 1250 837517571 837517573
    0x1b061807050604050f0a0e0a02070201020f071a130e010f05030c011d130b15040f080319081807030521031306020f0c010c020d090e09150712111209 65
    0x244280c0ea02c14080d9010303103800b9140c040b803214501c000b169031a1000e80141c0d1180c00a00304003d5840e0541c1c004003001c0c1e200381d0a41e0300301084200120394030320103800340d5000f00b081c0400170329040c4076140140003008007003401b103541d2980d51036003900b00d4142a040a40aa04d4916080c842800c0c10404144c0c0c400080c030384071820076072603105000807825800f441803280d030300d1003030f10103c0d0015604080c0f204500100740b086010120404014245c2c0244140d42c143d644031000002d000002205580d5146108051b941c85600240d0040f1181c440090103c8072100c1d0108000740710601c20403c0c5006144601c008100b1840004006910004510903034420a91f080080040003e03181841c410140d07071003030b03015031a4010004580e00c580914440511258644a0b1002c04035900141e15000e1412a445a205113a140c4200307081c0d80070215641c0c8a04d0740700c0104941c034012140c175102e40c0041079140030b903969450100140b05030344452050440c450070101c2c104051034590480f180d0040030002c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 837520071 1250 837518821 837518833
    0x406080f0a020105090a08060c19050406050d0b150a0201090309270209061c020304021e0904110f120303090d02030403170a090509011203021b0f0d081b0618 69
    0x10486a0354041d510000b81048400b09460490f5269182d00301c002e4074611381504e00b030f40b501d082c208032150001d0142e044012203800040b440503025501b150b0588000e95951460a81a10600c502070300000b010b5640000741c000842c0e0401683e040a44908440d6500205032000700342001081d5001c0b54100c605909040400309440c0d4034040d5280b12201030f03042d8003503152507550b80040d20a0003020600c0c1d0012541d06040c10120045a0055101b10303c00c54012282c0395a049140200c1e203080070308140c1007041d0300049800f160112030410079880c1c1c01804803e0543ca4100407810700500c51611a00c25400030081c0324030b00505109203150645248021401d00c4d1075a10f80f01190700074940000d000300b100080d1060310034070400341c42d4068280034100c00b000c0c2d6550020350441c01d052000c1540140a9171540701c4c6807030100080d07442107100c010320404100e5080c1007000309035040104215120442000030000140e4a0f00a00000703005880181c940741c6002000080340c40b40d000a82003040d0042 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 837521321 1250 837520071 837520093
    0xb03270a0c091b1809060312020d050414060d0608011803031406280b040e1501090b0d1d06070207033c030c060603120e0609181015020c040608 63
    0x5402240c12070f100d2410302090798000309042c4860880360022035580b42803c1000c0148220000d007681e182c00c0c55421074040e4503505e07204550314003a60240b10291210501c00d0180c91801030050b08616000510000380e0307a54540c85282103e58845019040301d01040301c800038160580305801c110350031000000002c0c540301000811940c218907c0200e4464244885141c6100700c085c6400a440520740040d0b82d03031703101c070801000c002040f6050803808204500200082d403142414900729054865010300f42428414a0b9000e050080301103e503414030401e0b02038043ea41088003600565558010300b0740d81d42035040c0200c403042e10740c001d001503e00d9480000304401c400280ca40c0c4d2001101c02020b40e500702c918048034480e200980140c8080d09109011003070201200c01d0381c3c40381c005602c40744040d050400a00042d409603800f11580b000700c40303801c0c1420501c05100568451410b1041da620b0989911b807091040940d0003a950069101e200100c01c0745c28188128405451180c002b840d42c2011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 837522571 1250 837521321 837521351
    0x15080d0302040e0c071e0c140303070f060c2102130608070c0f0807050a11040b0a1a1b06070306050118030b181212060f0405100b03270a0c09 62
    0x10300110207034213000032030b5414040300c917010240c00f0559a18001301c0c60000d040c10503544a4902548a01c440c007609075240c030b0324000080701c04c0c096001076030420200254440400a1001032480c0003805050301104601c4510034081e0041d9110000e00113031036580000d156404030104e900141c080c05510024400260f401c46000c0daaa598800c00300d44d000034003460710500502660400620724801c600c0850204000c207000d0016420701035508000d5041c0303010030008000703d2403040744c40b030310112051130107843c11a10082c41048569821010100f24240d0340c07500e0314800311010300020744c0d1420144425030b804a0840d8491401c0b1024140311780c21501c0c1d12030091320103004a0103070b003140c2c0440084c485040c001c05503041c1c840030300a500d0b0308048145020201e41103540070311a030001032203a800d51426200d103d02841a443c0341d80ca00600b01080040c0c1d0303610142404c00d04c151a0184400343c454844500c3d00e4101c0828080c2a240c1a2441e0a2940c0500d84d00041c8410303040003044154861 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 837523821 1250 837522571 837522599
    0xc1406030a050702120d1d03090a3f17070809010f0e06030a15080a0c120503090405010932070318230d0201050112141015080d030204 59
    0x94600c4000641ea00c40f104181c0c81c00907800c1e60100740d0f1001203110f000d103943d2a031010548410040c1003001000c26a8480f07901c0e48980006a41d010340a588140010300d20700980c0c902003003203d408910322003660602451100d1001301200c0b001209004480204810352111400340d12135140c2281c1050110340d40d03001c5a00501780c00504000105c42d900d40c401c4e200c0d0a408404250140c0311903540c0c2085004000540124000c08005040740000043c42e4100003e180c44403c0d0001507200341241050020461621290001c0d1468401031150740881c2d80d032807042d00d00911440030001f604ea08a80d11600d6000031610b410b406104880c907840b0301d40204003d00c2c0d40d0010740d91034002110045810294031130f0013200300240c0412110701c030442401c01450031075640038130300d40111703041c0111001c07080342620703000d005180803012443c1d41c480000d46a26240320084080d84259012078040300040001c03282c68060500c1c401010798000c01c1401c9051100340d9a5141d02e1406600e410304101000064503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 837525071 1250 837523821 837523831
    0xf0807051606091506060207050d0b18100c02030301050a05030f100507090b070c1d13030c02180709030c050a03020609090414151f05180c250c140603 66
    0xc40d00c000c24200b000525072042440a40c40464100380e0560001500d000f04810700400c3d0140c40303444000310b524505084000d50711540007400000d90f54910748403002007400400484d61921564140301c0d12403095000700249030b00103500454481d8541010007500341e181c0e80c84203000e41c10039140e041ca070000204030110a00000e05002c14180c9610f601200d40320f09036800100340007070205240c0308100e01842990211103001c100200c10203820040c042e4502c00c1620300e41d0380280f05150070000613005519400c102c42c00200f1150511900c40b1104141400c00c65508000a000b88001e0040100d401080c0c009420103499828000e4110703804100c4904c14225007611403001e030780001d001c01c03201d055031541030032140003038850180d111502107840d1304040c1ca1521000c03080d650103600c01d445244056003282c50040640010300030180c0c60b01d4071054098502e0518610404c510001452034810920104404451200011110341416048074003160401c1160000c0f641c0c039641c25a50746010380e6082 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 837526321 1250 837525071 837525097
    0x1501032102030c010606052110062709050f0109060b0d020c1e0303040b0f0412081302090108030c1e0c010f02010b090f011508042312190f080705 64
    0x2a034068401079146004004030042c0d55800c1c18030104440b544000504080500503801c01500390101e01164241d2400f1654500180d140c1c0004029403840780c02c151340b03050202c542c0e0404889440c84480101c00540c6c00600909840d44180f16074030042181140c0141010001004401c0c00c0c0312031990b440c4140d0964581894001c03528a803030f840c0c00c0c040703003c58400c2014004201400d180702251690003c0b42e0070f60f0580351a200003004051a025034601c11544180070350001d410036031080d122800082d11501c01100740c02252401a2101d09080b0b000c3c001d00d0004544448008006e14545420780200e1200c0000e40320001a03086c0d40020031861070748003400c0400c80d00360200c1d03040340184002c2c105254810415800e2000409280c405941038407001d01e410545d1040a031000d40e807110068500401c81d002880c1d4100313030030001c0c0042c0c044c03111403c01501c0c0740a40d94809a11140c00202000a00000d0031031140b0359150480302c11906e03d1540e04100781c140c0b5003164090a2801a8500c2603c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 837527571 1250 837526321 837526373
    0x90105150408060a060810140106030f0209030a210e1008130b0c030109110c1002180301140f060108010f05040c1e09080f01110403020418080a020a0302150103 70
    0x1151088041d0340240108604030381c50707480c000c00f00318007500341449003c215000b00d54100580c86418014003051009949024145910f048002c400030030042e0440c51a4980c02c0c0080e420300e61301800350341141c5000301da040c00840701944481c03d8042c600ba0380982402142c40920707000e80c0380e07040014032180341d90402c00025600c6038081070b2880080071004011490b00c90400800c04da01c5006181620704022003000a000c0c1032049031030034030810201600b41d50298040c0c0c2541d01580d001020a100c100254041c001c064101080c01c0d1141482c04500142c001381c1005a190366080350158005801d280c400d210703506d84007d5001180300c40c041c007806252220129100d503405066145620304c80b42004007d900c203500703801400450980141c10b2180608145004a0305050080f02e07080300c4103447c06803400386182e007048001c21070306862680525500f501c02c00410348030700240c000304180c0d4015001032801031800904016641e487c045241c50070100520214100d00ca1203021103e1003206018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 837528821 1250 837527571 837527599
    0x30f11090306220f05062a03150a08030711040f09020112020307020102071a06010305010b1c1802041103250806040b040608030a090306051302100f0c0f080403051902090105 76
    0x43e250215080242405608001100800000280c80c0b4421901d01c044200d40306e1020002405c640020903142101c2c0d0410b001043e54044008079036640d40b031000f025800304a6030b44103080c0c2190010081500c0346174003a5501d407014100f5000c0c0f850404002d410800820b1410341c000380000c070f000c680c4c44145c15804170000701e04900035412564081d42041c0004112040360b40710500e1802c04a5135140001e080c5800041d15000560035a0310340408001185600d00c0b0300040318008022104601828880c455030180140e2541c2c8247d6001c10221702c0d00a170340340b9228102d0b011089002405584004409000d221031f654003854540e00000200c60100d012070b211000580507003950707003000000740000030346841c0c2141c21019210880e4400c3c1c03400c0c81583e03951508810b40b0058000301035049a03042410000c058801c0c806181e07a840581099083d403601d9864140e00c801c19104100e03404c240006050080c02800c000c4914200840318410701290119808100680410710585015001a0104036 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 837530071 1250 837528821 837528871
    0x512070e03030706050603190506150303130b09011706090c2107030209010306120f0201110f0d09052803060c0306031406011505041d071e030f11090306 67
    0x3503609040141100d80381c40c22030402400400c4195004c038880c2c41103030410007015500713a503900c1c0c00070380210260486a49490f0008100c91483c00d5096243c0020490a460246040e0744403003d8458581410f80f0f4a06510000d441d64104410415034000180204a159503490755401d911007142d158541c0c4514986081c84003030f451043d4031410303e01c0705004000c0d816070b1590242098513005d82c1c040c03044a507102c945401c6040381c804c000c3d1440c001c0015013009540a02ca02084d10744000080740c29840300d443d501818020701101290000302001000c02241c0351148000c008280204105840304400940140c51510144001001e040d15000b20004a500039440800210780100f0003a0001014050380783d201c2000740038030b002842c4540030591040344158283c03025580d5801c0520b85c40100e2680714040e00da4010b0003c1c0800c03080252040302030000f0390000100401944000c90201c0130811701c9030548095000104149105000c1c1c919541d400294194010400092111030303001703803100071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 837531321 1250 837530071 837530087
    0x220c030204020c1015030206030606070f02030a0507030b160f120e0706032a1b2d0c090b010c03082703130b030403120b010c02030708030405041b051207 67
    0x81e510510201c1d0b0080b02e01c0c4081480341810b4908001004440340d08141c041d01180d0a01002c1d4000c103090000585d2420618000c04006000303110740340c10b000d00d039400645008090b41c0120740701d4100342001c20400c102403c55175086188001c403008400180c0e0401030030801018403180400c00d0071041410929680d5001503968401c10042e2540b164a6050181c0a44041c500c041c070701000c0480007a0558651072100b0098038055600c55011101c0f103107241a0707550600409590302d01140e000740b180c421054803814407001d80b42c404070340c0c3d000d00303418500740040703c40e0f1000000344d08205070200c0b56030f8410001d120b0503902d82400710441c0c4070001121500080c1d0b4036403016124445491440c202800005028803031681d000d5101e41c56121001d44070a03000076500100070a076410364003c198411a040301514000c1854441d0410f54550000f03440c04180d82d000c44256003000034248030700c0c2454050072100880a091807008144e0940005000340308030310112500d83c442101258045201d0410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 837532571 1250 837531321 837531323
    0x506011e23090315010f0e040515070e03061302060306060d06051009150201062907021801090b010915050a120905030405040b090405120d0e03040e04050601060503220c03 75
    0x140716810004100403103039560200d50118424455850301011080802000078140c4010043e20350010303103085040c0b4844030016204451364000e038684828402404d144843c420459503070b03842080588402407606014028140021001102d48100096201c8c1c02c00c4030340000c0d091b242d43e0750790f403010601c0900800170354001d607621010a0082580320340d80020001e00380c50102041c0c0f146490790300016400c844a030b00c500740b0000f0146070801480e003012011100b0512400d09418500300140e40001d02c817000358120003040a00c02401801500018420305c0341d068030a007490b0040a0400341260400d0020710400da080140020303e0002141c810318004442d0245910300b44800305141c5055604c80d04140500340c00303186032202441c10380c41d00b51812030080b038001001e00092042e11221741d02c2c0f80d00240c141105243c861519110748201040140028a5100ba090b41c1c24200782c42c0003810118103a014408100b410b00622079607400e40112140451001020307030b00261043e00c2d00341386449080e40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 837533821 1250 837532571 837532607
    0x10e040209040608060402040608210a03020729060315310b0a0c0f0f080606090d060f05091c08071205010905090c100c02060904020d0e0715030506011e 67
    0xc07001501d04400135585c2d0140b44226400d0241176192000306a0b5007a02d086d9402c802d0840c0712204a16103030b9140104a0301e445450094941007454403190459180d20f58001040e4491594242d09024100c4410340c2100c0c3c00c4000d0000b880100c0796181c0c1000e400341c800751080f003507844140c0c1e81c038080208880741c0007003c42803401031001c0d0f800c1055080c0021a90009450b050040c000070300c84c0f05018a4500c82240e0326145802a840f50044400f24002072140750800c0041042e807509549020041d2040c078407900021901134407121880301a100068540d1a80b540110030304406210800e61044000090b8034084a5558507045d007161108000002c003050246414004601307032201d03130400e51080c0020011103c81d540c00388144145103803503045440000d0002e120f8200185860700c0203244944000b400582030840701d14400040b01c1d0040020001c0d43d200e81400c103c80307030148038400e003444a0340c01c0421252512030000ba2102080c01c984508181c071070f910100703565008900c0700502c002000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 837535071 1250 837533821 837533831
    0x11e0b03060d4701090903171009050a020702010e24071106030a0c080f070504170c03030d0e060f190b060c1510050307080d0f050c0f010b12030306030c010e04020904 73
    0x40c0b0300c040209884001903c01c000b40100200d0401e44600490311070a626070b445801e40a0500201e01000d00050b040c01d904070701840002132103c000c3c1c0907443c01035202081c010380d030345018130000d00781103038016896010b5000e00300b5507001c000f055040044000c0445240c00da4030055032400b042c040303000106080e4040b001005100703070818554014540194152140765098550407040203c3c0c100403510078000840401042c46a03070301c2e01554000054280d8129481c0ca0310000000b4215004004103440141d5145820580b000302080055003000081c04c0750724203403e080b201c070481002840041c26940781c5035600c80c01e20b529020100d0381d041c2000001d40e000303040342c1003c0c82c0740303800305440003015212414000b0a1501e8041014001c44086200030848bd02c100c1ca41540e0301040c074045a000d2100501131018810b0040c0719a50b5800300c00c2000040c032040c04e908001d50041c9041c40e502e1310341d0051081018a440014480c20000300900b481c210007054900050043e10560003000d8100b4104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 837536321 1250 837535071 837535163
    0x260102031009050a02090906061b070905250f0806013605030f070909031b0309091514130608010204080715020604030c0f030c0b011e0b03060d 63
    0x22a209000350740d40c00c40c040c403840d201c000504050f4041c000c0c1b0700764014100300c04903130541303001c00013840c008406050b0000110380602c12107081a41a510024406032240204900b8441c1c000618040c0d074000c1c8a1054600f9141000074103814044900205203c1000301240d41680074080b1010f1040120003100e80300102e210308103903a000d0b58110f14110801000e408241c0f881c011900796032201940004180d403918100500e0003030b180c100c8003a028406e02455201905c840c040e011030000b4002d481c0c0340640c500d008038ae071080701d501000001c000c01c8803c0d8240000d000c25070074050124000c8480310f5a00080034020801405203500140c00d5610014001a84000c00b0600340c040f25078903510345282c6104441d06989540085400800088908907424000742c0c0058041203040d009151a18241e03200d030307582c018500d20a8005541c12464420300d61841201801e00e080605a280d420321309500f003581c00b1400c3c410500b640203040c0010201c080b5100d0811099506e8900c51414080050316a9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 837537571 1250 837536321 837536341
    0xc0d0503190206130b0406020706020714071202010903081308010c120506061206090705070537201f09061206060903060c02421026010203 61
    0x11020351141d1480d410300c503800550010410a10a41480c034802c80c1c9080d2030341d1a030b44081e800030700c11503096a0911085000ca0380e03d1001d01080c9215140320410701e4005000c06180040580c03100b4084e03070155904c1070041c0d0740400c0c030341c04881d400614103460310003000c0342820504158000e030030b45610b41034a40c2d0407242c0c004491181a440b00001300040d031544ac050080c188140c038074241c030241481010805504040414540c403244074074000d030030004560786003410700504044404205c943d400d458007543c100c00320091505004000300303151030440740c0e95502c291043d00045460081d2100440110b0f629203249880b0320103c8241a8880c05604401c040d200703003102d02821001511440b6000c0303040c0094800c00c0c1c1900c0180c1c490008043c55990b0720801b5000c4d6601a42c114020710300004245e414074142c00000c1880064032210305840c0105255031255034607140f01d0f480f089541800801c400d10041c62041e9419154240201c006110704243d0482d154880c0c00050340c0b00008000c12221 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 837538821 1250 837537571 837537577
    0xc09021c270506160302090a0302010c020a0e09030a110a230705091602060106020a0506010306110c06100302041116260301060309170c0327180906010909030c060207050c0d0503 78
    0x2080301d81003a54031403024088040f40580c842042d0000c06445d009d20240d0300840c65210032920040005d07102c50b80320310280460820590740120b01d50301c0820b0214420382c1180240c605000c1c44d00007400d800c01d1984440d64044501180e1343c1d19043d028840e040f4041c02440303450007401c030141c050001c4c1d0502150700503004040540e41401809600004141c0034030101d01c119840f90000d0080c215030b421500ca20303005250032080149154010408050340350424010284285041101c0c10802403540c0103003c20b0720051401c54080b40300070060141c45500903c825140e281d0810310025950806c203c03c40c0c62804c4119900000131000b0000064041c0e254002407816445aa001e014400707104010f80594011800880d51540003400290128540001000b4000c0d0080c940e1b60142d00700303103003c905a0040500c800742401c1c000b200304506518108400c07401000da400d0b04020703c000a490081c82c103000d00b40010101a0000740c03004c180501003000c0f050b5190002c02d64403441301103140107540d0f54 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 837540071 1250 837538821 837538831
    0x1030c0c08071202102415021b010c120314010906050a030f080904051006091d07050c12030c0a030e030f031b070204110702032a060a17040f0c09021c270506 69
    0x300e060b0700824420703000c0c0b2a0b01f8101405070000c22120300680e034203c040b042c006404904105080706480041008601c6000e240d03000c5e901e000640d031610004034070800c24141c00100c003a03414504104683c0e200e8681c4402240e40081d850111803055190900320b920519407846d41c03260410301409032050490340944103d50380e07900d038064415a0313480810b9055200d07101c0b00c110882c04000241009000310010b201c00207004050300c001c223550241141a81d00161907150421101003000c0715119050320540c040007142d40011810803946612450312440028081c032840301c42ca0002c610343c0074655003981c4480b540188140001d5404021522035604030b003400341d03c04e1250110007040210800c20b03011140c2a07003000d04c942002d601003070051075031090303244204120088158034144221030044601071841900c1061a2442a0410b0000258942c01102d0510700c1082000c844030100d81c111205414200d4001c1408246214051213465081001d869407005821241d020400c1c0850100d20036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 837541321 1250 837540071 837540131
    0x2030c13090903020a060507050c06070f020f210a0c050f10050c070209040201141309060816060207030f020a12030e03160605040e09070b0f0901030c0c0807120210 72
    0x41e55600120040e9100c00c08040c1c00341e0400000300b0040f8440b03800580d800102c41c100700f03207041c400808462901400302c8114001a81c00c1098095555041c0301184c00180210000e0840040d1545e000e45000607400076019003203800a6490700050241800210103a008810b0700c990041940d0015110380e100404a140c0a2070a400690b0340d034010016955016000b8140103500c0d86d60354010f54020f054041c95a00320b01040c003054040f44004600b040241201c40000702e501c628261681e0314100c0c10341c02840e0304d83c1c41c0c0030782804142d0b8001144000c40741c108668403a444681e0020500360010364025500c4c0ca407486041405050f08021101d83c034090a42c2120001c5a2803001c21400707504034010500084e4080000b080300c026007900d03503034202000b83e054402d21584d80d200c0c0b8505602014650143c0d50020403950310941e00352142d65640f14050911448648860307603456a140700f03100005087d1900036801c0c101c482c0c82000840c1c0c1c1011084000c0042d14900c507440071611502082201007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 837542571 1250 837541321 837541357
    0x40308070b0c041401030b031009050c0a08070e0703110d020a03050708061f12020c160f060306150c0c030501020d09140f0303040f051606030509010c03090c0506090103060902030c 79
    0x2580d0b038840100c1d4101d82100100074030951101004402500110401d240d1610681819180c40c501601ca598032072485000141268110081840181c0c04a0351000741d030380d000702000b0000c0d49106400c0355405441d070f00d000200b00503103074407144050045803096544180b0100d40303a0066034050380224050715060b1506800c80d82c2c0d003410002541691b100f40600983c0c0f01d00c12110003401030b0074070072846041072005414104140c500b0751410108012802c0c0c404a950b00c01c21503920b100101c03a0140515190038003040d410001031688440c810b0b02c0e4601007000040c402400d000800402401459101d4025555815001c240c1030140202040584141d0f03030b5046991450800010f80920240c8a400610f085903510340380d0307036003d4948110582d40c43c0250640c80300620000b1b000c40021f442c041c0c03400901c5050081060382100c0c1c07115801c0091502d00440c400100c1e54100c820412140101c0300b1554910070600100c000e42401c1c1c0c08005007a0011090054480840d030140503a504030941c0303410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 837543821 1250 837542571 837542581
    0xc03030906021b150a170a0b18040203070501143a021204170d060303021f0c020c060a030b03010e0a050105090307170a03021204050c0a15200106030503040308070b 72
    0x14914a00e514202ea015905203c26900380300200c014000d06007450402000b806d881c15400041c5000444403105501d980d42078091044c07900700101002284026510b285a00d13060340400d603250714900a180c18400710b80c040d8403048480400b220611507030303401700c135080c0d001d24010b02c0c0c43c207680305802d4441d000c415124050140e085200b0381d00612014103000d031003503c40b81c680d82c101160114019291810811418801c1801c82c01414002c51285d030080c080d00079010219043c034040c8058400e2641d0601072117091050740003a20b11048142140d20540d14641404207800804d000e2607095015400c010000c84c401c40007240002003240100f009206030354400c45400d40340e1040740001000f002041c1c1da02c142d1072940c0d0024020039103850400500d0024030780ac1010590f80200d508440c158031801c860074560500d041c07180024205140010300100b003410700984186540303130050301c0003400b410801078803031000d410040080d5000b00c141da644039100e04245200354804a825076000f610b12011070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 837545071 1250 837543821 837543853
    0x4061b230d0c03050d2a08010603060b030c0901030c03020d09050717061611101d150705090607020d080a02030304140303040807020409020a03020a1d0a0203040506010509090304030c0303090602 85
    0xb90b42a94190b4551380313007000400194004003a80314680304501d0312140c001d0b08044802d410189100d03031644569032650300d4580300900f603d1058000c00b404000c10302c14030142468800696040d5102401c0108001100701c008400078042c0407180c6d8142814494408148407011601070141c9a46684e408800404c0440165940409407202d2000e071503150311130090300348109160300402c80110700f03403426107107600c2449059581094545400303640e0801c0e03002c074401c0c08020a01c030307101d40340241c1c00c280d151010001e4030703d0140d02c9626010710000940e160455459030700408825900044290303c2e17440e41d881c000c0d42c80e00112011a107118280d03200003003018000069a01c503aa002c00440e207840041da00b8000034281c15901241c0003502d0400100041c0d0300c40142d440945005c050440c00715600050101d440c0b400131306013032400e038410024440030074400704505040d548283e600300e59070740398189036a2540c400e9510241c41200543d00202c00c040d0320235001d8046030411b900702c8240c00e1010a41d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 837546321 1250 837545071 837545087
    0x11041b0e01020f280f06050709060e0a140d08090901080604120c02030606060d1b03020c010614180603071203080414150103140a15092604061b230d 65
    0x114240c4030103420142c144e000e083c411040c00b5031003641480c014085564601c001d0350410b8403014049104003e080c4006e41c4d01c00580032036010201c44108105e464561000040141501c1e0103000d0680c640c1c0840c24004801e00b00c2c1c03c002c0014140744001d42e5288a0140c03120016982110b0300080090100d00140c0318402c83d01e031a640007400b401c0703aa15414104a125408004000226034542c00b0417050702e42280a100303d41881a1000350380e42c1c800003121400c49091b80c200c0c2003801038000058446485401c8594105022a40d00074499100c0c20300182ca411890351020f007154043e003060030101603022036402c2c044c0c3e201d0b007201006003681d40c110039207804e9504541c02d00b0f210040700400101c0d615481c0400002080f00549001b0045501c1e541c802d01c40c0d100c5c1c914802c070748403003000e002c002aa014a80008070354466400d6240b41080100300d49111f0380c4946001c0003854058101c001080c61004010305500c030f0100711500d120f2021180465003c00b44100b0b503800307907401c543c1819000c0c0c5a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 837547571 1250 837546321 837546343
    0x30108071413140f180303010306180b0406060302030601170d031a030a0f110103150e06040b0918150c04120c0806010b12010501030b090411041b0e01020f 68
    0x1038105103081404205060705405072040e4411144040c1a0306041c8510888040ca01c2a19020040c2d2416480441d044900545242400c5800c040030411a500103c2921b0640703600c0704000c00c82d04900012450400c561503405414851000140400c122980c0d120008603803080d4140c8204c1d03039951900e2441002c000020440c160000400d40030464402d52040307655829415403844d810080340c0103c4d180c10342400b42280c42500443d840c0e014045500c04c403040f030300b409107800e10080e80e00001c04041e004175445020828070401c03000c81c0f00c1d5592034000f4010b000c00905030365494504910524070580100f003000311039010b12000e0010a0000c0c2c00d803540300d247c0008100e0700c2c01c0e14015000340d00c0d54030594203079500740c00f800004c14000c0080c40681e000306802c0d45441c2d00c842101190030000750040e480741c0d062515008020366142c5441507034a600c6a00140700740c90b125000c802140260007100b21400c03900456004000c801900190115154002a400c4403502518680850340d91408450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 837548821 1250 837547571 837547573
    0x609100c0509181f060c140c0d1202070e0412031b050f0c0f01180506070c031707020f0706092d030605090a0501151a0a091403030412050705090606030108 68
    0x514143c040700ba08083c550410121944611a03103200030384188080e00642140f800514284402428425001001400890200c1c090490610b0f0440011800e82c2ea144c030003000304a0030a18403400d2402840140024202080f08101526140c41c20100d007040420900c40481d2510484070410b090078092014032400320348803a80742c10410303a030170301c03182e00300300901c0300c26114017000144111001c0c0039442c81c078601015038150b00c1070186400f0b810450010400c504004000a50b50080780c0e110810208803081d0000011503510740001c22400c01c06602410328541c800c41c1c000003034495000c5106002c444104580500c6084c081a0341c1e02d0602c0c00a100d1701500c0608001400456166400181c1200350441200d921802035030b04c0c2c07403d440003900901c4030f4000b03c1108015010fa0344074007004850f003041c0789903d0700b080b503000034001c40002c2c0104c02a0300401c13601e02e0100d450070400c0300c0151014021042103288e41d86006591540680600c42c05100f521000c941c05040850a0300d050329a048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 837550071 1250 837548821 837548839
    0x40305030402120303101a07170c0f030f160f02190801150303020a060e03071b05010305010b070302030a11030c0708100f11070b250c06050c0414010c02040e0609100c0509 75
    0xe441804054287d07076003004222802c10403640041c04607408100f1189005a241d0340720640c204140b41400d0340ca80e12143d041e0420490910241019022a1083c0d00b4004003007085246a0601780c3e051320074071000039001060080c0c0d42140481280c811012621030200900c40f5689415000c1a034203001d00c80140980e00908204000851b0394022880c89000002201c0c00d001c0b003915040d10030141e9450482c3c218148480c1070015507070600450b405451590300b42440d100066038003e5592055917003200810808002e941010305041c0200d4090b0f11130f800c11294202d840d602c07020303120004554200d0090f031518110b14501d514030701400500c0100b00c070300d55080440f5902c1c0d413440014003c0081c58541950207001c0355100d25070140050074241070f0398a140c00402840d0650448101030304115100070140030401205d80b0700c8850b01d03000c00081c071341610f800c001880810080e09040180070802d0140c00b04011041c040058021a00b41111400348001441c508055845205000744240c2084000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 837551321 1250 837550071 837550079
    0xf16030f1104060f0e070201060608040605091e0309041b0917010204091a090a050c0405040f0b04050103110a0603090804170c03060403020c0a0801140105210604030503040212030310 80
    0x11039640c500c1030050030190180805000040c0480c0d074283c109814040001c030f418030485003980c5640ea03112103240002c02015080c290094482c01000340007c0921b5100c4d40042d2a600061004c002107104008100400a8004456a0700c0ba0000d02e0b21a004a292443e02c01034611903000c0800007420075200e201c0d8103400c100c1200310480200c443c08407659002c0100152003000c501c00c407220000700c0303440d1a03076048025007048100030001d0108a0800d0901051041c02c052031011542210021240003420207000c02d0114060500c03c01c0c910740c09860031000005010780c1000004034641d04990b40107030302d0f0704c0740c0007541220417580000d000c028042c00148a403040c4560a10f0300300061030100c5141004601c0000c1c6019003c460450060704400d040b1060f0b1b06082040700e0145c5031400c003d00c0791210007010144001c00520880d4030a1105800c00000085411992000d00712010155000384c038050030081c1c09644152400c80c01800f400c0a43d83c1d6100c004003e4a009111841d0304400b003902e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 837552571 1250 837551321 837551333
    0x151a0304020a0305120a09060807320715110a0e10090909060b0102060a02090d08070c0b070f031803020306070e01110129040b10120b0d140f1603 64
    0x4010022038000b2400308010012640c00c122419861134110291903032518180307002005a001d40d800070060001c0101404404c5030003440440b00000b541c03200c90f4140d8640460520044454405505400310005080090200700c0140b4900b128140c0001d01c51413100240944552144542c1c002c00600f1703185c5c000c500d07440c6c02da502420601132890101410754544054000303c40309a072080701d40542d135120807125542c05101090340074410907011420b050050b07000c00c201107268600107000c048009a800100304091490388040c0030408540c0341c440d143d500d040f8088038900760301500812601c0d1079401035902c1040346001500d602030007030000ba8445c1e060542d801e111403d140341c1800114002c1c80c44e001801d2064086c070300d500c1480c240010001200000440c2035031b8108a004509084115a0544811071008030100b52172a100500c40c6041002000605841d594580d00c110000c3c0800140060b1025860345085040c0594001013140d600f242ea903003048100045010380c0081c1e0805c0071400b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 837553821 1250 837552571 837552577
    0x150806011d07031116060e1f05101a04090f020414090411060a170a020a022e0501090515090610031805010e060103170909010306090f020306040c050301151a 69
    0x400b5003000b0500b00d00402d981043d54001290a1020103102d0300c0314020f1041d9401a48540740200b0064128555502d5031500304004e00c5e403081580307a41752800701d0740d0942c104101000910004049020080320240c4010180e80b2030300c01c1542070740c188050600811440d108840840c7e205114502e1003512030003e000e82c000c0000c000341c0751492100601c03c104e8403004001c2041c2402caa940e60030402483c0e849016500b00501030301240342c414040c4180b190340002c0c41c1c1d090106291001c64089808010300c058550a0580c5008002c0c00c0600000301c0c0c140642010340a52000c0d0701078414120090300344480f0181c115032256014492152502580e8020f0b071190650350422100c100d00844591a45030945140700d002c198980c0c45038004106000912188962008107210824508020fa01c0003442c100f10600015041655a41004d004c1007170101c0001c4641e503019082e11107500c5d040c00c0c180428440c503c40d280c0294240300c0041d040d039101000100980702c03002200103040524500b000c41c550 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 837555071 1250 837553821 837553831
    0x1050607110d06091b0b0f0d1d010e1b010f080c090d0c08030415050c070b09040e060a0e0c0d02011205060301020702060d020d0c08040305090108041b0603150806011d 73
    0x405002000d01040041c004c10280d00d005080311140d600d001d0340c100801d41c00642c0240022042030014480c1e00401b80704559010b1040c603000319880700b010314250a807101500c0050590340c61b2260700c1d0150100841c60041800d0100e0784074044a0f0114019201c400214580000007030440e03000400c801c2c000e10140c245002d014040700310031541c5a81e014904a816044000390307a002080c100200c5150340e182a0380c0002c00d141160070248007943d055903a6540340166107007a035002c1044c894507180c66000001f040c060400b159082d003441c038102001041c10b00008000d500503031210850314107007104034420007941a541e00509141c805400c4000f0a4040c028680c155020084040503a848002808038491500c0740169208020150a02112034440710107090240c60401c200101ea040b905455a045080c00d00c0c520070b035500d10b0070b80c2551062418040442c6544d46020488a0b49a4820340d00d01150200542c20303184c4079400c481e40e401e4248292001007010060f00d88900086045458000f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 837556321 1250 837555071 837555079
    0x12050313060e0106120c03050c040605060d09021c14070503010203070f0e0a050303032d041e03020a020a0605040504271202030f1c0c08061f18060203031e0105060711 73
    0x1c0340c541c11400e168040e45e00c0705030b030391801515062080c08030030b00c8008140c9804890411035240342401107001c80c05203040300d4007041e6890441c1001d6440f144182800d001c5461242c00c900080c0740780442c040c10b5055004091445202800b107203500701482124002e14294070740d10f088914094045800400103440d0a4000c007030503000082c0354804001031800360b00e074040307101e0304e04905100d43c1011001c490459100c9450410521000c991055241116001850f003034003c1c02429080503440d06044440c001d40008190100050090307000010b88140c490840f01130054002c0303a50f088010301e0180c4804000718440c0c119517400600c1c4c450910141c6c40ca00e0040e20306180c48489910416003101c01e616140d8101c2401d01145080c0381e102d244604802800c0804890400d000410b00e041388a40086c0c4030b05604861402c01e09024449021040e180c21180c4140c00b902c6401c001e440c0d4009407101c610b41e40303903404078400c1242214900b5041c0c034800780c60141003c0291700d5807182030181140c01071b04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 837557571 1250 837556321 837556331
    0x6160e0f0a031704050319210c050706030e010b030102090f1014190f210f060e0103120f020601031106030a02040e04110a0501030b011202090f18010312050313060e01 73
    0x450701c000048800c1502c1d03030f90701d4460b460b2605050034090780d0200c19403843c80700540c410000350201142035006003003600d83e50075030080c4002981d9107200520040e21f5032040071000988264181c0011a008200314000d0180d50300d07400615081c6d001e00c0360907580c01100c0f007011211909000d10350180e5002245044c040c00005080d050350150f00c007611801901c400150a4101c040d0080284c003103d1905d46040c10510f40b400950001035140100741c011001d8446030392100e4410190402006800090b89403261940d41340307482540b415156030743c0340104000d0848140640d002194440c1242d40140c460502d2207001000c1048540c0022301e9000002e50900c0302140c00b951814020b440b661288600d04501268501088090a0b00d80d1203941018200a818203669034070803001003280b84c07140740245c0c0301c4540c000000d01d084181482c081e0068040d100310b02c280201b02803494100c030b008000c5281400c807011002c42d0b0600c01200c56401c090808030100001608903881840c40c40c012000000c0c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 837558821 1250 837557571 837557573
    0x204110403021c062306013506031e011e1803030b0d0605011d09060106300207210c111002120a05070c0503190311030915070506160e0f0a03 62
    0x100c070351049102d141d440031740200001c42d6049031840071340d5800c4200d85150020140360351110a55030707d03c108984016840411101e4404100440444032151384181c0404050441c41b4002d040f60340c46030b82c25107008841240c485800b4407903406d455080380b00c0c0c0f12016490b610207070b0203012035082240c1c0180700340440070049001c2d4441c5038041c25800e40210022a1110780075000c4a8000d0b0500c0036541003a8010041d0746c0d0020740500f0703a5002d849404600302512503804818407c06d40700320307500d14000540e07141080702140d0709001d42900240f17402a04440305c2011a6240b422400007070036241405030a201c14508202c5c480c40031542441107078514000d20703e11400d01d0704940d60f95004101c010541c00304000c0001d400b00d0240c101680280540800c0b21080d2101031210400602030200d0021191030083c4184115007245a019007074442c0c3d11210740048980d50b02901081d5528051580429002c0c48141c941ca00015001d40d10b440382d181020701007009290110b10701d254406903000e0008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 837560071 1250 837558821 837558851
    0x30b0c160615060806010806010e0d03020a05010f021b010204030503040e13170d0b0301150909050f030c07141801030b1513050f0708070212090103020c16030204110403021c06 77
    0x405030303071452901c06801d03d10f8408007900300e050242505041c400c41104011040e41e008011054900c0211020b040d88819401d00340d00304144440042e001c1d5003088000b040c0d84c0000c0d0002c02084414044401c02e082000c03848a00b03d025500004107150010030040100c07040020400781c0090050801c1e04200b486941c801c04c0803190227a105013040004034190180260500c0782c0b8008071401e0b0004c1c420402d044464002c004c002d80560744070541d842c901901031107010412402081000412030750317144054200140c0e43c01c690307c100c21079509020300300c43c91070600642c01092105180e0814005900359a5945209000140f511070700b4040c402020210b40c3e04c07580d0440100c14122400039407800e00341030700c03106590018031002c00d11007580e080c0031000b50b0004200801d5122450442d071102011030049000c7d110341c0340d2209051240740440041500702140d20344c21079100326410020030034012002e08982c0191300c00a03500c85520302959080161041c00005082c1c4100d0b40001d90194130613042c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 837561321 1250 837560071 837560081
    0x3061003140405060f0105040209030a0611070506040b01231c02150d05150a030f0807060603080301090c02010c031a010518120d03060501030902280b1819030b0c1606 73
    0x283c801c0e0b405802030000c10140099103502606003642c00390303e0a280c14020a55031046000001e0809544042008490318600c09032600701c0d0344075056038043d0809013032801903580c0a00039a840e4440c080c0040003007090300c1b0141450f07004042e01c180300c030350424600b580c0c103008803480c260b0300100e24540080f0b400c104800248800010461300284a04010b00c040240605c60710f0000d000d540101401c0c0302140310030080c11311065020b105c0390790340e100c180b401c00c019201a40c0010700140d00400040380d00d4440e504121015481ca40c0200207000070100118140d41d1502416500a004a04501030951140c0e004141504058000f07103502000320380801c0d0345900c0c881c108441c0d6001080b45800789030341406210700400091a05000082c500c0c0c000940d8804601072480301d40c14842c1041501004451114008140c100619625a400103101841c001c42c2d22100302d1083d50000c001d0003000d2403c00d220401d0326080b48180031699284070110700e140c0c2c441542100c0d140c054844160005a2502071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 837562571 1250 837561321 837561323
    0x37030c320408070f050d02012309060a12051501091214070f0e09030a0912050a150b0102010c0c0f030806030a0c060e090a180b07050d091a0f0408030610031404 70
    0x105200b0303140c0164050301305140e800c900d1242101c1e103d0200941c0c1c1c0080e264402d650118414055002c0e41c801c0d00d0071910502c4d114a80003000444d503414035a070013807180600c03c8200c8505101541d00c03580000c42c04040710004901180384a1001e20045e20348000d00f40c1d546100d41d038141c54000d10004200e2904149a211400c058010314061015081a540443d048240f60b0020f500701031007000b0260011109005903400500321311700d00b1050020400141c100d0a800c105400200d0030031124501c09440310610050140d82006034002220f84a07504035003c580c1c000fa81307501600c4282e1b50444840c8805003282da0b0611800480402080d89048e14100030303d826101c2c048500e0301a0140044680000c100715250303403402c5080000e503842072420f000d11a602080d00c5a480d0344a02080d15540104004d180c8121b15291101c030400180e904585e0039600345541180075907448a00c1145038400403540103040c03035070a101086290801210720f01580180e8100401c01000491040540e200c045030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 837563821 1250 837562571 837562573
    0x1f02040504090f140d020703201017180309040c02120316091205031c0f020414090a020f070b100509091506030c180c37030c320408 58
    0x1940204200d04400c0380c025140c4e400500ba100e808070501940381d01541c03001402c440d040f481c61000b40b40e02c90008000503440140b840d44412030782c0c0c00c000c0502d070401004240032a480d8001c90043c1c480403500055040300c1d20000c41c6852441014000030307080795207500055109415031064404900b20180d841540c100b002d42d1500c0781040700c0201481c1859012030024003044071558040784000c0201c80072040c40c07100850b039202d00303c0103810003016410000000b45101080220b11000641d001d049005000c59092a0340e40b9104054012482110300c0582c11000c104401c85c00581072515841d440490040b5840c2501c3c1d5a03008a40c004a0445641809410140c01d2610f0141550381d0643c00c12803d4009040f14251207010030a40415101e5000c1861824000a80c00c4c02003001181c1c0901201c0a240d1030b25002d903031420b40d1411400042c00d070b001d001c0e0313800003521a2003031043c140f4043c10743d558203c50341d07440c2d6200d80a006020b50a8a6819000010034045002c150000c00082c11564 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 837565071 1250 837563821 837563843
    0xc030c0604030e0f0108070f02070e0a0e060c0a051603030615050a031401080303010b13050d11090106080f06090604020d05010f15020303010b0d021b0d021006090e1f0204050409 78
    0x8500148075108465445104013544c0d0803802045c2d03400034140c2d500080c0c07414081c888003440c40050346458100e920821110701e034001044425403098200181c0d04070380303004031401a124280202d24900558046000040040c44056841d12041c2a21440d40f4001c1c24005030550b120008040b0160058840340045200001e2004107503906102d40100600c041240556075410003159503141d20040c071546402d0315011071801020403080185200800380140801c0b01d042d070920b42850801020490f10b44200015000014a14040d019252103142c0ea100c4903113803561800100070100c0760282025800036030902c0100742000140c1308540c041d200c0c8400c40d0159610300450307204592001e50001c82150018001002050714041c2601c500c04800080942c444000032800c0300c901c400401b9881352403103480102180c0f680c003c41e84445000c00640113006654440e10f00b20241c0e2800c030700320800c9034410308403000d032050094544c6519220f14070025103007654810005e820382e1602e80302954241030700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 837566321 1250 837565071 837565073
    0x111b1c0f120e10050313030f021609050a06050121020f2a0609190b060d080d020c0105060a061d0f040f1d0109050a080c011d030705010608030c0a0303110c030c0604 72
    0x2c1a090040403c13490110720394507044190300c6001000c44402000d000035031600b60009802841a0601c500820b2a0b68034469900d00f88100a000287c07100d003052440c1010200c1c05504ca50610b02c0d15450350641040c05000c01c00000c4000c0d841004203600360303141070089071014411106d40c880084800034001d0402c4410502c450300382600501201c40962006003000a20f96182d41c2c8100c1003078214401c26a1a9200c0d804240c45492545d0001d00c02c1c5030002c4d050446c8006035002e42400d000800080126a4442c0180322245174140514400700d4400f84680c071074903485022201c06c800000c1e000c4400e4041480205080d2502d4285001c02c6985840d68170079081c02c444410000d03008440024494030015451f03c0d40c580c5100c031805002a2000036500a5603071003504403440000b0806031500251040d41c00c0ca9031250060700045442d542003900000303000a00005981c5071141c50800b4066242c1c082d64260001e03c580140c240c1566403d10440c42815400c1c40617181c090713400e02c0038000d9031600e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 837567571 1250 837566321 837566329
    0x2d0b0a08010803030105010c06020d0b121005060d0b15040e010615080a15050108072f062401120b0301390c0803040303020c0607111b1c0f120e 63
    0x1058200010b00d034800d0004000070380c1d206803010b0041d500000c00603610030011620501820f4030b600b549401444524100e00c0c94900003840c80d00c400010703038040010ba1507170b10401109844035000500840c0d2440302040c8480c0365008600544440140009904214810924256440c0f64400300701c901a0707448a0b40056040303d0078940c8080d00401c208501c800c0c0f900300b18484c5105008603410001644000390045004000410060351041d03040c901c001001e02c025101c81d0440030181589018100108400b16200b408036008915801812200000088011185c190455822020141d251240040c5030b4800380b007100940501080200030002141c002c07110003148009505181c9001c9080f0130000c00e40c00300c04641c110b0303404201190349440b2424214003902804040c400e1600581051107500b0b41c000c020b2070002c01e40030f42075407102215800705508015090030b005821454525a01054036450104001d2080c403914600e00002000c0c1c645030000d4056055100114401010909652030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 837568821 1250 837567571 837567587
    0x30302040602160513020903150c0304030e010806030628020d0608010b0a0311040b04090615051c033c2609100908040b0f030a14060303042d0b0a 64
    0x540392180c00030340d844c003004140c1a40d281704138102c4155000c1868082e44e541840b40b044500d400300110300060070b15075030180543c5d2068408401081181e403805205500841200d80f04e090024007a000c0c80d554507e01c085050480f50588654a0300b80c491103041006a00c003900d078600d40100c0015005061609082c00c40d00501d0078144680401da0003080010080c250041e4229015200840c0000c4210701040250140c0303080142044d007071518119a100880f80480c1c01c07644126482d00e6400508110308040b8049043c0141c0000c080f40301c1040c0005841c0c0c08803040c5602d0a4680094013400d0f074070a02c0d0301e00201b03440c40018451044040d01703d040b003e0540c5a1102c010140205400d191001c41c0c0d80c2d81e5401080c05071192078040c1c9074240b0466809540040c1521421141d03580c840c0e60030b81b007440e030044a03413a000794a084841c043d8070390707040b956500c07400001d001540f03000d041008141921900b040c1d0401c80030301b070250304841c40344c00403141c100404107110403c0d2260540c0380b018010300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 837570071 1250 837568821 837568843
    0xd0302070e180717010216060c021002180405090f0102161a160804030c061806061d04022b1103012a1d1008010806070201051303110c0d030302040602 66
    0xc2d4411180d0011840102d80c0c10708032406131114802040c1c5070075500740079000b2100a10b86003694942c50109021207904880140d40c01503013940d0000340d55010f0309003203000d00c52070840100120494001503003000e5000d140c22070020b904503584201e05241c038509903801016400e09005841e15440200207465045082c10404c445650000b807610345250380034104200c0010301000342801c04a0107050084050211041c3c00220a1041c00c80c140d00107a0306060f883c1d4110b070001c0ca481000034010721465440c05881c40c1c1ca00f07196406841e10703000c0001d0b20022401c0451422101c0407603d1803040142c240b0110309220340094054520400101800c441d00310304402070920702c291080007112400300c12448110168100082103030300c107100c1c091000349845800c1e43c00c00d0458400c2415141c026400604a1b00d10304c1c201e40007940d509100300c0c01d9920035591a04540002c0501400084c0149520802002c0a50407104081c0034180001c9069040c45010360100b68005020b001966050007420360344 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 837571321 1250 837570071 837570091
    0xf030807031b0b060108041401063f06020901050423040c0302191101020d050a05090d0504150c06090609110f0d05070509100e090102040603050a050c07140c0d0302070e 74
    0x60b0300507840c0c142d8407483c0203050381d04111900c8006000c0280381401c3c0002c46048400800c50701d910b4a4005408252965444480780101d10002d00b013901010000c00401c1c91400d903440102020350340356806900884100d60500100348404201d0360180102c05509024000310510a68204018007040b503011401940405004200c0d841c01201d170812001011141480c12160044010544500a016030a0400705545c2040c4c2403045510003500900c0c010220320007500d00328400f40205480c0c034495482802c14844003d540c000310b42c0c0c020f0900c0e030000f23070113038070081840d0b14582d55282c1200d50004085503000c42e500d01d40c03205420624040c0c80600c8094407000f1034824561185543c0356610f10a0a100304c01c5c6800080c4810080302801008001c50050003015042541005010750858094100003d2816000541914660040d01e0003010000d02503072512200d03032105201c0e41030075052640b0500c2002004851500c03031241081c0e2041c001d0340a00190360406540001d1041c01030070108071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 837572571 1250 837571321 837571367
    0x31e1c140403080406230402090c041a030714040308032a040b090d05070314010f1e022d0d0e030307020325020a090c02010b0901030c1505040f03080703 67
    0x400306a245199005500b504010440b030307075070b0b10b8a00060706400074006800803481c50042c00300c566800b200703409540f00700c0c1e60071038580d64100752807014059442100680b0201040704d074042d00030080190f4000d40b00c4d151011500d542c881000c0706645c01944219201e201c004200894140d02081c08840e941324514441d180b50750607488040640560b0240840e400300014044000d65610700d050700116a0000035201480ea807410421164486810100c00c25420981d4119540000e03100b440c1c200c1800d07820b40c50345042c0350a603090003500907981c16503148608109119003440b044038925101500340300410b40e10728140144030261400d82d034074803645900500520220980200030f132440d07101c81509400c5000c20011541c90141301c8150043e40142110001003000c4550b5040b003050001e4580083c0404c600f07140510500a209110151000241c01024000081d010301d204201119608c0c141e41000d4540020308000c0b5140e0f84200c403102c50024088040580040380e007040c18601d4a28502 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 837573821 1250 837572571 837572591
    0x903010c09230d1a0702060a14160c230d0503040f080705150106080a0606020d0207090c17090a1b0e0f130515040b010b07150e031e1c 59
    0x40c01e14052010b200e41c01e907041c1120500b40d216070a0984420341c10854080700d50b07070380d842000d0703ca890075141390006008403000202d148010340116904001c00351520421903569100310001580003101810400550034250310108901102c91207040000c118603000130f0f1070340280b051030082c0440c031201c00c1c0702d0203200300030100e880c1c0644a000650030450940c1c0d200d81c58034025050100140e20241001003444c000324400e54464034580c410b5807041001c02c4401e1700d42c481030b03030746810f0803440000580c007000c401d0043c8032803600650420351841c14400c0d8050b0042f0901e500c020b0040340c1c21442c0380d20840f0103d05200d00d42c0182100c5001c0c1e0841e4101d003506060000701c2400c0700034031401d441c1040e580800c01c010100c0345903284054001083e54001c0b25101c42c49030700f000050307506446421080002082210f161811181e080da1320204424407800501c0758080586030860314000d00c1e020620011180c0c01c2c9642c13801080c08160b006c800d5513403844d0b10094841c49a040ca40768005850680444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 837575071 1250 837573821 837573839
    0x908030a2a09090209060f0c07180608030d0e0102090d0510050f0708070c0507030206070b1501050f09011101060509010b0d0606020c010e13091b061103120103140c030703080903010c09 81
    0x40181d4481c4980965600c5c3d031003001c03c550344141124010b86074400103450981c1880801c145054a8102ca0039900c82c0b02c3e0b1040000a0324060300840ba0709030030800c04029640b40981c0031645030f01c03a80d0300160034640e6074400550b544058010640b40380e0001c05059003040407d03c5800e6019030b0b80381e000c580d1805c0820009104420081c081030a02c904071004900340a000c000f107400840c2e0003440244d4411203803404c401141c02c292402d410140320f5800c54139056000f8019208081022581242070158400c01118079007050400c06915568621000c907041d25030100103401390545180c481d5450b03d0100c0034408685050340403000b150400f400d80c0859a0703216030a01900c030400c0301c0000d68940b1205a00000380f820040c000c01141518401d500004804c0c5801c0086410755160486e0501e58100036607224403500942d40c170013545850052000440e1020151008201d00080343e20b843d412801203403505d0425001a20140004108440d09140c02d0045200c808864035000807180e24011602c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 837576321 1250 837575071 837575087
    0xb0402032203090801060f08010b1e04020706110403081306030b01090303081806010609050a080a0218131203050a05061801090f020c070906050102121216030908030a2a 74
    0x1a101c90700e01d1610700e040c5480342c0c502201508080c00200510303595400315101960252145000f01d508044424009240602984401c6620800d21010308100001000000e62107031908442c0c003561607001c06c0d10380c042100544043c62107025655902d0f2040a91004400700396482901014141055264240d034401085411640e250a0034503894540f0309440c0050742072954851128480c0c41e0000034030951106081e001c45400741c0e0303000d08903615030040c40c0c1c03562986140690880b8111461080c42d1041f011426405000001411414261036880903034003e582e5441000080e1034105000c40e84449104240c1c2204048403200b02c0e43e0f40704840890f0b040014440d000c10290f031800300300450b0803190100d4000040400a4070452a160105140107008a000f0607006205101119804915480490b41d0f0002520110b52250303854001c1e02800000c03410205040584480d16440015500c04c0a580200c803522400300b0105840c03130148120b00e820680b01407822000e0010f0b040070316000012 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 837577571 1250 837576321 837576361
    0x60127141e0105090604030b10031403040b04031104020f04031a0c031e090c18090606040213120c0b07053406080c070f03120b150910030b1509040b040203 68
    0x2c01134541585000040c101d01a6600c043c02010030b20301040501c04e207003800c00041c0d81c452041c001703220b9500785801340e90340940e003d443c600000401090000c62008041d00d64090b0000300058580401e61500031081d8210342d0081713903d8205408094154100035003000d038420800b0144078114504001c1b040115100c1144000d07810043d0300c0801c610440c140300b102e614030300c090000341c0000300c00d0110000d640000c880701e8180e400742201140c101d2519008407802c0350140c4010000b2203080c084a03081a078054031013255141e900700000580b82d6140c0018109482c0114040e003c46404175039440032130311035004407103440d0750301102c801c00250403071080c00c05803082454299820b540f00007250000741b1034410050110118200042c2c20036910000c00a20b90780c01c1c180038403103c0461800d1210b03102280c0c00b0200032801c14084090b8030b041580d0724045c1080d40d441c001c58141e031356201240d1402581c1e9940e00107003000003040b00701d60900b0700031441c074803806a40440c0741d440c0407840c80540c10b41e5040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 837578821 1250 837577571 837577577
    0x180d0e0108090c120c0f030c0d0b100906030609030e0f0603220206131a040b031503011d07050f1804122006150111060609060127141e01 60
    0xc04030300592010032002101c200080c101c1c01000502800071a07417101521910f5204010b8160f030b0f031040c1d003804689900c160a01034500000501e0982e1203c08203500104500c07982040d0420001e00307101c450151000030750040e42c000446200ca801d0081015298602a50050004240c65111500d90300216036006021803400a000581120002c3c0701c11019030780658080000304e080c8c410142d41c0f440060071201242034034404114144c0da950700c1070049110b01e2400301400d100007aa0281616428180440014000079480040907000007240e08002c184030325a50104800b40b20703605040041c00c00a0004662901c80088807280721005240010001009000c1c940e0380406d000d0f0080019403004903018219404141e54118000d40d00d00c0e0484521840700c0000c0c1c5132402a5020700c00c90301d07103000d000010300007031350b80c00d02480401600548810304008400c004859150010451070000820003a502c5404604e84141020000c416200040c0315081d0450714514131014914900b0741c4460a003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 837580071 1250 837578821 837578837
    0x501090b1f0e04140906070c0f02010507141509010506030703020d29010e07031b02030a0e0604090c0305090601050f010c030c0606181b08131401021e03180d0e01 71
    0x44400c050b2040b1115045824441500c030202013001c015803081d2100d9040b207103e90380e0440101e890900300d04000e0181070a00e45120b015501c600c3c0104081406607003164500005034007201e00d03244883d00c14a282c403c4a806102c1e000f202030181a0b0891000c5001f040c4003400d540020300c0400c240900100b91848585000c0f03442080c54081903a0b05c14840b0100400d03603514150541285011107940b00040d10b040602c48030040d16149900034800700b40c0c0298100389109030107a4485000c082c010707500100a01000801c580030340180c09138800c1c640da001c1018280810140c3c03410038181c02c101e105202c0742010061343d0b40d0001d41d50b9100c41e010b18001ea40002c0c2810200700030170700c58002c0400191244601c821581c16604074034280c0c0c031800050710400700118070440d01d44a00f941c5070b240d0701a20b8101240170031181e1484405140119000506d00102d802d030303a0500b03c1c585019010201c030f0201c2009214040030f50b500e0841e40e898000b80c05501c422907001890242c90351240c505214040c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 837581321 1250 837580071 837580129
    0x50a05010b221205030d050901050c04090c030902031e010b030c030307080a0c080712200709020c030c0d030c09081606030903030b040509010203330d0317190501090b 73
    0x8505042c005000b142c040b110103406600f42691280d0082d014114131504010105849641c140b16440c400c940b203100e80c40c03c01e8108048400a00079129003502010f446424180150b40d05121003c8050314207150303542d0215070107540609440c8204251031090300a01c880d0700d010745020040344c16042d80701310312581c0ca0044000903141094414800b400207000802c440c0f04100c8010b4410409001c03540704c86170704d141446284400d100940f920110584c010000c00c1080480903005010504c181000360303806d15411081c3d4510b08012148881d0009465a140c1903189401880e01c40203003a44d4009004281001550b01d5002980c0340700301b4081590318a404c00a040c402d9220303044848004000707204a04041044501039001940c00401424000c0900310008501d41a41108111803d0b40e80482d52004000c101101901100c26820b008144000c190f070010444001e51155403c9007404a0403503500c0d824508846050700090042da240004400c0036640b24802040d030a070090744488840f40d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 837582571 1250 837581321 837581377
    0x1806091903050d11030306030a02090a061205010b0103050c07030c1707080a0807090803040e1f08030703050309060c250314042409030f06020f04030b09010f050a05010b 74
    0x5403840424849155800c0030040000201e0460b1903407042e95a1203032808020364040fa220f210580d40503601d070740f00d03000c1c0c2d00c01810002030603a4030114840000965650f1010b1450250310b111500302e4141e5925052040e07290b03014030403142c1104040c03070054140100c40d036000c0d12102c5414005041a03041d460700b03000060b81c2004450741117601520854030780042d0030b00070f001c4010551340c64010480c010300c040781c4804e0000c00e4070300701c0703188014121898455043c40c6a0003014624901d00706140c00c6008240180100004c0c25064400e94640d03071340c0c1c54441d1010703080600203851900c00020070041c41c0b510400c90b441169100c9243c110042e1b00802d07900d000d1381d14482c0901824112800814002600901901031001410025031103858000d85407104441c94065400000c14540b4085001004140a1703405007680700c01c5182d4030307441d040d22503d8132200d0203000c440180c03a580d150a0035404045007400740c180c00c040220700502595040000640d020300511800064190044420050900c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 837583821 1250 837582571 837582589
    0x40b0a0f0b060f0c0c10050a110c03010603050a0515040b010320040c0c030206060603070807080a0b19090f090b0604020f1209030a18052b06240b180609 67
    0x3600421050382c540d0f00e440064429040964020740c58001d02202c0010f40c1004400107407110880e648051a050400a0176078032554004a00030f05407084090441c8e40c0d8030300f44180d2000e14040c00c000c0c40f00c1600e43ca0403602c1d040d0100318054035065400103000008062a030f000381074079400b5a0161000140a0301d07202c0c4d03010010f904d00c0e07000d8103250040caa2150456580380889000e40d007907404c0c9584072014008030744010307201c1c000002c0d054400a860140700d4244070340c10421742400480c40c0028540040c00d0342d40f510380300c1662841602d404101d8081144140040c03485424814004080203845031282c0141c004d15460096400240c0010000010713003c8405503551906100401d01303104480030b41d240c11400351140490002c00c05502034507411112030041311402400d20034400074149003500300c1824041c8c801c506440720500880002d00364003604242e03008000000c2039020f6010f207807651032002c1c0e900a0714403080c2008103c24040303601c10188600311040d50003940e1940308c003000c100807034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 837585071 1250 837583821 837583841
    0x1b091802210117011a030a0201080415020703022a1e01050c070f081608060103030e0409080a031a01050c03070f020a030b0f190c20030c0111040914040b0a0f 69
    0x48028000825143e03003a4801c1e030800300980000304a1400000750b005504440c06036080e50590004a122005600c0340001aa010f072080420f84400398440c1d038500705030380000340d044000d44c00000c4081101d452028100c41c12000c80038008040b02c3c085c0e004183c0ba0600c2c1c004002840b80394008514450340184211501c1030012011103801c2599904858030070301e81c1707009407400d41c000c032140d04810304d028034030300401d45800d50050302446e444e541d0240c40c010500e03210130341c00c90384500103000440d8803600030300070701001614013280f22180e04100c41c080f07070b648010903418040240a16608442e0002c151903403964001140508480140001404d50a903984001c00000d0303903d0030800d949000c00b008a00513001041030f482481e005c003143c01c05860004d40c85000091000012015188448140c165260400c070150307807910003456061400c0d50b6010180c42c0c294000017a04015819180c0300e00599240f528035900003c1c1015500c04074803410181c0700060b040e8542d0310070007522066600c51035800e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 837586321 1250 837585071 837585127
    0xd061d07030606080111031006260103051c09351c03051b070b130210020c010210050106021c0203090a030b15102019061b091802 57
    0x29030701c2c0b034108080c00180c00303440d605508129443e00000034080550340903012502030038190608001c000c4802005c4c45201004c8501d42c01e0200c0c4802052819450196008401529040561403102015100844e80e400100a1544402c000010000d15101d5100d541444005140c0c4900d402080311400e50840020311030285d000b0b50041d880c030048420702c0c4803e80751004c0c8079641d5080e0b9445001311016103d20b8661b041000a40001071502e1207296000c8004580d010b8603054135000300e00d4590014080c600940e04c001d4107c009582c04020304a50400000814081e1750304003c4025102c0c14000f112a00c03005103d0b88042e00140240252428403078094411580f5070f07034904100300c0c801402c0d20084280c1c000b40071040722034244510102400c401c5501d4002c1400b112941c881f410b02405a0000c0d201e000b0740765074400c203da654100180581c001c1e14003082e070711040e001070509000342c2ca040c90144852450300700304900c00ba0180035000c0d015503000589071040740c900d2118601c441e180001203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 837587571 1250 837586321 837586333
    0x109080303010f0e010807060c0321090501050108010b0d0218070504150503010314010c170606041205030a081806010e150907030903081f1404060e0403020109120804020d061d 77
    0x8802040d4910131035401194402c4103076680c038280b03610791000e030161000042030042c0100110313000d006d2004008075035424040e5510503410f00b03007080f0f42c1001c404480b680d442c0c10040000b00d809008034402c5a50440700e061070300d2056800100400035080042c64004401400110101c4c02042602c009110585500000789003030200141254000d000c11a00e0410700d801030341c0121030520a2a41612140e00d0319124661038030500c0d007524500501969201008100216000210b44d9408010500c0f8400940c0c50f001d070080080d0483d1402085901e03802d0081071520808800003070014116050540708450a0301c0701c180c802d580292035001240c001401e00305100c80c440d816131120070700350300070b690b044681c0d20b808402e41c2c2c01c0a8145c80f04603500100c01002c2c80712996480303c0c403040280050001441c039a0f101080691600202d80650160755141071302000d110307001448000010661074124010f290650001d00d5903d0701074405429207030388080034200103080c0d8626000c00c9560f1021200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 837588821 1250 837587571 837587579
    0x1120b0f0405270123160e150c010501141c14150f040204060608131712130b070504060c060203090a1b08071202010c0201080408090618120a0818010908030301 70
    0x702030640160340d000002c2c1640c0012000b0340205c400d1038002c035540c07419800400c126842c03c880420340001c1140d88060030403070044503855800003c104280c1d500c0c00100c4c2c558034141c02245222000810140160800004002101c1006000110495003e45078100c48800c07c0451031030440250080c4110703518050a2142989404822600c2544215414425181ca449044920781000e40c3c007603421091495089000a041e2058a124110500303551400c001c46d01c0b40c40d40c11507400360307902001d4012180400060110812969030300030700e5401d0280c0303801d1414000074000001c680000d01150350210100d80c000406005980800350080154003540300e0f100b1381c0b5500b0392003510805030103120b1240000b90b140301c81c1030300000b4250141c44117400320140d40c0040d50700c1761004008480380036003086a90030035550740020b8010010428403691007240c1c04c005111a40c0041c030021040d0794060500c0341c4c0020b090408680301650000b5801228503c40001a500290701e03030172004072404080000b203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 837589928 1107 837588821 837588823
    0x80d0f03020f04120c1d0604021b1b010201181e15020a0507030305060301151e030503030c0c0c0d050d03020a0507021207030201120b0f040527 63
    0x740c0751015015004125600c650480054190700b2290a8107000c0000305000c041c0c59201490700007814403102e004484040145024421600018a2240c10101c07550498110512000f1a104c09805401c07208254400ca010b90340158070380014101d1080200034010503c9800295210088416030000c41c1e4101d0000d200303455078401c070204800c10700c0b014402816801c646035107a544416691174014160f81d8050a181c0c42603040c900d29a00313042e070b0700c224030044554241640e402c1840c00c002c401c03400c06041c0d102400c80d000120030407050720b40300801080b5001001c02541d0040200d4420005190341800014281e075011902d01500f0030700a50060000c0303c03c504006050110726400151a0b01d003e900c7c418058001d81c0c010011542c02042e0702c0b204500490051215a5001000c02c01441c040c1018611031511600810700c40703024100c585e80724244840c10502003d50030010f403 = true := by decide +kernel

theorem cover : BRFrame.Cov 837410071 837589928 := by
  have h0 := BRFrame.cov_init 837410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 837410071 ≤ n) (h2 : n < 837589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
