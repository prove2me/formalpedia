-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3553
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:59:57.990643+00:00
-- url     : https://prove2.me/submissions/cfcaa194-28da-4d2e-883a-2dfc96f0612b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 638848920 ≤ n < 639028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 638850170 1250 638848920 638848927
    0xd1704150c051c02120903070b04030c0528060f020901091211030312013609051c0f14030c0412060f050a0f2406030b22240506 56
    0x126401e0348200d550408a1424034140000050500f154600241101d800160017103100181101503074849130b08561000015840c01200360b07101003400400070000341c00d0100d019445414814103112003240c2400d00d954116a00191861225089a038488251009031074079410062404d184d10841c2e50340d1074161250b0300c2040c540174040800c000505000c503902010075600140c80d4138100f0181c813859a000595800b15814004051121003051844410500c802e840c01441c200321000515040000000b002c02c07000302506016190481c007619128082006045d4041543d42c04520050902e00b513554510003120000c402e051640410b5460600d0000200002c0084a84ca540300131400c51180001040000c40c00c0208000c0f02e2045440d8403481da04e40b000c3c03000c2440d05205010300940c210700020484024000c242e41855240e02441003410755034a0b20341f003155a0100303c40c003800280d61061b59101c0d00202e450018140842d51080d4000c0f564510400c00c215212042d8152035020700078a08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 638851420 1250 638850170 638850203
    0xb0f160905060702041508010e10150302060d09050a030e040c030b031c12020f040306060506070c1e0503010e0f010c0504060f0305062e12140103060b0415080d1704 72
    0x6583d4061141203078000d0b0369080c0c00030703c2c6030030b003400e04010010701000040300c9c3c000314a02030920704410703210341d101440d141c0f46400e40780c1850ba100b416290180e0b4819140c503465a4440d0040a02040141c205c0c82000000030802d944039a030610a248280c4040c807918507003007819025601d400040d558140c007c0400041003134a004020094951280b8100440000c005442000ca038041b041030039a0000005040c8184203141c0201e01c010300c819507100f4030f4a0071a0300c0d03070a00d0b80d080b8010204265600c85550403214a606010001b500c3d005000304420602d114500b40d1702c443c0e884400da0389509002080c0c0d0300b1380c098810346040768050f8550140c41078000b4000c8008140080416620018034003e0b110318401a0020b2490340f44040d0031885a031401d088064426003c000302407000c1801d12980b6415000700100039411030b5445400030404048200001e4060f00100d00c800c0301c4106500b400003524040002c40d15040095034407504600741188d805080745d41c1003190098000e0000a04144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 638852670 1250 638851420 638851429
    0x15030c0e0c1303050309010810150e0301061a0403050d050a1209030c0c0815090708030d02070632010b07080301050108061306060e030c04060e0f070e0405040b0f160905 74
    0x6a004451181c0c0381e02d48112000c11005840c501d0f00260760f41e50000c0340b499003550304041101d402070102c501b5282c0c11440c10b40140034844050052408000e03a0041e03103c640d446c250411009447c991090079044081d40c0e241c41c0ba682c000c0e21060b03030302d44100500c61245038000c0048426102d183c0c0d5550003881c442010035405060444e804804001215010002040c21a0303c1d441c09024680050403030b99000040b444400b5a01400d025030700d40000000704100400003007160080b040341340001d1703203a24503410094024154104031080070051008031040d004170100000d01407014440703d548c203603603d9841003002c40c080c01d10002c0090300c040005002c290700a946041e88240010100d100cac443ea031a4105d403c1d50019031060020501c0310303000d549586000d20014120703c8007694100851454003010800545020346903409401d5041e0124000f64400c119034080200d01030000d00c05800d00c0c2c500000f00704000c44240002c1a010008510342c1c6001c02803424003900d190395000101400c1a0800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 638853920 1250 638852670 638852699
    0x705060f04030203060a090303150503031603021504060b0108010b04050906060c010e1e07050111030d0c0c080a020c040c0302070c03080a0e04180302061305030f03041e0605070315030c 81
    0x4654035106100c000700595007004118071484101c500819012070f2441d01405903950207100c6a020400c14609100c0c948000007036441c0c0790400d6841182030051703403c0503070904444599103002206403404000c1400714a8008181240c2e007a40c030440315a0385c6100040075401030340a41a40601d031000070580d02e140074802f40240e4030a46000150208880c0050703490071040803100456880440082c440407002448402c1c010042824440c4007110254003c503242c2c031408104088c02d5944150021146125409206000394002c6410750740c0c1190203000b1355283c016002e2584a581006c2591102034424020344550305c0e1701644800b5079500310365a01c941e58012408810800040898030b00603a512802030a15018021034100c141401d6820001d082010040040c0c8000718000c2c0c100c0009000001121100c0146004980c0c40341c0300d91070511014082e48191401c241950000340e0f0921411b503228501a10b80ca450800044100b41403940003884140320142c03880703c1c0901d00b00410121450321 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 638855170 1250 638853920 638853937
    0xa052b030213081005191e0c0201090209090f01060b040501052b1103041712011509052101061a0a0302030a0e0304170c060423130e10060504060503070506 68
    0x31280520340310b41c01d091404c2408508031022070340769003d0060304000c0400b080d80c024159102808580c0024000e40c01212580c0c4980400350340d5441821206c1d4800c1d0f00c141c1b46503600a0122015080c886906a52114403403501e41280d403811800040348180caa00320b4045600c1a1101c5041800d000e040307000f500c042c1c254015034031b4060904441d0106a070308c01c541d1030700c0e02443c2c0f03280c4030308060528041062120729107080581d42000104c2000320821881030441d40c14036485240e40c01740440031a0081040d510860b04140d800c5a0a03400c1d900a400c0496160003c2c0c00800583c0c0e51541c003000010030010a14550341d00030003015102070700c81e40082d0b50200c090503001c40c003415001c4402e0710303561180e44104200c4295448040c0d1b081c0e004d1002d04c000520440d0060309060038003807108400701242102070000c48030b4107107030b101907120804501c80c205124417007006a1205408074035154a00718003403c803224506000460686000d1046400b590b00203401410510b05280500c200b40d80081c10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 638856420 1250 638855170 638855197
    0xa030f05120307020703140703030c170f161407060807051b0703080702090c040e070f20010e0c03120a0323151c2001090e090a052b0302 60
    0x4800c0c00c0c407503550002c50150440e44d0007007040c01d02d141840c0304920150b9203c05c03125002004108046a80400200d01d01074200050f86c0e1203080d41340701d00140340316030758844c49429030200e0944a042030805044003200d0041c0c07446240c00000c6250640c0701c041c2e900900000c41d03108804124114400d17000f400c100081d107041142101c54250640d840d08140307a00480b10428000360320030440c00d0100712a41c2100840000c2410a41000581c000915004005404002c50080c82c905001e12070030f0300100c1419000c0300e149120500714a1540603060180c084c1c1154030501500c14210308000685c00e8200250b00d060506041001c0000c9024000304103010f20450001c1c1c1c4452021000350f2482801035119034280d04c0f00f0200c43c014000003041946044001a0041d140880802d070b51007842da0f0b150803039104180c00c1652000c010781e061540ca801106a11000302c2c10018107000c005400044c42c0e00410858103007525035000102c4101c0c041c0030852030130001c50480e59442d0f0082e0043e0100f454640c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 638857670 1250 638856420 638856433
    0x30d140c0a02060f0301260a021e04021201030b0903070201020709051008060f0106020601060e0d020108040606270506030102090a0b030703020712080a060602190201050f0d02030c0a020d020c0a030f05 88
    0xc00041064010405900304c00400100420041545402500800c81d5800f0000300350200e00d01e155485201030f8001900825191502825800f42814031151401008008640f13881041e400701000407400d0100700c5120b49841c0c042010708000000b540d0f00c0581c160b00820030142402c3c81000500805417181c05050a104004030741303000c040c8120381c800e130302e80f1896010703c0d0715010000f864402c06900c1807061040c80e8804141d55165441d01c1c50844d902800c24041c0340c0c0b69803505030b008204661050381c0c6200d070003030b52420101c100c0c100800c080c041d08005103c9a03d800003014200d01c030b085002584100301440c10001121080d000d9a07000c100c1d81001424100075484a010f42e03c8d0b031480c0c450000d1004810414510418464100948114401480944c0102e50034071059410030801a05011001c91040c0301600802c00301e80c1503c2c581c9009640701c3c1015500c0741c445400030004000503010340036103051824070010b481841c2500c010b080320541403954641412039802a48262040e016a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 638858920 1250 638857670 638857673
    0x307260715050c0613150b0109081204081204050307051201140f090d110705130609060e1008060c030402040c0c02310209150c1920030d140c0a 63
    0x4a0460807400c0c0a4072601d0f83d406a000c090340c102200100044841c007441d254142c045041444001d5070300b0948440025400079100060701c8180b80c550095042c0c1c4211a038050303e4000c0b140143c8116861030045600020f40c00d821940345006078099141c06a0141034200300ca441c1841c1d402400c2c98900000050640408000044820080750321601341000031090028240f01000540303114040e516000c814501c60310080d54030354202c0d2027030b41c1c401c01741808201c113403000c03d90182c4001d12a1340002c11510381c1daa05407400707041048442d98070222184000090b0074030b0110b00795124039000020340b03196a941c0d80c04c000c010130081080000b000f40900d084c0006880303000206a0a02c2041c020514460b504001e031090010307442c43c4065068010b001b441c1980d00e60100d0070400b140703108001d82d207842128090310f180482c20041a01103403030260b51f04e0180f000c503451910010908814043c001e03c54003043c55501c0c01c0720b058042c0010b0000303207010411110386000d091a00036a809440000d07025 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 638860170 1250 638858920 638858939
    0x1d13120507080304060207030f1b031d090f06030d05070b010b0708430b0f07021f020a0905010f020606151b0102091c05070e0c120103060b030c03072607 67
    0x488003251781c40d5000860a00307042e0411f844883c00141481d001071002811103d81040d003040600040500244021100c00f40c014801079081402025044100c249828800301ca445102926110b0080c0111741c010440c5c14801d2084034a0f481e0041c040b0f02d100c0c0d01e0082683c0580d841a04251850300080c00f50010440c00940403585594418441200c0c810065904810000e00c8420f0320001184005c0d4400000707014600c01035010102002000781990b980c1001c2c1d080c5542c1c490020041003611070b00d0b207003071074540c0c0c041d05a148440d0f48030002c0e95251401510080310304009003016130b11481c0002c0c04c506c0d103590003007403d80c2e00c00b1405040643c0700c80c0386489500f4918a00e4450b9401040728104c50800340410500d1541c01c202e00d0102900948400c2d40b514003034000c4000240e014400210031050341030454a02ca0807410a000c907960351780c05d1203030040c0130000c26248280075000d101c2d10310b032500007404403c0d100045017040c80c1c0382210340c21240310088002042141d026260340003c9180a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 638861420 1250 638860170 638860177
    0x212040803070506280209040e0313030b0112032c0303031e06181803160f0516150c1e03050c240c07060b0d0501061d1312050708 57
    0xd605000315141c001500c0d1107420031030002c000b544880440000c01c0079485400c8040040c3d80e00c002d0f0016078030000038000c503000e0491141c0400c0c06120001e10001c4105a40700382c8802c690040414101d41c4e62104400ea6201500a102030700243c002071804500303014014a03c08a10f01c02665805070440e01400b103411600708844114501c1d44401140755a40340041e01564070100032138120422600075404811134000103040d198140042d010f2220840d102082120308a030902c040081043d0428030b030848000c18a010112824094601c400120202050700700d0161a0b0400c0c0c1d00b0b5180300b10200444042d18240416105001002940c545501403483c0c0c01e01711a0196450541c1c0f840082d8403a450310002c1c24801c107150a90b68080b840c1c0c0d151416140390010611800980e035103149003441030282070318407046544510341c9040d074010000d0560000c030071108145500f000001a007449403001e4a401c0f240c0d0f88903003014803000c4001a1a5506404140c08542002800d2015030f40b1001322903003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 638862670 1250 638861420 638861429
    0x702150c01060b09090106080709422a0b0c07061808030c030a020c25080a05060c0c0115060302070501060902030705120403410c030a0f021204 63
    0x1200150315108140280507001c0074064002e80c640c5055501c4020440b804ca0502c02d001c2004102004a41041d10403d00040100343d890007100024400d0006841c407181041c1c1581c26642d2000d42c641d0070a0507281540408210a0b2500c02c070144a41e00d259602071000c100001740111010450b90000d68000c5e58139005445984106440c3c60003483c010044503242c04159038028020306000e000a8400e50440e540501c004a40d60b440b0340b212004840a03020343d00105a060003440300e181040300b08404882c0ba0940341030300301c48156503540c0d20346444000c80314000d0286d81203a00050486209000181030040001c400081c50101c00400f982c00d00145410000c000398000512800b072210074003405000e030581f03110441c03840c142160007a29030700c112140d08106002507000030b0700b85400f40c2c89607264681c0c65101c031045581c070034804000e80380d0301444007001004140b0606144080300da00b52000c6082d01401103140c050145020344031070203007070102c000b1407203a0300c1d6000b140c506402c054001032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 638863920 1250 638862670 638862709
    0x40f05010b0d241e0504050c180a05060412110f01022a04060e090d0203120103031110110c120f220f0f0608060118060f0912120807020606090a0509030702 68
    0xd00c03021002e81c440044d039000134411801c1000784020441070300115280b591404240125006d41540403940040003548000c0d80b20401090010703503060f40000701955144515448010308161a08001712803c07040310260050f03202c80010380408a6000710150300c200180c81301000c1d014541d0010703050b0f41d8190000c0c0d02e00c0a1030000c0c04207000d003c020102070034555001841c1448404000f0810303426050bc40a020068414401804001d003440001c0b11f035884600c0900155a00e1400011181e00c0f000060000c1c0c0705807440c2c8960007450000b40d03800001540c0c01c403460000100c0c20ba2028013101c0d00403040a0f1722820700000d810300e50520740c500404000d000c81c2111460600050714444000f0542414000714003900901a0351300a907590a4980904201252032600308040321001015007150529403a1909501c05200001c0600201c0e001c4641c0d407040b450740c070004202d0f1a0402030b5402034002c1d1002d0702243d5001019001150b00800b420200d0b4148000303178000660070038081c454071586 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 638865170 1250 638863920 638863949
    0x60d08090f0121020c0f010608120708220512030414061c181a07080103150f0509071e060c061e020a0f1b05061602120a02010209040f05010b0d24 64
    0xc600050080804501a900c001c01c40940b500c2080c40d1078152b440700380c50790b0760800207201c800c01c5034200a81e411044980c20200350760554480000b40704401d030042612454203032551a2280c10000121402d845000c0c0701f40c610742c03c40c030091000329004000c6143d0950645040700b02088024072801910070041c040d0503c2d40300b06402d18858001d600048005841060800c0040b015048109141120360251600d85c4001c0100d00d80d00003043d00450100c0024103007420310032000b000141950540366000002c0c0f00c1642c2004020143d110310b8891440810900c200103808034686500c044050400f05001e50119013001d542c20040307030300131181c01d004909501290403043d50310148071544484e1509040d1041c40310381d1203607551a00c0045c141c1450600031801500d910b40f00b44208490040c59807842900d404041e20080d001c4d410407059180654502082d5850800c0e260284504940702c2a100c607143c4094042c10002606035000008c001c0b040f045142441601c60454045c01055010740220f20b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 638866420 1250 638865170 638865187
    0x200a021906080f13020d150e0601170106060c060b0114070303051806070e060306030c06040b04080c0105070f030c05070e101703090a060c0c08070b12060d08090f012102 74
    0x340b0540a4003203140c03400e004003000b038081c3d060060038584680441c1d0300441010185481e1413801a0710400003134207070420320320210f03882c40024080d0680c2c514020042e02e0082c11039001f401c0368424420040002c0340d11040c5c00106186038008110810103141c40400c00869003a0400305a0040707000b00d0000355501b003040545032250102220840070000580207e080c1083c000701400020388034103100c0ca42c00008100c56a84c1040344490100c07014040b2502d45984116091300c42d007040c41414007900030b0000c0c40c1d00701d6104108448005910200419214071251011200080000c104035441d110307580700420a0344a4400e9a031041d90f02980981c3c070241404a81181c2040302c1d45075910690060000c090299a4821140203644480ca48000120b10354102061611020b40c891400e0340203441c40824050300c036100411245a0351a41b00300c5030340700c00003888901c1c0090207002d8074181052020207007500d0010b504000c03200c414503003a101404610350031220a2401101031801030b50000d81001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 638867670 1250 638866420 638866427
    0x14011211030c0112022802010905060708070f0518132313020402030603030d02030a09020103140603060411010c0c090608070b040b070602160f0b01030c15200a021906 73
    0x10300c509800d8024010102d1100c001a109408050300d034800d550b000716100100d0a0511906004458a80d054031010019428040d0080104400640381c0707002c2c41c000120ba02e4000d4620f10300072102d0f0383d2580a002c141c1d1000300c800b90007024080c0001012084541815a02e0702048105040c0b10b2100048603c2a20500d0f6001600c2020060842c85680108a9016032440000c4804e9405460141c1c0d01c1c1d40340400a4194803c105018451034400b0040c0b00b6680c249510080f400d600c00e8804000d80c40c030050030040040401c481c2141d166202c840050001564204003003050071040c1041c090122466441000809103a0040400941d4030a07080208020410826005044d10032400c1c0c60036090ae0f5044003280300d942005480140c0007c1c40f460f0485901260140e207680101e0440e00350001307490701d10300d0f0050070300c03041c1c0da181a810030100e00a14400304c008481c01807511441c1c04039146030381d000319074510072a4146d4107005940b15200940c40740c550034281d5498412070100414200403000d07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 638868920 1250 638867670 638867693
    0x1030f09230c06190912031d0406210507050d0b2208071403040e0a0903090b0a0e0f03101e0612020603130c03050d0207090f0b091801140112 62
    0x280714079030180408034959141c45040b108016100008040c1444400600b030b00c1010490344448001d40d15907005009050340100c03041410222407400300c4200054404120544225018890f0382d154007402002c1110036420341c2002452243c01070b10300080e5508000b81c0785100c0807205403482ca107070f60100f01d2108510400d4031029004415441d241c800a6154007000d80100500244036102c05a40f10402240410070703540106444001106a468016414400380505020480200b803034954042440c013416005c0d2208040030b950342910750796158041042100b180000c0c50b4040c000c0701c140f0b0f19024910300034017900707140d596040040401c03041a00301c21560b1643c002080000040b40c810010303600c01040702e0f00008002040d08034a0501c1c10601560440e603030008080b03210724544004001d0f00450010100c40c1c042400b00000e002c0d03240500196000301195030b60107010280024007000d8004045400101030b01c000040240c41801e02404c0700f5030a030402e0816080c200064802c00280b09180d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 638870170 1250 638868920 638868983
    0xc0d0e04050c0720030d050a0806010306032006310b0f0304080c0331050a050a03030c1406040308190c0807030b01030b04091a1006050f0901030f09 65
    0x4124900e8201c0b108030150140150013040c9050000e101c1481c02d6903101135040d14040101643c82d400d00c1010003900c10740c0300000780008200d441001603003d60107885030208498102081103040024044040d03031519040700c0c0d203603200005210024400e1031800d00308008c0b64882000403511505180d503064220341c1540710b4a0f803050104044551400e082e010b81e60003903403100c00301e40c0b07603024000081e0941c0204c190b140804121946008800c400c42204248003c141d1951b00580e240c80d40f0134002000c0f00c1380140307600908428030810000f881014101f01050081c01d0f02c1241920b01d002403424044280d90607400130b007080082c0000c2c82603403030b407495407000e034a1400c0283d1600400d014044003002003503242030541e5480201c1d07059000b900481d100903001007080025242c58a0002c00c8550341d00d21040040d8140000540d40d808500c0d1000c0c25154240c40384c03401c00c60035003403900d110740c01115400c0c1019187d250000707134820680a0704204610a03003a4402e4441c035401c40441c041d019044 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 638871420 1250 638870170 638870179
    0x1080a050c060702010e190e06030313150c0807150b040209010c060905030d151509060909050703020f07030507032a0209060301140c0706060f050907080402030a080c0d0e 75
    0x464009040010055200c480039103072591240b4075400169515506500c0c1580c0100c40e111442c809115030000490130385e100c4042140f01515040e003416504d010301c210580c50200455418072004041c003007d41d0645450f458241030340c20481d40e8005d030640008104440c464009068000d00103a540160480480c05036400c5050040500000300301d000c0100340540110358440c0b224040c44818022600c040d0b040c0ca0090090010100600c0f079280305604c00c141142c40d0020940701c0b901e101d840b55804451080da120312800e802c0048500092034040c041009040e4200480107820310307404060110680207031101c98580d002418041c00040084244019104420001700c0350840040c0601c46184d4041c0d0741c0101c6aa034101c0841d0043c0201c5a00d154980e40702d034108080b80107000020860548262028454155600350140d03903607401d40112a44840d980700050446407103000c000c0d62040c00241225817010035600c4000682d8004000c1c1c40040d0490081120b00c81e0300300641880c2d1007001d0381c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 638872670 1250 638871420 638871433
    0xf0607050301030b0a141608180703080d022502011d091b0f040e0105011106010e0f0705130308210f010303030c0c12050a110609101503061805060108 66
    0x240020218801408024240001840401c0f8444101d034419a02d14040030110301d03441c03d000041452600e002c040c088000380e84038001550000865070203034565982c42000380034450456940036442e8005c3c0c0445000f01d41d003030001425410000c051000300e06a040040701526046000041c00b0001e02e0810441039191a0a80e050f20340311401440d03449004188013001d080f08500307441c5020300c10031607400b90000c1c0106005c01e05540c3e040100d41228003d88900070b0780300d082c10000ba1140c109204041c1c840b5030403000030300c1e012008030030a40d0205107454a149400f0586007401d070398221640050329001b40c0418000300000c2e1006201c10140c828038110456031408541c42c01f00400140401420540c4400d07606900502403099040309907401040d071008580c41242c0140103030015402440040d00a10420801c8c0c0c202050050003094860041e10101e10a0716014010302100040b03144152707080301001010039528030440589880440d201c0011102c241005450b000041e0000d030925041078 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 638873920 1250 638872670 638872681
    0x1605030a08011d15041e11180907080403140d0509010614030f030706090c0e01060806130e0a02090c0d060f08070e07021513060609050907060e06090607060f0c110f06 73
    0x448940a140d60817140480d1500c000740900c54544254494061680d0905503003a0b005103402002d800d000c041c0360108034500301c00800f081030818007512482e02044948001c0341c0407c0c4201d250703025150205030100c0c074102c04590030500f200d030300304d0301e003003541e5510081800005891020110700381ca0460040140e902d41e020805c1d120b2040580080c041a50b88002d41e0030800500e002e00014484c27080c20701e803a586d40d6a0054100e4a003224440d00c03510a42d015004202e0b1548200e100d61042c807001014113400e40c3c1e09010b070048014192641398181403000d8009552903008100140040143e081499840c0002c900c1c074142c9960400608802118104100b16a00140c000c091950ba8a0b912000f038642401402c40300b04841d40181c2401c0c01d000303010a0140c4150020b0b401142d00d1021100800d40e500000c84203440d00c4c03205039074810780802c4805c08074a030600c05000c40b42e00840c00080c5a1200907204002c59698a4401e00424020b0b4040d01024006200e200d403440700382c001804161408 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 638875170 1250 638873920 638873941
    0x180b15130806010b1210081f180f0b0a0b1908060f09150c090306070804031d01140702010e04140708072d2303240d06021605030a08011d 60
    0x7449800070b01c50140c0307000600b0346d44030000654000c114140945644110b00402e00c042d1124560403003800394105810301010329001081c0601031504074880070080c90640e42d8401c08400064181030185880e403160411555401000303100d01c0880c98034814140e45070100306414048011300110b803c3d203802e0200003c40d2004180e1190700652514220925036030000c00c3c0c58035003e1201000e805120354401c21407800c0d080203039180610b000e603c5000c1590306050181c946104c94858690002e80d002c021403546401030703030203001c0551050410402c10200640882d00311380d407004944921043c1031051001142c2c1041d0310036042421464461404003010305c45002556070116500121201001480d0000d4071481240c18000103809189103580d00d00c001041c0b480c5c000ba20950301c80500701c1954219407081050302c1e00030803c01703807492181c04503e44905c0001c2d0880c9684000864008035403034000742d0705100030607585040b61280750495042504404440620542e90300b54600d0b15024400403506 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 638876420 1250 638875170 638875177
    0x30506090105010c05031608131502070513110c010b120703030e0d030504210302010e0f1f090515040302010c1d12120c07090b19180b15130806010b 65
    0x4213080000704918a8900f80345984624a0307100b0f965807a0b049000100b1600500500e444803044220803041034a5036091819004070080050142c3d00618041000b4208940b00d40c400503018100025410100519822550700103800c1c003816035503525601c58145011071000303005104520013804050b080d41d601070308088032003018502c07c20000c402c640400d44180119005444200028480800407800010b0500403009084000d5400c106c620114a4800034920151903418001000c0603003803031200301700030740d00258914800c5440b07000a4000c21010070040400d41c5003d48aa4150b14140c02d000342140d403113001140c00c120a400c120903410701c0154480c0c100600c2180e44c000f905518a040d90f02d00f01c1c00c601c88600c004004030759a8001c0c1d00214001084500020040c410301e4800000c116008051800c466400b102c010014008512106500120300201640000c0c102108600041209070502007070012000b0001d8482e031111850820b4400030600040100402c0d41231075000102400b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 638877670 1250 638876420 638876429
    0x9090112020d1e0f030c020306160f11030f040605120606030c030606090d06050709060809030301080304030f080d1401031b08030a05130312080f091603030e0402130b04080c010305060901 82
    0x1840b0310700820081c05800b000500d8551200b43c0300000d219500d40038003a400041b900740d02c80d00490380042e95401000b03050003000c101c190707100ea221741c01c00b50080c1c5140c95180007980701403106124000c07045028800820250802d070f202d03a6100c20003e804d032844240018500c4d401030300f083c0144444110b4400030349420039030854440e40c5410b00c8001140c015200f018029050342e091105101c0000d402c0208602501c00960354440d03070b9550074042681e00e200a100380032032a8800c100030400309028180800340c462250b00715501d80080d40401c04241c864040800ea0000c8142004104100908003620083e0306905104c100440ca4060700b00c0d201c0c010441078905000c030025402c0c0312001400101d001840e4020384981d051921020000c03c040000c48070686a0402e420205220010001d0340011220002d11501140c074115034040784c404155030b0300c06d500a42c0a003c5910014450206500600040301c0400d880b14034003000a0f103003204031a9414145031600c0306000c903540b1401350290665 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 638878920 1250 638877670 638877683
    0x15050a09060e04020c0d050a0e09060d0b09070e09060106120b03060703021303021e01020c01180911040b0a020d080604020a050316090308130801110910030507032009090112020d 78
    0x2d41d15601050180c030a581c0c02ca030030b81c041c1c1c8040b020fa282d0014090302000406640d0207110030002d009100c48180243d0f561644a12482002c200040c1e8011007140d100ca0480180d034015591460000b1741814152800384d02c981108005002265100c00c9940381e081c0b10380000d01081c054200402e0b101e21000d0285010076030002030100190340540e80e040015a40500710880040c0b143c040080c0304904507111034014090000340800c3c0e584121801c0a4000c80603812101161400e4140001000d04810240b0109010701c0002444c4005001808601506401401d4a212680d40040030038100030700880c422481880f00314000c55000042d40d80c03140c4c883e204c24810840241e03080e10041c00c954001000c2c0c140000b1070745080582e400700203003164003400c000d00204255000b407001c907001d401ea086402a00f103425180d15944250010b40d003107201410b001804040010040107030b4580c0100d0156000d4000a411280381440703c44140104a0940481890061035000600301d044003036025122 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 638880170 1250 638878920 638878937
    0x30803060d1704030302010207020f0f1f0201091406060a0806131b05040203131a01060e04050a11030702030a0215040809131404150506040c0221040f03050715050a0906 74
    0x401281904281002c03080e000c00b1a10f465a0f403034000e01039444404200d0050f90b0316035050300300341000007a210315410010300a845a0014650a446000c000315400c0110364030f50042c6030204a200c0c82215028903004040e0102c0d240c04000d100442303c1c5079011003855808103007040001c0e2460a00c901d1050781c00300d11040e8411004118405603200d9800c0b4542c428800000e00c4000003844190200b1140f00711000110703600d10030710210311940e0900c220b07004245541c1413051075207040c1c2d011b1940f0050701e080c00201c0b20380e070048960584e0004c0f078464016a100041c14044141c0400c000803a0086220059070585426543d100d8180501c00b0050b00444c25440203440e01c40161b003203215180480d4170581c009181a060180740360381001c003500c001ea807401e00421030a003001c0c000c190140701940c000f4811003542c0c080300c903003501d854a4112019203043c000420394040d2048000011130003107005201d500c2c24540c0d03031203e0410052210b428172208019084074a0342140c07c10048441c9410030114 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 638881420 1250 638880170 638880173
    0x60e03191e0501061802071703040b0406020904021308061e01050f010c080f130906080a03090e0c0706140f09030a0f0315181401140d06021b030304030e19030803060d 73
    0xb40c0813507040540c080000000c0c11541e0b20003039015000d0140525024092a600202c1c5180c451000b0b4402400d18100040041c000c501d9036001000082c00c003802c014640903084c4802c030359001140d0400e0b20250040d100303219030340350220030345016010000d42c1042c6951501c800200b1100b01e1280c05810311a54900c69001d1000d2001625041d003c510039040c0d442c145c14a80b03210201c00350041201e250310740100801c0c0c0301e0002503002105603064403009540341c20030118580a44c0000e100001c094030402000c4000703003031030080b508031248003903054002e410001d02c007060288000340052007030b41c01804a20140e580c0443e401e1618512820006116a2002034220815005402c4440e04014649001d585900c141c1e00040e0115403888164890766211344003140301d81c854550903903120715045120804254598010001180b843c8155003440c55013801d01e0b8115001254294003181c028040c48040341040f82c505c00c0030840f2003901800103030855072160440d002c00347c8440d00a081c00745e203250 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 638882670 1250 638881420 638881423
    0xc0d030905030a12170c030403030905011b0315060c02100c02150a08040605090c030304090e0c120318010315060315050303030a0c030b030f0601150c0c060e03191e05 73
    0x100546009400e4548045184c10907610f0381c3c3c0da500c1c0c0309000a502c0700b040742c01204420a01c0c2c1c01005844803444c507684440e107003100900342c83e06050b80c60355654914060180d1407103210420702555903c0105210841c0400c910460340c1580c01441844011000380006969459401004803500d00b40450311030311900204003011510040e84902420025007055001d0704584417500c12441614284150760f51460000e031144203001d500c0e07405074003d00c01403100c400c2e0b6400543c03198a074082141c00b03100da050b0000b43c448101c164894071a400008004040683d039826031b10038040d080c2006c2c461175110001c44d11100c20b03103101e407204150b40d80c0d00c4c0340e1845583c141d400d8005c1000400704c0b520707801c110410400402845841001007480c0807103503201414003058404d410510360000e481968603106030b4100104402a0000c10019402d11600002d000c100c1e5610181905658003405c280711501812700d82480384101c03c61888080442c0c0000030b0980055190940e04c42c000c1e00140c1c0c0b114940306 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 638883920 1250 638882670 638882687
    0xc120a05030301060815040911120c060f07020a060906050f0c0109060c05030a0c14181318020f241c0e2b050f0a1214010e090f0c0d03 59
    0x4045001c00000001c10582c0081300380d010382c040040225501003103008100440304403410041c403920244c400b0b21840e2070300b0004a000c01951206031400760921100142055201c080d104841c103501003800320541c01c01000d050090700e21802d054903007034106031014009004000d41c2d030008501c0046c2071a4014020b42010304059800101803250040e002c8018040f80c0040311f5000c04d0b0741c40c11501c01001380c410a0301c0a104080382c42503602c0c00c0e203138081800340d49201c3d00f5501d03023002d14403071600e265003c64460b8014011402040c21030701c00c0c0500c10000e2100844c840c4500c2010b4600280e0711102050031012004101034251540c0da2620b8070f00381c00200d0482c84038460b401d181034607414045c0c5d4003040c07000c42e00609415400403911400141411340d210851701c0310004c1c001740241c1c0f040c155994002d000c1407120b4100004515401c00c43c100580da58074044031030340c0103a240100941e441801560b07400500c4880900301b0000f840248940c0c0721150100540300d1201e040c0040141401130144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 638885170 1250 638883920 638883923
    0x50f040f09060501050415050f0904060b0d12030501050f01120c0e0a090209031c0818101118060c03070803190501080d080a0506100e040f060906180e0c120a 69
    0x60050700003504000c40207002c240700b9203004500300700c14194005e40040303c1c01d0030b6400003441d12481d40444810b1101e100e070000c0044401c0c590707900b102c6907955905000c810020f80305580d890300c200e0542e50001c040e42c0c41a44201e01404070114076041c10780c0c000e40c01604042c40001c000903640b40700c0c40c0450324000c0305a5250742050520b040031801150301d800038403440ea010750072030707150800c80c0e001c826413109640c055800040440c4045040700740044074588800805800300c4a071074140c0c5c51250100e0707560400742e0b074605030000b42510000020b151100018074040319264200000304805940724842d07903000510b00c1c44c002000480c4102c041058910601c12079100704619a116906543c0d20015101c660001c29400c50020341300c48524015a84207180103040d0a00440714000d055a0912046525552003510782c1c505000841c1d00d4810f0700000e10317940001085a82c03606840c0d8120010b04071000045d182030107844080c00c0c2001488185505060b5070b01c2800e410b03846442800e01016050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 638886420 1250 638885170 638885201
    0x30507090b0c0a0605060f150c010204210b06030601081b22022a0c01030905031210051c0b0c0702130203010602030a030e010e06010603021b0708161707050f04 70
    0x80003000ca540016030220140d00c25213003000030b0340343d0310b0400034050f040050391580031040428440e0744502030320141c450140c10f0000942881c0e1034040380c040d54809081902c140f045040c0094080c090b648210a402003030a0380a0046941802c0c0c0039610f90480000b52a003004181031061940c4c0c50b4900e986e07140701c29070710151400000109103600a58400e1010340c003501d1120441c110600708050503588040403000c0104941c0540170010f401800300510140c4d158041170100c030010b040b002840500c111146800144e1941c102003c1041c400c3c8014410310240c450000210000344506040613040020800c109031900c3c910310009411000e455282c4200d140007100010398150000080c0c88910012723101880007110304c0d100c0c03500300c5016003c50f50310750f40088010801e840c0207500030090880d05149401100300c2c56910940f418405501807009540300c00c1100188030a031a445002400d10070002c86030a4030412100e650f104c1017070142c244076825242001d183c550700e80d030000e84000c01200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 638887670 1250 638886420 638886427
    0x60108090a1a15120a02102106150c030504170a1401020c01050114010f14190908010e0c0109030b2505070c05030c0607080d090503160c0806070f030507090b 69
    0x424a540b0301c1c0255024041402d15140000c4580b44c50680306034030507107500c02031000e00065001c00c28030f05102110781c424441e00000340100c5503280c0180c1d14405e0329000020039050724060300d09000303582880c800070070421100800d00019511000f19402c0b039151070f2030070007407013500880c950405074803002c018500d82c00d1030aa85c00071075041d001740800e062140300030066a0f0307842664800050510002c0b6000807154075007450054020703500741e411500e00042e16401d1010140d845a50312014411550104800c2d03d010003c0800900402d43c1c0391920002600315030310f5040c00680f940080340002802c00013014002000361402c4001050840d946940803808021280300240495014200a840f181c2030340d41c000ca40c9041c0000e502401000262100c1d2a2401c2903e030000c041d0450650300400e00e895220320310114400700302a0410700610a00071810216034a880c9800500550251009801c03c4007040b100342e401540c014603202d05828045480c2d0b4400b20300320b03084940d6400c850704100703011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 638888920 1250 638887670 638887703
    0x21c0b180907090506030313090510030611070203060a0b10080408130303030c081006020c040f0f05041a0f22060e01110a03230406150f12060b090f060108090a 70
    0x95030394101c410440d03040000e41c683c0c60a050b241c1c0300d22410040d88c580941020080c03207420ba0310403079000d0003900d9040c20003034592b134868090320702800a105241d0000311b80c000552400b4810590040d0014104002100181d00400c1ca6000702c050120140000714001070144040c0c00221040c41c0d42c0c4811407100c00351a483d02500070b00003d01c5840000d1010000504000000c08140702554108e8008100700c3c03d00c0d1003000043c0c800c00ca070400c485600c40d9034918a01c203080c06035074007c900c9a000b51410b11800182446032050081c0f01040d090f0316603050080825902c2c450300320b403401c0e034120340c2c10b001642d041c600c0180a0201c000d415070343c60120106198612303c0007030b0075409510765051200c0d20040001103440c2e4070b070596813001448160302040000302594403180951142550031000103540d4080c41e121440c1e41da0150748118481e420030340400c1803900c41d580510800300d030003a0250429a0309005281002005203050140080100f400c14504021500402c0c1d0b03c00c01014001541 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 638890170 1250 638888920 638888923
    0xf08220308030712140f09071a0a0e06041404180836281d091204030b040f020a050627040e060408221512021c0b1809 52
    0x8840f81000104011400c140c41190703800349002050840082c3c541e591190352681030301c0c6101411845075031050902c00102c400418000060b154113250300d041d2103032240500a8280040005290b20400081001f4020f10340110000145484240c40000b0b404d4140041442c0d003203000c030b1001c2c0c001c8001259034258180303000c051120303001c505262000001d642120f944200740003c042158071000000fa4018030310355244801c24005514841200c0c1e850343e0303076a85400b02c525141d840b250303500014200b04050404014942e42480c00014003840c151558492115050300988000c00501040c0c0004096683d5840e2050240a005200987d00c1c0208502c2140c0300c03105034084030441c084080c2c1e41140d40303083c1c80380c2c0c1c00012200d4068074540d40c540e6900101d580c41100c95036100101c80d54000b07880d4000c0500760300900a0048000e94030041d03000098038071a0700b0749800d6078590040080c070001c0031901c4102c6d0001c8480f2203021400307580039800141c811104404540d0000e05050070030512440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 638891420 1250 638890170 638890177
    0x60e010e161803080711150703050f090904030801030b0c040b0f160b1e0a09030804031803060617061605180102010207050628051b0304050f1507020c010c0f08220308 73
    0x208001c4c80f4140c6c11003609001d10f4028030403200c4d0100009000388d10200b40610010801000b400060318608118500010901e04c019242900010101c00050080029880751310f90080030320640c10b802c1910341410640b6901c914400c4101021010131403075201c0700710300c1103501c0c4951b211503103010394030741520080c0d1b5403d6180c1188060800600200b00361040e1842a100c042e9010b0390380412581d10783d01c0986448084588400c000c104081d0700001290140c4207800241840340810398550118003a02c5180c9a070140c0345144040140710b00c0c1310110380010031200303002000c07207001d80100800d00040c0c2c0203000c1c0c070002a0450050500308a880341500e81c011582c050310b0a4003122034140303032404a00300d81c412910b40310683d880291440c0d5800d2020040d5030301501c9401254040290005103604069625208200c0032001005202e801ca8062142e102d800ca800c2c47c0c0b1110011054903045240d200380a80070b0410703140020020f05800740803102801e6043e03c19034120140780e586c60810b09991 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 638892670 1250 638891420 638891423
    0x20909010209030d0e06040e270c0906090708011a0f1306021905030a030b1c0302010f0c1107090f0b06040f0306060f140f1f02070504060e010e1618030807 68
    0x1800d600d50f000a0240c05c80a030442005002c4504060610042012115010708110980c0c1f40032810311403508180307407111949182103006490105010703002e1241001002d05150f10500344802007064066002c0e0805044a241844111520103c181c0300c1c0c17914400c0c42840071800b000003829190445a070003d260455443d5402c60b01d9030f001da1031540c4440980c1c25001003540d0401c00000310400e01c00c1d004090181801004c080101508041e007800c6822041d4003280540d44542603070b90403c900d03110f80030035220035041900145602c02c4069854a01c1c0e4000e2044041c0d940c0d000c1c1c3c031590480c0d84544e00514014060560f225101d207a170b0340900c4024841250407505100010904110303c0104000700c0308580e095140414022040044600b10f800403903400c481c92207040c00480c06040c103040000b0107035030007511070641800d052000b5650303203400c0f0351015802003004100c207200200100d580480401e000440900030103004482d05070003200d041700141c03115080413003403000403001001541d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 638893920 1250 638892670 638892673
    0x507051612140408010e07080f1903051216120c050409050c0408190606080d0c0303020a030b04020301090213050609030c060a0c0813080f07240302040308072301141303020a02090901020903 83
    0xc0d58418a10b03075150302744070a071a40c64112030801c55a80c61f404e52005a41c80c4039050030307810f02d01d58008128603142c003110091039644501400203881a0003018882c2d0a0810b03210030b00c560100710402134081c1c4218072802d51101da80d107000582c03c040c01c2060320041c0001109036001c1c9040c0d501c2c011400b038544107055807180d00d0098000b901c10000a101c440100540c0c0b03800306901c0194034240d001307400512545003030540380d40400d19542d07034520055003c1d02d28818010b88038100000819032101e010740103540100002c00c2000c2081e0ba0000354000303502d004072481a6551490b8900311120619041d000b03040c0e242c042822800c1243c406c41d8001a211040100c0d8024448603d800d65620414850403440c4048036500d503150410b8281080b03021281c5040140c80c043d5680e8a0425542c450300c4203880d00101510030b4969203541070104502818040020f0240d440c85c1410708941c040060540e01410031900c1001c0d0815000b840700ca120706400404195640c80c010303401d54040d41c4110a4184207 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 638895170 1250 638893920 638893933
    0x80103050d051305090601260106020d02010506061b0a06020c100c020a020d140f0304030807120206071d1210060801050c040b0d020d15030809040507051612140408010e 74
    0x40c20b02c200299100546114010f001441c80c1c482404031194029204604002e0810034455115415079800d40d07a803030300d01c60303040f44030740c50030400909051090000004590500301484041d036110019101e8101c2803414100c1f6046021000320f162006001d00101001d00104408260380000314015041007880c0d5000c2c40003101c60308080362100c001810003540900043e00341d4020500c6000c89414058007201116030709028010510700d141c1103913004468007000010002e0400110f07060510f0486503038001020b03241804940a40b107444a52044020b450140464113800d5450340c4041c4036031841070040d24919015201c4e00800b41131240100e080369801c002c04078100c00d00341c138103c0d02254000d80320a03050400ca001c2c00c0010303510903c2289051038a408017803203807007011125a001188916442d41da180900c10034401928802050201409410311011841903048507136101c5903a80724000e07000b90310240c1820348209020001d0031140c08800b10b40440c4512055122032105c0c04403c04030740e413 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 638896420 1250 638895170 638895193
    0x1d070501081803070b0c13030f200603041e022e080c0a180506030f0a0507140922060b040303030b0d110d051218120109030e060f04031208010305 64
    0x4145801c030394840081e0f401007180c0c0e408240005442d542110b00f03085490720b0314680724104e100500d00c1742c0041d114058280c400f20200f06903140004d12300302c0303c01c1c169641044d113040011800d0000030300180c094079110041c8042d00c24a03c04000b01103600504500200d002e80111034041540f07942d051a04a0150100c0c84e40e0500232690248104000c611443c90111000001c440c20040080070500000040a01140c1c0d592500043d42c86900b2602c1200218070b071244c1c605040e118081c24400c00c1c41070f143d00c480c040204090455172503000c1a01e06100a580d01c44a03840b81154494912114503e0208081441030104005004880c001e03501030200c4400d4a04120388a404814000c3c1048407855958034503041094079520550b001d0313000e842105c0c1c01c0203101030f19039000344007210100307078400e001000318546056584801141907000700f0040780c1c140e80241811490000d0710307108410101d803106124852000301d401840d444586407084a01c9c021000c0e10003d0b080c0030403207050148081021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 638897670 1250 638896420 638896441
    0x2191209050304060c020d0602030112020915030a02060f090a1e0614090d140a0c09111e0d020d0e15070c05060106050901031b020d18030b0105040f1d07050108 70
    0x40d103258216014500d000e1500c2003e4072000e030000c1c412604110a075540c000450b038070b84050f5000f170005190b10140e41901c0c1c4108075419000800505c03e40c20400100740d610303140080d07618240ba9050f2012561202000c1020380340d802a010080e030311040ba008080b4040521503400000c10340c03140011001282c440c03806075024003441c610400d5002051118036110301d0b1880380c2080050003076103c80702d400104102a070915425160940b0401b42e021020404102d440c4203074000d10350351100e800d040c11800c1c01e000c52a0381c0300c04c1410110700e40104da805911b080c01c0c0e04840c54408080c0003004820690901030b42c4421050011030081808d40001a92241c05544102d0909901c04040d1210340e0a006059440ba009100c405040545d11420107401c82c4030502942c41e040138540052515010032403006000069501482140d100b03060010400120000d040a040d6202140d020401d900b250845c400285808819181d042e04004003034081072002184a90075960300703980e940400d03600c454640 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 638898920 1250 638897670 638897681
    0x705090c0a050702040c09082b09060e0111160906080d08010f092c010504060501060f09141302070804060f02070b0409021b03130503010539040306021912 68
    0x40102d081048a50014a495807010b480c0006904088000c6612000a603242640e1741d03500c060010458181c580c00900520400000c881061070000016800d0220003094a262100724038140035920b60703440c200150900801400200c4107600105895443e035001e0040d05075403040c04130038010400301c10507603449030503014140c602002c3d00380229490090510300400f000039a020a140c51303104e100d007034600391072051681540c48a00106880c100b0341400400c444046c2e22600a102221200644103500003c16404881510541010f02c1943c080852085210010b506541300e100050020030007409074041d205070340c92a500c20b00a481c030940245d07a80c00181c0078681c0691030500080182e21035980040030790307540d03501c4e500f800b0a4074401002e00d1604507420192400c1041c000500c004d00707003445103d602510b40d403001220f2040341c036029000c10301c090641070000440320840c1d030000c02144048800031a8401c0003107503181d80241c840283c0c0310b041c540242c006001c0d47c94206000741c003030040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 638900170 1250 638898920 638898937
    0xc0201020a08060916210515010807180b070807020907050a18120b06030f10050106020c090c09060c1203070c030801050402071709010210050108010603230a2907020705090c 76
    0x500c2c12400015406480302000e60180d4441560122100404c041c200c2c01118048c404800e01c0e4200d03800c6410000d400c590004082c0010004241d98003a21030400c1810b100c04c0780c40107030072180d0351681410454440d12030407501a401403840414810324035403200003018408199510300b0b181d05482800300300c030440701d8805c0711360303000d440078504011413440588180c0081d8001c003203503507039030b0b50303008050a180300c1801c0f081d1440c2e40c2e18010840340307805204801041004940c220003614140101858500401c40c005004a07004245c030143c1e41420450901040400f08010351a403070044001010907400e00f500318002105413000042c0c40c2458000c0c5c0d1107542d072090900f01034a400b402442d1081c0c0210310210f0451003400a020020341141c4942c6010b0001003002017546421820443c4100c1d04040015804804d0344000ca0080e0001240c42c0c0041940400312103000c040b44441007000580301104400c402d84840e041c05046a00003d00400700d80059820742e0180d038403180409824040c101e01d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 638901420 1250 638900170 638900191
    0x30a060e0108031909080a030807090b0c1f09020a0e0a0c08061804030e121b0307050901090f1b1d0102071401270b130e1909050708010c0201020a080609 67
    0xc84684030003400c40d204c0844803103140c0191a030b540c400c0200c0c5401090b03d400c2d404280641c1c10f00c0070281d030000340d0902614070280a030340703440c880c4168643d49121050044403001e849454404002005803c1a039070741c6d0b00207000116542d26001080389200c002e442c0001001d03d004810001e0600451440c0d1056600505075017402d0189250001c142800400c01c408000941283c40d03142d55501e0600c00007444560300609150964505055080980c40100c078401c1d0f0144d942001140c1e280c4004606441582401240c10007a01d0b904130054440f000b405880c1c425505550ba10642c0d200100521920745000c1d100d448030404001a0b848805070700403000520940c2139000d0302035008641c0818a881007071440750800714040c050078200000381e000b098000c50000b0b02c8040d68404450740c7e2001d8045081d100c2c2c882d00303040c045c1d80e105200000a00c105030707444055030700034444244106001421048024040c6080b0114024001d5000e22055004168460049403003400c281c1000e40c882c032583c09 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 638902670 1250 638901420 638901427
    0x80d02060402012f0d091a130b0a0210020a03020a180b0306011b060509060412021f05060402090a060203030a061e0b09030a1703060a211205040515030a060e010803 72
    0x3042d05080c03200c04000200c0c0350740e13080c0c41103d0040400444060408135540d03a4034480c02e08103e60580c808040d2246e0400380240000c0000607203e080040440d44d8512100395112a40f0500b03070b041c00c1003005060300300f51000c00c2d00704440e43c140d0001d0140ca00309584000f2a0840c0d4004118038000900a20310a400103100007481540205004081104003001360100c400013560380c141900c030100c88904044c0c000400b03000c10407042100003403291042d8005460f40440380388800c060104c1c004110a03d090303c0d40c0102e02c0c2e40c0c0b00c075412240070040150080580326143c20010755a5441607590441d0145018000644030741c111500003180f07407082042441280c40c01103560b18a41010030030030f916003c0d0344a1000082c83c040d0590400072082c0200d03039140c1c03800c80100151030280794021081d04a074844001e0404c49201840e01d50f569015160740c0504501c0601100c0a00840d042980c108080340710411010034614061445803108250a004058490132290300e055000c4c490300f1107039407050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 638903920 1250 638902670 638902697
    0x501050108042604030b01081507050f070209190507030c020d020a0f061a1f03050f010806041527061a01170603010207020916030f0c05040513060902070c080d0206040201 75
    0x2042c180c03100403403a018444c10583c0ba0788424517030031001e0b404090700358081410814101010804103a0201003420514103000c1000c081005901c554000207102d0740d0700c0e030b0005442c1003490542c900c030326580300800c120500e40a80041e0003020070030010000341c8600b2004109541c80055030381402030307008400c42c2020030245c1c0c07414060001540c4075400080441031060490300d42d140b6084401c40c40d0a20b004548400f05c001808907140a400c0000f1403620a00500c0000d10001c2c505800980c403405003000301d0861800d000080c0f85543d081564520840c01707007417602d034004d0014031520740220070400031031842c81d0303102e152040c50b4001d0a001c5120b840d42080b804047c00004c950200014001501c1e04a2690020344802c2d002c607010740ea004102039210300a2a4180300d503d090940301c5508000101100602074040e000340d00c54103100d46440b1000d5007007640c56400c50790040c40365200c00d54a4040500e050310980803e40115422441030800a001c40d62002172994029a0181c44032005840b00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 638905170 1250 638903920 638903963
    0x6090d05070b0a06090c051c09170903121902070b07030e0915130504151e0b0a0510020d021506060d02180307060513051503130212030715050105010804 67
    0x3045243d00caa80e1300070001e81d50403e805020403c201070741e20656660750100305100c040c604585201c00103850b0240d00340004040d0854100c80e00e1240384015100d068040020745414410850300210301030208003140d1580c00d00c68a48005c40301502500c0c40c40b41c0312095004907000d42d09005e00000d0040300c1a000d80c0c00d04c1d0780e820b504031a1922640380c4051000c0d0201e000240b030001011001d550b0703002000141702d00d01001c6540d844240300284020305400403418603a40f21091079120b01c41e500e0341403808c550385000300c40000344400391400700c05034000711001c0e48134025208180f0260150640a06c00c1e03983c004c950a214040c006c0440c5d0078040980c40c03500080d0030101800d0320b00c84200344c0034078a07550100041c40c003d05542c0d0381c40381d5450382900f401c11641e015900c0540240d00d14079840c0740080c503820603680d001c40c00c01e18402c05030345140001416040710844451141c00001480030500200140f036141c1172083d0171003071107503036680c000464800b2001c41c0d02800102d2814025080d0800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 638906420 1250 638905170 638905193
    0x613110a02010b031605010c150504050c010e1c0303021b070305030904140106091a0f0c070f050a06020a0f0809100804111f11070504020a0302090f0609150d11030c03040506090d0507 80
    0x14000307c2841108200c10750b421552b06541c299010f51055406074000d690180c9426a00a000e82d200080e0300d415040941ea50412418014203150300421980000e00a004500c054941d1040458541a5a0f81096074595001c00e600b1401170f400c10a00f00541802070182070304030b86469885403400d91030040c11a01110050011b031303215400030000a01400f0568000e0080c0b4119240036010040c5081d01c440d120384003c0c0d01c21070194492040c10083d2a0b0041088844190058a1000001810310305401140315490203658420a00c14160000329030008030244a18401c4a6000b09200d03100704203c40302d00c03002c00f40942c40c000441d51603070640c40740c9005012851a07d08032914241c4038800203090341c105050309400a68042080b503207500c0e11002c5174038035803001d07544280782c24140801304004076001c185003108800b0000d00d13141100465401a03502c900403a0b40241c980c104403a421f00550b00c261001c2d00e062041101041003000045008480500c0301d0f1211480c07d4441e41c3d400001e41c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 638907670 1250 638906420 638906423
    0x4080105063a02040f0c0e0109180e03041d0103060e03160f020109031e0b0a060f0b0f09090a0902030f010c051b0c030303040f0317130b0613110a02010b031605010c 72
    0x35a40000b0400688903806040e8000a55080200d100f005c2d131103005000b0013a4120365810005103ca0804c14074172070319021460f000400d00081440180c00f40d580d07140d0b1186a110b11140d074410703c04150f56000800c0b009060b24811401071204078072044549550f402785048c400003a1000f44001e00004900c2c2da50200000d10606282440316601c6d240e840031a0500340040c024440080c17159000c11903015851980032a0521041080a0804507441c0701c0000b1402000d508103070001d1215441c080e60025142d007008000c12a000c1850f01030200000b8100840e0b049010744507030840e1114880060041840001080c4d5a8908200b100c1282c0000c085000c000c00007580680400040141c0301400110701c01c4d806440310710083c48082c50b008101c0a0300d80c42d000e030f9901c21001070100f070401c0c072542d002609030002d0300c0d4466911440c0005450700810012007084901d003c55840d00c095480c005002c09110a40082000070055414142c0360760440464900c0c00c101030006002c998010342c090010035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 638908920 1250 638907670 638907769
    0x503030f0327030306030f010e071205151f050105091005130b04090c082d0a1b020a02030705030c090402101106070c0618051e0c0607080408010506 65
    0x8a002c1540705070340b20301c1503003030302c1968100104200b180c0c18100402d082404203c00200880b142d40c00381140ca508880c040c503c0d00c0ca00303e482200a00108122282411a04080d44041800d22b980d04a1b0600c150714102054410343c0140000e00b50301510a540ea2244041d00c600740f204510038003110f091380112034000c48020400c60103e00c07052604091300c09404031000c001002c40c96084042c1401000404000b402d03442892100550403130f851451004242e0341c210388446071108070282020340703207590111640603003460032080030a0340043c1c0e034220030b4002d50584101685034024151191580e00d0142d41010b01000445c0c01030512054003100401540340c00c0010000f5030305044d04044082d5405000120070a44603424850a8412184080300d0300c1c243c405844015070f0313042c0c4c40303d07541080318222031203044107808402d40034403410300180e200800d455034035111403602071f41c150024000d0008642c031b82800200346040104039031300303084021000301084081d00703507020ba0020300038005030826 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 638910170 1250 638908920 638908951
    0xf06070e060c0318012604020405060603040305040b030601050d14071107060c030e06090904032c010c060c021c0518030601060c0215040e0a050124050414060708040803030f100503030f03 82
    0x1900482ca007004c040400d0003c40306d241800c0c0100020b40710060325a034030509042050000007a0010308490880b006804c5a030344030344d40c400040e80e05000e07084903070600c0ca0401004503504414248032074800c5403213803110790014821008d0a42d460340f071409490301051504280078086801200000540c04004007164500210308020500d19402540c0031000b04040d8183c072604050003802d22501515140b40818481c28418002081503411201c003074401a40d1b0401040f50600c2446040d01c00c4100f001c04000302d071006c1d0802000c41d8401014881000c4020700741040307900e00420328504949480d9030305140380348590200549072409444040800c0d004210004090b060007882c0c0703118645c3c101c80007520350316103805c400000400900403074071000040c200f04192a000b005072815641c02141440504407220041000340c403501c14050100500402c0005582c8000401588901811040c000c40d684500b00d00d40d0b4400007030701403a981034000348020b803480c403c0040950340c05403038040a600d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 638911420 1250 638910170 638910197
    0x2107090c030c032d151e060c03053108061008070b0901050c03040f24050a0914041409031b06010e0c0322030201060302210604060218030f06070e060c031801 69
    0xc1c5d005841d440034405c140c840000c03041000341040440c0007440e41c0c2c00c15500e41c1749603580041043c032580380c07040100d44100e0403c100203240300c040c100014540c016042c00c0b003611000e1840d520302c411107008250040503030000c00ea003000401d5081c2100c505a8081d41000038000c0152007641040c04c04404910041c40f0000d91403c49480c120300400740e6010905000e5501183d00c818006121a20f1091050810224507055806421141240d080109452030151204002800340110800200d0311030401c10520041b80c001000412260148101285100c1000590b19858210900c203d0a01d450190002a0501c100c44015544281c10007000c225200310070710491003017503c580f01600147c0d9603500a00850400d07010000800084061050344402d051200306c3d42c1c1c080040000b0000ea40202741030110700d460b000300011405c402401d0343c030340c4200c40c02d4155580d00100d850900203026100644103500303001044824104038800614070b040c180000c4020302100360141281000702100007482e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 638912670 1250 638911420 638911451
    0x1020303131e080307030f0218041d03071406090604170702041407110c06030114010e0d06090b1b07080702190510020f0f0f07052107090c030c032d 65
    0x111244280fa80c0d43e220f003420a4001c00302c038140602482c0d950b01c1000031aa000c04c4c00641404030f84004c80c1c0110300c160028903208204040e1030300084007444082172000c02c201200301005115010801280c1807955030101da075030346202c20740f0050003800e280340c140490659100020400b5500182c408102101400721550801d50200e6052000030510300062070140b00a00c11420403c401b01c42e001d08650604642c18040c40780d842000b81480400703a803000301c0d80c9030042401c0c00243c00c05400c1021450b40d00b0500307415001101c40380c45154034014082c11486410081e2541075811400c00b44c107004041d0f0074841c0e8069107201a00e2070791800f00002500350340e6800c1450408001c0d6010304110b140c0c9104052404274200d0700380855070040590300c440f0160004605003207540031100f060380302140781003207460101d039045044258001c003000803d0414154001440395800e40d0380c200b01c02028104110126a1860703d80c900e01c40f46108a03c42006100c0451189079051810000d1501400000c80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 638913920 1250 638912670 638912723
    0xf1003020a03140c010c030807050c10050103030e03060106030504031b020102030c0607020c04061d04081b0a050d1413091d03040806010e010f031505131a041103010b0102030313 78
    0x40303034002c4a0401c450030043c028045450308400a00b000941d4030803540e00603210b200010b0a01040182c040381000100c40100440503030b80100c11010032007540c49040c0184030a8134210402d01030311580d0000619280b1904c6594840e0b901507440e1003441c103200000407950040d009069045100520200c0a00301d803d01149009921a40007080300841890622094401c1a40304404a58401c00341d002c00b101e0110f42c51390300c1136015035001e9980b054941041c62030500c00880a138544152841e010800000084910340400c123a04e66061110007440d15041c04c4c40303100b015004440c2c41c950100103140e00c1b070b002038505072806122800d0525281c010b11b07207140c0060380000c00984c00320004010020b400400300b8090410f0506c00b4118600710f0303d0b1441c1a200e90f0588185155907000000c83d02d0340c4085035848102ea108001d280b0b204081c5c0058000300c0d005440a0381c2d1500100f032035902610741485595000c02d810f8020714107590341c6a844141c00320940d00d0586030362001c03d240024010030140c21 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 638915170 1250 638913920 638913923
    0xf161206060302061c0c0c17130b0703110c0a031e0201030204090e0601140105090904120c0606152c042708030403120614090a0f1d1606080f1003020a03 67
    0x6007171701a615055a800351000d04c2d254006100322005640042407a041000c241c623090ba203401583c8807040c0d0041150103141d50711545202d54046a1003041592102420046400180813244900381100c10807800d589070307100081450f0702c4845141001c0610b001c80440700c2e03005040c018207166940e07954500750381d81e0b090244165040744c4014007002d189000d6480c240c0c80207103019070410360744a01141d24100054005000034003001281001c2600c40c1d2948600180e00100a222079651254084c17541c400002411020a8014078218101800008410031103414200740005032248007092000070301040c0e00380f0021041c00000c2d601c2514440d110341800ca4800c4030301e00c0e600e103020308005195614001c02040380c04d09102c0100414000700c5c40c000d080b050115104070700741e10380340702500040015403a01e1503242d08120760703d401d0f00300812000c911800c2400c1a20300446803a298440744513071a0240d030011a8044011607070f01103100d1001c42e0302495401181e050301d503d0743c00041da6144152f00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 638916420 1250 638915170 638915197
    0xf2105070e180105010801031403040b18242a070f030309120503030115030902091f0501050c0709050405070f15030e0a1709040b0a03140f16120606030206 68
    0x8498014100744521140c0c420344402d40c66242d5060200090403084103100240c2038000441d20300384188018000c40d8000e01000d00c1e400d0b0350f03040c0602c0d0441300e0610400b00350b10420b2004003104583c0b40031488a401c03c00d6408000b45445040f07440c1b5640c425001c143c007500c00c007c00000d03102d400c0342007103044091b00a4041105081d8550300d0002d0200b5041c0d0058040d0120300001400000c5001080d2415201100c5d290b07a07407280c0c400e0085004045902001c2d6018415009010300b41026601043d800700b20500907855894550006540301e22a0244008103540506000c11104045520807900140300d1020780390600d50f01c41c001c0b01189141d40010312090311400080d40070756014030582000c5903c100240ca20391000392109800a881e0000340c680c000e0000a82a0865450f90301410300140c004003500c0364180c581c10180894000c51182c47c040344503070b00f4001d5050b60300040c107010420201005090701c5003080e08211a1111200701141c1c051346410010005030394280180003151f282d0350 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 638917670 1250 638916420 638916437
    0x503040b04141c0f0812040c170118111c08090108060103290a0812040e07080402030a08071505150f0406060e3d020601050109060f210507 61
    0x1401d000041032480b503058030410071000480e601c84070702c000200070503400c1441c04d1a40d0b922400c0c85009440f820803508610412002004200030040c2808d60546250303414403c0100000c9a98508030b074541038070090448070064588c400114804440e4400c00700c081e02c500b143c7e1444055005000910300412981c0080203d1556010359100c401290300c55024a020701041c001c0ea401d800714201a599a1180402c508402401680f2400d0900c0014001281103d8030491140054030003504540101c2481c00404000300380c01e64403d40751a4080c1390001c01400140009a580c42c0c500e40c0700220071500242074841000501d4040c1c8140c9104081c040c0c0c500061076000303400c0000264550301030b80d20461908406000c01540a0741805a40740c060711324881032424081da4100c0d015584840241d4001e41d840f0501c060b1541607640e104010860702168441d90302c603c0150781084443c00740400155101d56801c1c111445407034041c1e00040740c0c030b11403400248040d58610644500b2a0b4100200d800c50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 638918920 1250 638917670 638917679
    0x131203020a0b0c1c02090d0c060c050c06030103020303031305010b1908100e06070c05070e040f0b2520060906010f091104051909020a031407081501050c0a0503040b04 73
    0x80b450141e00480345041245081c04081202169132085080d04180d2940818a011203440e00e00c51808a0798001c0d40d103c0095645034001406002c0c01c080441d507a006a045007101170420b01c1c1543e040c0c0754002c001d0f606541e101d0440110101c0941025501076407900203001c8552580301c0d00800c0003c14040100c041c0e401c181d82280741c40c0000f03010004036480c2c00341c1105c80c00000304007075400602501d02210055418100f080c900659a0041e5030459445014441080030101c240f803c820702c100064030079640e41d00c00309580221206003440e444039400d9180e0f0611480794800c407200c0041d852840c000003d5000c1c859150130002c440014007940007000610030803940d110998001e25a441d0140320a1a00c210081c1c00b40c0990300c2050302130080c2d80c240e0540c039030a004403103015001c6540115117515201e00000c015003a4112500424441080455803440c41002c0d5a40315043c114114400a90101d00440c5d55234030003038000305ca0740580003034440024001e10061000f071051020050300c0f40e003003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 638920170 1250 638918920 638918933
    0x804031109090d0c140321181203010b250c06082a1303080d06050a1a07030c02040b06070f050d1b15020d050103061b090b070206131203020a 62
    0xc2c2451580d50701082d02d0380d842981c09080e81d04640e611000d08980a200e95402031326600980c20000808002c03a0390508421140340c02151003902c0a241243e407180484504a86445100d140c0c00d0401c2020001400650b041c00001d01e41d480410740846d20510041e101c045400000d84400c80ea12104000308000c01540704c0c4074035420030704200c621340212901d05a03003144001d00e201d107202c01c51310200ba4624841c6007103a0030f10065810082190361703021850620302c01450396019231403207401012008203140d14503a0344110790440030b03000da518100c056182907034030748154482281d2042d10b43c071a684040d00e60001038001c00b0310030700034161800b03503a240984c01e000e040f100781030801c1100c10b1a9001085840c14001026421070a543d1101c00c400312000301a2250007030000030541403500000c00c00c001544000d00101d00861481d2601c018400211010189880f8003002c0160600007100946044002030100c90140416a1fa2080c1c2d10003400c507034110040d00a030b0160300484602d0042c08072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 638921420 1250 638920170 638920189
    0x6050a0b06030105030a031214180f030a08130c03120c02011106090606060d06050a0f06021b0a050112020d050c0306030f0304031a07110f01020c0c040204050a090203100308040311 79
    0xc089482a05660400e00441d0fa90820b8003809010030412552007480118154042d01901c8003803500504103161103035038070715456048120146644284801120160808816111074a00540d01c25000307880700000300360321512a100a44013014050000000285103810f20009030009484030301d140401e900000d0008005140d52484581280c03003084480880030440301c0e40036404850042d115100030102d00001e290680096401c40011100400d01461a1070b240088440640c02ca036032001080c0513400d2000d42c100580c40c0c02050480d81800a503000340030100c01b0307805c820300c0142486e81d2101791209a900c00d60f180310b01d0503000000d0002070309041c429038503204480c2e030080d1303d071074610b070307a801068080c010781050002d00345404221a14030031000c00c0c5054002c101250001c2c468604c40c83e0007075000a014016511030020350ec009410310f40207840481e1001032081900a24041c84c1901a60000700039604110000c0300c00302c009107540b0040c2018500684045000e4450031040c48503081 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 638922670 1250 638921420 638921441
    0x70e040c0e04060f26190c0305030a03050a0c0509010e0918060f091510050607080403051507020115061209060b030f0106060e0d0b1f0504180c06050403031715060706050a 75
    0x85403124907a90b1a0170003d0492080c0d40c240d19000002c101034104528840c0d40394000812031b000c0050003040701540758100a0182c03412950402201c1503084055415205448005000c04c5180951440a182c00010f099105100e80c4144180300c102d5a1954203000302240c60088504584043c0030703080c0750420162140b01030700102c00f061818081d0311000070100a1040700d109880014040d4104545c0d6000d0300c00440c1e03c181100d8a0741e52000081c0e1044004030751a000562804030541c291201d05110581215011788501ca500040780b003140c0e018003141101503131026100c1c040c514164030700b0850b02036000c42d040b00001e1140d040001c01000000c806075414820031a103417165012400c4015003980203180c0d07185443c1c1551522684da50400090351103030340c1c49450919020121301100c01d9044030f00f84610100c0403a00c1c0c41d0b0506039054020350101070002854112400c4201501490341e541000c604000000000d2081000a0a640c0000c0c41164401c0e00c41c4180007003009039005640010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 638923920 1250 638922670 638922719
    0xf0c0c11030a03081602032701080a022a07170609150c03130c050603070c0c05040216030810030804030804150e0609062a06041208070e040c0e04060f 66
    0x1011a071030007494044c0c050714103803110341044142010745000300b084070f1003060009402e5058144030340c8200c0032506110419404100c14a002403050a004d10072140f4134041d10300302c20aa440105001c2d000d8005c074506003019403241200205128081e0014201e401203450001d21051a00560907820503400090b030a550200c00428010803041820a40b03911508401c00101580c426041103103000b025035201c2500014000240103105502c00036801402d0300903812481405d0351002884202e104922803412803206408008001034450403040390019800c0a01007500307030310b07515003444903800b0340e0040b40c0c48480003908000c3c01051030000000c001c0d0340e0a10a00140e480c04c04580d00d841280c9015106100000ea465041d01074210141a00002c0c03036000b1800c510203290f441c1e550b8105403000c1d203041007035208500c912032142c1c190b42d00c00c10341607549403a1008510140700c043e00c00c0680c2603052040011b004034958039144201401002d118521a03020380c5041040c6021051158101030380b03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 638925170 1250 638923920 638923933
    0xc010207121704030f2709060b040b07110310050915010501020c030d05250510060803160602070809040903180f0501022a0307060c020405061e130f0c0c1103 69
    0x20460002d00c8141e0060301410070104002ca50142250120034403584c0b140004c0191015140c0e044030780103d0700a550703400b03c2c2080001e03102c0240e40e155005901c1001c541200810031840042c102c0034800300c812201408480340d40115410142c00d56004852992607a4459400003c80c0c0c5000c036042801028280060003c0c81d00b8100840d4407410101051000d108000a403a00b2103a20070202425141c03050002c0380b00340101e40b40258a4100054140320b2507070070709502140d81600807045900c490411102c034040400995915000f80d0030140040d40e01010510080d40140c8980c000c501000b80700b40c1d240c400301d85071055038920000d26034100b05211300a1a205200e02e0760005500d0b00d070f0700c180c4495170300c01644191400c07084440910300c080c1c2501908070005000c64108015044181c403c540501c9141c0d00d003028440081c4601c0180c4c4030030b09281d11035001504000e1922240c0f05500340b80841c201d001c3e550010181d400041710030000070020301f1183d041c0084a0810203084504601400c903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 638926420 1250 638925170 638925197
    0x4080609010f1d030d0507020c03010908035a04032105070c0816050a080c0706020a031407050703061a040608010c0c030f1101050a02040512120d0c030b060c01020712 73
    0xb84c3c0c1c021103038524030080c3e03101c010503409070080010000c2410010000c0c041c0c04118074114511341c1040c1c1c1c0074800034010041c5401c445003081e40b844a680b509814112000b040c01802c50121070091340024003035415004400645454000824411402900c1e15075004080e18000d0746c1d461020b46140031130a1038034080c0300c0c07101d50128501c00b02c0f0390440481500c5400c04428840060300c0000c00071b01034811089d803102080b01c0c8402074040015100c3c156203042d5038802090341c44100210000300000d01480302c400300004014050b0034114042d0b4100c0e00d12070f889548070001c640e0340c82c0070015003982003041503040b4a014024040904404030013440b515440c181c001d800c048141d903008060202c0c852029030322a200790088020080c40300000e0049007048402e4100070f622500489019003130b00c0d04100003040c4005508030901028080403450b01c2c60501642001705107580340c1004250719100a0f821554071039001c0e0480f0b40c50b140005941d80c4581c81c041c072103800320100410902052240040c07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 638927670 1250 638926420 638926423
    0xb07020f0d02031b0609040c0f020f01050415090503090d0c080705010215161e0c17090307090b060409090b0703150f0e0a140a050709050307080606060a030204080609010f1d 76
    0x60010200c0c43d8030000c4411358000078a280100440319401524010100014036404241105440c45640a491100706018041402d90740100c5000d00b0510862156049000c865808069124068800e60381459031000008455041d07040059400d840d0548041c80b030448103101071002030100340001c080d40c60003800c159560400003000084441014102081c00f140901c0703c41c3c80c10038200e0700d511031f454007500c006401030705003801c107440c0c0b0009001c00204402c3c6034000c981c0703104401001032a00c603141820b0b0308043d003007240d03045412200601001441e840d260041000e40fa01c80c0080d080c0903d00050010708032002c2030b4607205540e0505004000c07498890740d00da01911400690108642d4509039803e0290003500c98514095011404101807852544e00030350240b0b96554680039130320355401c105540c40d03403107010f0070205400440100389549044030041602c0101030402504281d505c503201410b00004590701500c0ea5110408640c0c111502d1044a204101000441e40845051960303913 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 638928920 1250 638927670 638927683
    0xe010803120c07050106030206130305010b04062d1d04050105070507080f25061a04052707080303010f06030f090c0504090f02060d0902130603051c0302130b07020f0d0203 75
    0x481d18007400095483c1072000c01c1d00a41c01458018080303c0d03071035180000600c10401d05102c140c409507e090240813031460280503d0044075242400c4020f04880050104ca06810080c00030845100c5c0003000074604201c0c4005440010848003041c016250a08055007903030001000103041040400104001511600070307a00500d0103c5500b684a80102c0484411002d036400000280202d4441900c100059904a007507600780c44c441844a03003082905010a803481030b40c00f5400ca0b4910b49030a104101c682d4221032601c250301303049403d01950b90343c90f941584d00c01c0e01710713035507680f8500c4041c001d59404d4003409441c42c0072404204034070040b50700d51035030001c072030b02030035102d01d4403494058184504620385c04e01c040d8005040a64440e000c44a4200909030032074203c1c0100c800c60205402c2500c20f114023000c0345e03000070240c01e28511003a44e00d424811a0308079001031507400d00c0107202060300f10201030080c1c8003080b10103665401c9401089100c2040407031051082d0404803295005131400b040f00d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 638930170 1250 638928920 638928931
    0x18060106080414011d0d090e0a0f020409090b010608010815070e030115171905032d0d0501050f030604110103110c010e031b030c0a121b0c0e01080312 66
    0x71103803580326407402d10703c50004801e502e030f00766080a8080d0400d01440242d107801103026001c45055070320b151b100765089095840b0301c0030100040400910503094640012079101002140103113816183d019041c2245e440900c00d85007044004010300c00c1540156010740500700e03003801086018030480b1306d03003c804e40091528003009582c0300c0c01d003440d44094101420b41c28a40080d0755010f5290702810001c00008214200d0a00c80e29100f074010704a900c40c80c00f491a0001e0185103030528188600b1010381e540d02c0c01c10300501c0b2001030392003c100c20401508444400850106480d45040200b0544000e181c03d001e22a8203d00240000941204202d1038400c90a003408600c0c1d001d02103002140b8000da102460f1a542404600242c50030301100030804040014103444132482d00f502c226680c1c0c050410355980f9035000503c032502140c03491040e20501040f920b4002040007104e0391501e84014210030417101ea042441c810301408071446c2403907001d0030041c0019030828001c81100c1c2806034000e003c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 638931420 1250 638930170 638930177
    0x14090c12030a1d090a0c02010b10020703080a140d02030a0b0907120b030c04020711040c0302190c020a0f08010c030506010e0d08070812010f080c0102030901090608100e180618060106 80
    0x9843c6410314140280101050000744600c58510705030b0010b0000c0c05c000311907030006529080410000f4a4000c16035120340078141d00400ca050304560f0358945981c850020b00307061060000c51103545110010040003d1903011401607268200140c03840e06030f61800040c0c1e845050410200b0180a44c44012040d090585040100350540f000e0042400e0010440b540303a00b05000242c0b4500f400280c440001c141c41c005d0314100407101408000318100d0064080550003a40790203e000211441000301e50b820300e0005114408581d514001012100700f1988040c0d502d944400030064220380500c07815900803030030b0918a0a001000000840c520700d03c03500180045404115a0144980038003038a42040c0c0103000c05945517190049041a04200d11803803985106c0c1c003076590320325440030060b18800c01d41a180d201426017440401e41e0080c0b030040c030640c11500303050000248401c410081601841540c41d880e80304074a030034901d1342403072002000302a0040ba400007601c101c0000280442c11a000c524 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 638932670 1250 638931420 638931437
    0x10e010204032f0310020918131713321c080909090c0307082406010509030a03051327090c150f0809010e060c0d0f14090c12030a 57
    0x20321000602030f5034801d40360984101c011303155510740c45900802003080d0854014002024031700b00c807444218202c1e0f401c2441d0342c1236400400002c1c00c00030201d1070a4840300b4900e04110414803810b4100425900c0b1030010707808034628010003109072100d07800b54032035441d160a65900d1a400700d102c4020814044041b44c4584411006005001007544d2140b40d0081000c00d403420842c050540c3c605d076841c0f520340b1a0284e118005a8500c000910440c2920840b407a413184018007079100b01c0d070590080406041c001c08101ca00f466079018420319034050301c25251903850f8000c103000c903505416a904000700c40030780c80d92113800c19255100c09008201c141a00031500313030a80d14240110000c80d40c040011002601d00205266402c15116800045175030344105140e9544034125090764941204481e540e0010008103d0902d40036000304403807404201c000c5403252035503c0c00320841d44582c038005101407241c424030041d083e044c042018690b03801c40340b1450a490384868681c0305d101351a4000103100802 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 638933920 1250 638932670 638932733
    0x207050f010210150f050d120f11010203180712020901030b04020a120303020a17060108062e05030402150703050f091f26070504060503040c170d02010e01020403 71
    0x700f0201544103e1498180104d80300344401c00b10b540300600411418904a41c0c001c606420302c4260950001e8100440242d6400c1030142650881039810b81e010030030580784003d000c4040d090000b9405001001e5020036411f1010086605000030f5400444a071402448188090381d200c040450540360451a501750580392440040d52203400b176840360b9014100c1500c40030515405502405402109468403140c110203110411108201107800a0101d040718000c1605402d001090b9810b42142c003c40c41c0e0131102640c0c2d1640e503040721207031920010302d0000c20041141002c805200c8621004000340307040c0940d0340d8002d00f490240032107114944c180415902c12943d0749014189690500c1084900e1008502c48000d01da501000c0c91b013940c160000300d03002004c40c00c55150a20994080e0f8800b8141400c0403030440c0d05034005081541d41c00401c190102e0103070150071a04400c0c0c4411402050001c40403070010b800d440d41d0400f6031a03140d20606c0200f01041c007050300f0f1610400900d13081c0d054150704 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 638935170 1250 638933920 638933923
    0x40302251404060f030305030f0709050604060815131a18010e0406090813090513020919060305070b0301031703010e0604090f0b07050c12070f0206160b070906120c0207050f0102 78
    0x144d5001c6000c03032031044000000e25421000444c011b6032091036401d40343d60381150541d10740041e489002d4001d0b50400003009594411842c46820030710380e002441d01e03480c0d1000001c4094108034031008078036565240b46606a0795098000c5e080d510f007035581c103445451029020240350070520400942207038203000602007042c2075202c402c21580c01891680c480398002e010801181d1280511a40c1d24a0140400c42d9032070000b034804030740755004241341403c0d52000c24aa00014020105018140e121800400004c400381b100c4030151a549002a48940c518105002644107003840500d0032441000184859010703001c500764050000e49002c00c1c440038528240004903501c06010b4840c10380c0a040c003418560100040c00070214440841d9012010360040309200d100d0303404018000c8125903503482c01030414901038004d081d19485400c0e1400c8668440790750305101142d000d40007400508050140c190054904c03801c1e4031000e0001c00000c402618044e603290030300d00a446c030803110b50010a600f40c0c070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 638936420 1250 638935170 638935181
    0x10215060d150501031a06010e030619090212100507050304050705010f170709061404140913020306040b0402010801060809030706051506160b15060706090204061d040302251404 78
    0x71030a0b08100941e0340c4d040c0014120413565100720f10040241c046129036100710140446040001c0c09404151601250700c61690700031820300180035103032036280c030141c2e54620b844400740b02594040c1940342ea041d40f00c03000f02c0308018000014000c044c001d0101003100000d004080d00c0b0301382000800503104000c1620420843e920145280c4050030410010740c2c0d01407038201c1204c080391119160302c28500d0f0030403218041c40c000e940b0000920505421035240403e400c46d04120b043d0050020302c410303034001c00e0074110101c43c02e6890f5007000040c0000c55902040060040c038480c81d0501c110b04184031860340b40d100d0301c3e101802080d190408a400da142c0e2081c10003d13114020001c959410107665007001201c144001a12501003000003c2d10906810b1400c0106200007480710f407500b21159284001011003440a13a0010303580c1c4004220b45601c1c014240401170b1308500155949005c0c03400900d0114501d140c070030362411910250400c4000c09041005484402400030b085450180200b4001d04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 638937670 1250 638936420 638936453
    0xf050c04060311090601210506061605030a0e1008130203010e071e090513030507080904110c010f09020f060903010b0a09020c0d0f1e03020715020c0c010215060d 71
    0x10315000d00003041183c00e41204001d50800c0e03130724864a0361070383c0054402030703410340300440011547c50402c1da122035542d0082c1d40c441d60060070242412000075404062699807401242c3c136500016184e207106070031114040c0038842c1201c148114810701e8100400c004400351082070030821000c1114115a4290015884810720304112840b01d0340d502449085c020420640e00a00c40e40f885002c0380804203402403d110395151070114010603803582e421a116446000155074850b01030100180d9039803580600704914508201c61034890202c0601c803421907000381e800099040c6842c080d903006880c0c4812070362140204541e41a29008000301090240250100443e48418041d1022450701c0d25603018084102105040352000f4400c0c1d4130a980d540840d03407810010580000c1c245005041900d0300680b01c400c42d1401504003081c030703a1340c1005602c1082d9600d41031a00849c00c4981e070f900c00c01141c0d400080174401041c15120700d0b0810002d0340005030003240141c2200d80350200f07102c428001d84070b044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 638938920 1250 638937670 638937679
    0x1517150a18061b110d05031b0f04060f110d051b01050f0405010b120c0d210c0b0a020702090c0c120708030412080403051b071e140103060f030f050c 65
    0x308403458410002e0843c0240c8102629042e08211141031140001460180745803004201200c00c2000643d03058100170200520a0003a01306454040a440041d00ba03148100158945a80c2020b8001d03040e9000103080c01e04001d50f0480f10910000001a030302c0c003080f40da05000395100250034200d100e000c3c4c10101116107600349001d00400d04803040319248a14003d000800c101102d5000304188a8400e10704c10005900081d080c0c4190325196050482161080316000191900d000360996040000c038004000f05d100040d1350340500c00ca040d0101c1c1e204000c904118944041980068100d29000e04410090040803c1d40441104104045500001c03410f00e03071520398800e46402a155801294100c0704c41203003100f1150900e000301c203480e0140341d0540325a81000c504105d65118440e1000880c1424801c10b03030000340091031101940c0348001804495030496003003200d030003009511204e045040515100e42004001320400c001400d0300d90004041180552608006242807030f0210500e600 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 638940170 1250 638938920 638938961
    0x20903070b0d0b030303010302010816031b0c031805010c06152d0b0403080a0e181006170403020a030f170c030103031106041221050a1517150a 63
    0x2510707821000e40402c002c0030409000880b0300805241c4c0b240001e2100a01007580100030403100301107200f0345500d08501e4035001031016424002c0035004501101600089a00c241c004e800381984500c40801d1005110340b0003103000d01d000002850302095030005090355544000c2c64121000e801108001003149604100c1901040602800c0c200d9003100c12064040041400143d0800403070155001c0b20b40003602c45082610181c0c0595510442d02d600c158040641800748016081c200249070151241d0400c002c0c40504001d0060240c40c9003ca5000060b05240100b00009900140f203281480d03040c64910584003450320155011001c0050707a002400b40041000b4003c4101005141264080c0d034484a2400303090705459100c3d07505032405001340041c1b0301a0020387c2e02950940842583c803001100380c41d00c5148400c0c044480a0f21000b28840d111140010014101d1a4080c050540783c40e180754000c15140c221581d0301801c0980745001c05150b800a00360003045d6004083c0700c0c26041c1107258 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 638941420 1250 638940170 638940179
    0x111e010b030f07050d0624030809040b0103090b06101b050102120109091505090a05030c010902190b041a0c0109060509070f0b04231305070806090f06040f02090307 72
    0x64615800114040e1040300341c0e0b0700721104001120001c0740d202034003a8007070b207a15448460140014a100d42042c1051400901011400030b84060055001d142401d4843c3d6510041005446510303803d541090b04048000001c0350801e2078141d0055403c80b50080c80038414003082d0f0700b009144c0da004030b030701d180140f088007030140640003016230083c1022660407580c1c90b12402c5044840030345003d4420150040300c410300038180d074803d83e0060f1504013120001c5201d591030302e295a02207003500c411039440392064400c600746405140009249a17100a00f81d44c10107101d202c031805a4450788071240408400c48004689050483e052203400c003000b0b20030b0400c1400c0c0900940010b039400502c2d0b04c2400000920181500c1c0180d007501c4080c4011803a240c9801d8640d40c00448060407401c50500003041c03218a562005014000002c509034081581d2402490140074120003d000500030541801041102401910000e0380300b54110340c0014034a010848040090090603c1c642c0c06100740d010100c1e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 638942670 1250 638941420 638941423
    0x1c0b07090603050106050309210903031303051b01050a12060b0307180b031902030910150f0605070b0402120f0f010b0a08010c1704060902060a0c1401050f0106111e 72
    0x1015074405860911240c0d0b80c585d0115010700c012500303242c0300d070004022412480c0c04540030311854401c803030034035080030b481e2070002c1d00355840515040c2c21501800410410040c052044503209614208541ca00c10b2034207002030028420590341404100303401d28155074960240d808034003e0b0040c9480c190310fa1801800181840445100801403482e217001c0029040034500201d03449600c10f415052600c17015001010b01031f400140000c4540d001d8402150200f480e144244070403540600c943e40d0340503207400c0100b6000704e903c0d00020708002c820400c0401240000040d01d8000c2d074180c560b003c601c1c203035a0304d590401e002d0703141407150703402000d21030040600150419200b5800071290020b01c242c0c1c1c3c142030b81c00c95200300c240e440400e03000b4840c042607260034688298402c0c082e810101d940b4986a0001d50607500215100d80810555200b01c800c2c411484402c12204034500020060390501d40c8501200c04014410601000794060303e84000380360601821078601d010810000c1c1000c001d89a15 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 638943920 1250 638942670 638942687
    0x1091a06040f0506010203190e03030c071809020f0603090f0607051327020c0703080f07060b012f0f010f091e030504180e030310170115051c0b07 64
    0x9116a091280718040c00d829807150740d0250b44c2c141c00442c40c2c00103107440c0546141103a11020140300d844901d0703200c2034509000404038a003031f620260064905140000e0229894041c1d610079a61803d0a6000140c44442c412407444808649454990303031005070003850102600d86094a0b4055841840706458000c0080d00b00c0c40103001400100c1d0391a860384401030f49040240720407404d0204610000ca9a41c0d070700415003020302005440e0b0003616625000c4103035001c41d40c3c0c0050300200192810502603039115100f0745c03050905e01145020341754a03d0740a03041c0520800c114520300c1d0101c0310765640003004a62070b000110802800901261400b0307000070702c2c4070281902e0b690144401c00d40c00c2c0410b0740b401c2c540e181e850b2b100c01e41801c1c200180c090030190a0308001030713440d980380c8044482d180c2c1080698416041031501c03500c25420004580d0100b880d0081e06001603040140620580041c0400c0505440003994034110744040703500c0900307940115501c0501010340300814048085c2c0d00c482c29 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 638945170 1250 638943920 638943931
    0x403050d0605130515010201020c191a09030a021902132d020c0706030209030303070807090e04080a0f090b070201050904060308030405150c0915071412090109092c01091a 75
    0x3480740040b10f1700160f00740c0c030856080c2e483d103400c1315405c008414a088581c01d8564010200e0340c0183c1882203804000340001d0380d003116240e0000c595070b1241a81003000c40e900644031402e201c6455001d5004c039004481d8841441c032810b17100c86031442501a105001c00085065010314a0916203a05200f4000d52056441c00054002e80d800495000c2c000d0080b2401c00101038021451907941030710407208001c010f801501041100d14000400f00e800c0d50150340164080c911541d5103400c1d5070406069a54280c600005114209804021542d080c4095980c101d0302804c0a940d07501d100400140100010b4100501d0703030101100f800140300000800844400b18943e446d0955203c02c40b80680030700a0384152a0303c40380c00464030300140d0b5502c000c0c00c41a0302c1015000e441400707075a111420101d120081b40314482000c103144c0c4007980c0c0040042e00426500700100144495070103202091800b440c1032a4420b05840300030a1524002d40c00800c00940141c525076a8040e5491301000c04401a0382 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 638946420 1250 638945170 638945191
    0x1e09070509031015150c060c1d0a0501050a0f2006090709140a180f060b0a0e2a0c0d050d0617150c0d05090309190b030403050d06051305 60
    0x354a5510f19080c4a01c211090a01ca800e0400f41d2504506014032001031115404000700741032508002106402249004046070b198045540000c03040c100300202c1d6880c490740704440340c150820890340c0210485403908254640355490f20500e6200b0f0b10312212845590f840307a0940300d07154140003804500503008540d080240c0328031039580d0b025201565070742d6a00419202c0c1c83d8011601001207944a00c10f01324072801c021041d02c0d0f8644542c0d4021b060a241500c3c151b886020f400d01600c0c024030740320080c004105d142011401c120306085020b488002c042542c02c0c0080c0f1100c0710100c0c0d804180e54000f4005d00850309020000c10b0b00034000d40101d20b2003100030303040480100d400c80c0480748100e0524130040003801860b940440d02c800303c0c60080c09546643c0020001e5118403046400b8091245584d400210b654a10740d40c24021000030480301003000c0010401c2c140f02c1081143d046a0700181c061800380e480e40598050840100100c3e88025400485884030b091002072070340140b44600000320 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 638947670 1250 638946420 638946433
    0x9080d14010608150105090a03021809101a0906300c04020403030516080d09031119051507031512120905031e0106030507062a030c021e0907050903 65
    0x110700f034031000c900740c8400e5030400c641000004c02d07521402c007820f914440100a1282560303243c0101d0100d10b0040140c42e5000150f80400c14a4142042018840c0030005400c000f0a030380380b4114540c242501d09118401c43d54003001c580159100c03642902c1641e00003e190f003040c0c01d170740b619541860900607840902e0046100c2c0c4080c0703203002c0c07007a2012260141c40c0c140c0b8203004204c00c24042c4203500b80c1201c454105020940d181042407103822600c2c1d10a441d0006078007005d0403820300d08020000348030311801c40003000400054001c111149403086d038903e001c0d01500c440d0360a8015045942147d203c000c0c0d414070024644c654400e400c80654040c034504001b007500700100b1203110761a801999015400444900350346c50010309030800f04035105c40001681d030340b681d5a80d414414154401b0000500079208407100a40365203c60181100c2003144032000b840c00d84d80a000c0101e11003029100d0212501d62008840c02c455001e0002040106052040e00d01080050300c641c1140445078001e00c41c1c40b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 638948920 1250 638947670 638947679
    0x1022a1212030f01081203041103100f0b09010f03170309030c06040f021003090c0611010207080403030c0b1003020102060601200f1c080114150d090305030a05070c02010c0209070309080d1401 84
    0x1b10320349246070320550f2503618581d11925000845030710700018030b0b058440c0c001003a070f14a115120741c00c005083d001c40070804005640410803071a80c180c20804210740d0840c0d0800018542040504107001c6c810316050303c0b55150219035045010f00050800c0c540a5203080208200740590b040d400e4510807100701003110b5025404504440c1c1d011300003020013803100ca05010180c0110080402d001240c2c00152030121680d40700000d03a04640e01c100c000c2000240000c0400c441019425070041c000015030200c0e5140d500002c0d0307100380c0a0402814025511071400000780300500591a41a413842200c100420b01d46406541320400700000040122040c503040d4020710a40c661230403a0180a50518109001820042c60091400d40044a02d03020407030038100144502032070409a000b900c440c1e0b268a800d000800c1079540c018403200400054003080c40040c2e0308014024040764064030b01c20125070300c034841034005041d00480035014070008551f65151381e4941e00000d00441880c40d48030100d036070300e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 638950170 1250 638948920 638948923
    0xc0302070209040b060d05012a020312040204020304020105040504090c080c0402161203020705100b2707080408040518040c0f06020304030311030d0906020c060601022a1212030f0108 80
    0xe04400039400403000012801250902000c250410780060003045244030315940c10342102d502c040b00710710000400001844d07030449081c0c0d01c1c4504a250000d50720f00040c4a42d510135001c40200700a11590307012001c282503920981c15100903000241040241c03800702e0a21448a0b001482403e45900c14800300c060f060030140296002a58a00c4116407207072496540da00c0214101a180000c05a09018510201d20200b05401141d20180000146400d24505020001600d403c0511460b160410414900c0c040c0ca50941c0e0311030380d50310308014551524540f041c82445142d0110b0351000c68045107504a51040c11098096480341c9202c1300030640c1c40c1c0b075098100449100b03607805608144000c2001c01d0141010704052080442903a20300040d0a94100407103000303c000340e4000d58046a0b20604100800050b03400500c01d00080c20203040303011190b001c01c0505000c41c0c401a4948000302e42c2603c906514010800b2003d06580c440d0214912041154000f100c1c5212903204590000601280 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 638951420 1250 638950170 638950177
    0x9020d020d151a093d0504030305040b13030c08030d0f1526011e2d0c030b090f040506011203050304030c0f0c0e0703060501050f192102030a0c0302 65
    0xf16511031410800701683c16002c039410900712103412800881c0100e12500145600c83c0402d08400328112859083d04040320700303985648881030a2050070402480448d400030103407003c450f0b20b4980144d0b10f03120360304240c2070b20000780e000821101031301c40c01045000010001d41000c01e05101c0412121603111a500c0039510a00342e11030300109694401d000f030362501801c0007003040071481a1564a881941f070682100c000714056080702800e254000d140450768001c000d00d00c0081030300b900801c03020769444002400d0002410b20f110743e9902070610241d0203508041c00c0800000e01c02682d52a0401c40c1c40c90b0381c5030440d421100c41c0203110000c00c100b243c200c210416103030940c0d40d80b41565210340d000e40c0d410030048000c1d28880e22611107140060388a400b0346026068004982000c0e0400e100c01070240c0700315130809818813605100c10020701103031328181c84460044030740c204c515100d03091050b204100c00e01404861b040d00100e0501d04910b281c0c0065000380010030b4100b080b02003080e4114101d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 638952670 1250 638951420 638951429
    0xd0506060f061213030512070305150d02011d0d051606020d1d040b1c151802033f07020a0504090b0a0e031603020105060a0f0b07061509020d020d15 65
    0x108444c004103514015019100c0e0401a280c0306e210440c140024070111840c20001ea214000c100c0c07060310402d0341030702c0740c41c003594414040c1d08264001380c25081201200ca07038078488640c07000c203e5070f40c4000d4090410382007003d40b11500c0f00f02c0300c541c00c0b600140c092600948128a244243c1c1441a07c0c160080a940030300030101080c07880c00c00001e4004004000e6101080c039814821140c1c2c44000303800070394030420a20203c01c0050203200151980001c0542101200d580d010001d42c8000c14580c6802051041c3d004008120000c00c006c1718071201041171a440501d040031410005900040c56518003c4030360201c0d040d5940104000d0341c8203030b13034014110442c4201164801c02c040c1c00030710014403481c09481c20010110301d00700805124103410350050b03441d8420701c4202e0921004050183c10324004240640d42410100041803141c4c2da0000d00c03a43d502c01d150826205504040c80242038004810f40d40d4080202070640650001c40068800320314150300645400d1a2001c6400ac03203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 638953920 1250 638952670 638952697
    0x31b0b03040c18151d0108160608060301270c091104060e01110607050d0f050f041b0506040e0a05070e010207230a0f0608010602030313020d0206090d0506060f06 71
    0x242007400304801c281681922858654581d24608004044480d84c4800341240d0402c03006a030790840303130f020300040040c0c0c411344040d0409011210190010300310001621054101844c0079119100400d005000359406c41c0d41d425440d031000e000c003100d00c02403004018010228004050f88400e141d00840702d041c0c0c0c401e062900d042008000883c0101031406084005061000b1101150302c1034a062080840f114070001c0c02c0004e48072340d0310b610740c40740003e035005a41003008203140c1801c046280c05000741020700000078646581e000400f0904064014001c003405050300d0350341d5110303d01c00700c0e001503d0004841d0704120000d1161885440a00181481680140340f91450f01c200080e044154044e242040c0b10003408040d45500c5840e1103400901d050081c02890034540368000700042010781040c421500f00300144491006500164003000b501110708500c1a045480010441e200b40d4400c0c54000084249100a000d00030528500c0b582d4281c80104007207440900300000d5104408041e40707107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 638955170 1250 638953920 638953943
    0x504050a0b1e1303031401060509130509030901030b130603030314070f080402010f09080106030f0b0601090b070204020a050d0504060516051218070b0c0703031704021003050601020115031b0b0304 86
    0x3020035111603c80d0aa0081c140044c000701e00c528960300ba01000d0b044600462800518080241032440c440318078041001c00c00c000500701216225220311419400e02d04154a800b0115050b980e00c501084101c109804108012656854091301500d0030b4900302404240c00000500458010f9100050800c8503982d00d0500ea079031a4010764860000391642c0c410448003e6000c220364500740300c0d1a01840c00784150441c0c800b69454000680d01c2c1c020030003410000503100c03c02032803141e1000e854080350b0444016030ac0c0d2010390011540f0b4000d502c130903602c860a040c00d00c420300100350301450286200f4400702000795903480040d200c1e07216035030501350300c02c00c1d20300025000b0a5030b103500c00038000c89405a9841d0b5580b0954210580c100d00010a03043c0c200d90810000c142d0014603000c11440c2181c00700d00d080c40c0075000204102c4031071028005142d00c3d070000a034035038401e51141080000d051f018001503a102e0900003036030840804020183d49104002041903186082a02c0c441d5130702420a050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 638956420 1250 638955170 638955181
    0xa0f021c08070b10050d0b060a14011d1818010b030c10080a0b031f0b0901060504030201180f14040b120c0d170301090209041803021018060504050a0b1e 67
    0x15000180265444c41a10b00045621799038082c40548850040b54680c13070509042c800c100300303a140c42d80004400031420101900e81d0348c01c0340300c010401c48409503e209160011001c9062642c1040207a91200d4462080203004901400c45000b0004804020420284d0303400a240d9105150741600e0781c414401818004464440c01c103c0c1c0c0d00611203007010440503241e0002c80c0c03500322900e10151005102500e50242095903108200c2d0b0140115603046c059494010041c1842c0715500002e4108211900d10081c2601c251701100d006181c10f102c0d458001d940d88403240c1865a15981d003034032413400c0c00000e100030b2518040c0b5a11950b1100c000d80351a01c0180100000c011160500b11030444408002150240441c0301560003040070303003c003580e00d00e20701e030070002143d40c4801c1c0600541914207520001c26800154484144c03454800025200301090880080c4603800000901550034501000708000c0c1c0800e040440d54400d2a107441140c480c1810b100c0e511055003600c06002090100161 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 638957670 1250 638956420 638956433
    0xf1209110f0a050310050612060c1e09030f010e01110403020603011707090f1a180c0f07050a0c030506010b040b0a050318030c0a0309060507031205040204020c0a0f021c0807 76
    0x594888000c082d40022580d8802003424180030006020849039034004101d51810b180445100c01070f417a2010f0030741032a0107038150419005e04031016007000074450720300240d00008030445190000040c2164210390039000c2d100c0c0a480300300c0c411451035081078a1400300c64261000c0e9402c2d2a402880181541c1c04c004802c420100c0410a200852041000009030b40082d441102072111120001041440140541540c0114507829160141c50306031148036110000000090f0041d2030300d0f034030340d030784c0c2c4007441c0c11040034026107001502d54003030200180200a425041d8404a900c101d00f40d5815030f13a03a2941d4495409584a0b0308c131690070420040e40450311a41c015a80a02811007500d00390701b000c0c0400d4559003102e0401c40c200e40c0421245401e00d50031404030401441c2928049190400a650051222100e07c0d00800202d4807440841d085554036010703a202c01c120300d003c171400260181010340c0107540c2c0c814180d001d1554510300b8510101e03418a14400c154105002c540392851694450707 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 638958920 1250 638957670 638957689
    0x90f150201060b12090c09071d030f0f061f15080603031314150903190f05010e250501051804060305030c0a021201060806011203050f0a0f120911 64
    0x10119540c03458045800c180c43d40107461480d0088a01010038580407070014075145110919620500144081240b03031940702000c407402d041c810703135400c0d55080b400c004285000c048400d078419034082d000361041900c00000b4594415403180708101c600d01240e0720000b00f848640d02542e03070464501c0c5020008d040c02400903507042400501241e10f41419040b500c0700c0e01c8280d410042e2071510380700e00303844ca40ca0461040f03900c041070740340d07001e20303101071034002a64403004842d03c0c0018550307482148003400031202c103951000350001d000344404044102c900d611000320860515102c1610307503800400d00303800300c0e06c00c0c20303548183c482c2480d02400c1b16840900083c003100c0c19900a8444d440800003d100f0f0019202e00c2030000c0c01800d0b02801403042041a40803060700f00d103580e25200c2c0030809010001001c604403a2049044481c1085604044859102e010301c196009900003d01000d00381d48503640c1c50300c5144c0e40c1d4a0520a075082c4103810196410000090150318241034a5065450710308207030b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 638960170 1250 638958920 638958959
    0x909141314070b0a0e03062701020d02030c1b0604020901091d1b01090b07020a05041d0d020601032312030601020705040f02030601031d031c0b0909070f06090f 70
    0x201c20811004581441c0703090982c1d0041c1c038543c4030110b4504446504511840300c141c03411006400305280808454445080c682c0380b17012528840030b2164258942136040359a43c200520080d0b5403490407004014256008030309120a00544c00340c1800e0041c07000c174003140907035402880100140d18005901012701041060f03401c19510004107120b014904201845408000d41c1114100b42c02c10780026000c10b00603403040b07070505c4c3c04208040040c1c0c0c4140d4900c0030758008540018203902d82c1c41c009511807101d0000d1411a1049a00584090350000b442e0f178103c034455001c010100c43d188600c0c55110441501140c0940d0091025a0300d8681000c0030703640c08a41841160b0a03a9640c000140988142e82c4c4034500c115400418442213581c94021503407202e00900c030440b403c45541103000c1e940c1c8503d00391002015568003140e00088900c0d009a0f002c020020224540341c206007182d5919020b66205114920101003c0001c0f4140601001802c60740b00c10198030003130345040090380c0e84601071100f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 638961420 1250 638960170 638960183
    0x72f0a03031223130303060920070302120f040302090a090308040609110a0611010f1506140d1a1306260102070b180f03030f0403390309091413 63
    0x3c00e484654804450b203849401181240410901c050801608445c1d0507001004102e040840d9890140c400342c200404240d008040282e407a8914141242042003002c8403511092000a10715070107103030f200151094038000ca44a1000e6200e01c45810708907120900001e002c60400340005021034055480b5403c01805050081c1d003000e0fa050000f102400701d904001c0c0424901d200f0001620f0003486421820f10548030200314041d06810940d8802800d03120b04810070591180401c044100701081e22140043c8020a01c124181141c03c2490308812000c280d00640d00104c00b041054910b014a200310360031002644070f100d510180c24840310001140d001408e40d0200003c1c0d00003140007001034410002c040c008444000e003640c1241c140581d40700c401099500c2402440003800309010804d400c280e140c20803418038125000210500b91103503814032010013401041c0c081d08805401c0805001f403080c1d8658507110380f02c207028003c40c2c6a28407581c51442c100400034444600080082c00903500035007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 638962670 1250 638961420 638961461
    0x90a020304050703060c030204031b060804120c0f0308040302152202010c0506070903020a090218040c0c0b0408091302030103050309060307020f0d0f1e0804080f072f0a030312 77
    0x5c490b081515106845100000d500040400034415070300c88214455048010100900d4075100005011100150001e01174085a00010b40c2c4d00d8000c0c00c0761041c0903031191034080001c10508000d0604c100c12038055002d402000d00c031030011201c00d42841d100d080c5100b403014000400c803065803412140b00b1001c90510040d41c0c2d8000c0440d10402c0030324400c0c2c42907034403031000604500c140803106501d503000140e150300500812600c112071800b0315048440a0b40d000a42c40c00c44403085440742c4d0325020140418442d081403206004003030005000500055440043c0c1ca4a00c2c4500320881c4000d05c80909660000d0000b1081c40c42d0020065401215a00c11203400c4c072003003912223040000c0181c8280c00328008000c0007042682040803d0b2a44608504c3c6507201c030300d40d1801808040d8002c100402c01480040d01c90060752080080d592001d40002c004460040100100020310400c103c0d10280120504c8058055240c000d20f24030640ba459600c5119000b5150f048402500c0e061a00f00030040680c0e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 638963920 1250 638962670 638962673
    0xa030f0609140607090303030e1e01051023091018060503010b01090b04031119080f0105060a081c1206120c08010203011a03100302040f0902090a150b0c0304260d02070302090a020304050703 83
    0x48ac25200e580c40594000075041c200640710b503a00301d4282e40542c240ba40b0300c805c001c43c0541130400e4020b04a0098915601540e190b01c440c1501845030741054100c001060610700160055510200a41c1c405500030414000240015141400b01e8425032000940800003880003d6511500440090001d4920100601c640242150104247e0440c00041e481580d4416a454090182e5500507209540c0c044c001810f014044e80c862804031010b0008000c2855080c103070501c5045030118903803c18038200990303610349510107004448041c041c2e655076003c040216242d00180f081702d0407920141640000210003003510b4031117800081540c0c104415801001015858078040c8440071007411300700242ca2140c0d403040100f1141d000e080c007203040c3d14251180804139240300002c000e403103401840548070005001e07441d03e103101e160400c000103101d5602040418800e0001d003441240c4083c00e461000c031001e102240e07180070500c03000e940107a081010890012040d0700558101c4c1c010310a542c03040c0e840703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 638965170 1250 638963920 638963953
    0x803040303020a03032409050403110105130212060c0910090801021206010315060203040501030921180b09010c0f1a24010201020c0309040b0a030f0609140607090303030e 75
    0x1940c02a03001d60441c000e054101070307041c4180340c0f0601526103403400041c04e5640d4030b12032104600882e142c66a40c1c001244c10f043c018803d200c840280c0d600203200e07614000051864400c120340089001c0e130078840a009003800c020504621850200420500740654402000244040300029800b0701c100d2880116a00c034080c00100102000040032000300c1c28642c00042c1141c40b6400c600c13550307041c010710a000700e42d400310403107044401c24640400c2202075420080c07080680b040680480052840e03c80121542100c00a4000b1650000c1301c00d100340c1e911641001486401401e500250340b4144c1360303000030072f036100782e1441901a24800008802091101940402c16207004040c800784a42036501c400c072a00300c0c541c02c0708007803009500b4140d001c07546640d03034051020b42d03374403e03620b4003c00e12a60300d03203c0c3c0c0c0704000c64000c0c800070940c01444c10101c0060205080980b0070384824448004580d01c0020711a019030301c0c644d44e02034101e00d1270f2401c070300508200c20300c03815034007a002c6251110500f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 638966420 1250 638965170 638965177
    0x1418011b12110102120f19051005041803020c210d08040507060e06030a020d0b030307060b0415050d0209040302120406030b04050a05010501080f19110c0c150708130803 74
    0x424468000e07240051500680320070300e0b0411144a90b0f0040007103a42c1010411503560304007a00280300105e50711030091580718002c200b245006520302e484200118005180465021030b1000d4404229100c0e850180e00945200001c0140140e40046440c03030b80c80c200101405000b4118004001000c00b10301600760038400c032040b504001403145018441400800d200c003000802d034034140345001c0310200340441c60b1808000d0144081a50225101101071900e8000c81c2d4034007130040942c3e0341d41d509480d2a6005082e002101401140740091204000b0309468031501501c600070800e8240000315401c211451500134011000c5010301d0407100c15200e950301c0504090a025100807503004103075802d10080f10802410380e0806030030840104041d0341c21011907074208080590152559440e03100b10f1901c03082d02d001e020f40e510325160780a40360440000c041e0a01007286005d03a184402d0180030840801501104610310308020000d4070f002503006401049040381c40c00c001020700b543d84001506640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 638967670 1250 638966420 638966423
    0x30a0c0302011e0b0907030501081908040e0f10080a020105090405090c04150314011b0c110607080306030d020a02011409010311210a090f02010f0c0212011b1418011b 73
    0x2c1c0c0310301c1c0340300203480c084e501e17158000468501048550b04d026050390b650200030607800f40d1411302220078402e00c0210003c44010780200003005c180ad040c040c1c2ca00000460845954407020a94000400c032010007185071101c40380c05039078a034101043c0d1b5003004000c0002a240081c40d1244440600c266141e40c051680d8401ea241c9050442c00d145040949103880032807501c2c1d0540c0d15111281c018440c443d00e00c007042000038a00303000e10318044d1401c80800d002001100e82d01c5400410b460003080941c0006500c03401d000c0c0d0640e10301100248082c3c2e40d80c0c41c60751001740890100340300c28a1804000d13020f04002c4505140115810a1105280c140c0d82d01140111703242c00718440350413034030004804445420680c002000c02c9450010f0311034144a254900000741000718401813a81d030107110b2082d444200d90000e0051090082484255000384101144081801c881c2d201c442203060062540c84651100d5210300340c5004c404003a11007501c49202c01160510000c0986245505803400c0e003008007a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 638968920 1250 638967670 638967731
    0x60621060906091204050d1217010e010302130e0c040218090c0c0d0906050930012a080402040914060a02180d030507060e0f0f0106091d030a0c030201 66
    0x504081c00032a05040c1504411552410200170401107500e6862200190a8003e00214480d4690540840b824440461000514000200080348d68514000c00d581201c4c401c690b9401002103245260098446401c64200960404100820182803940050494500490740100c1407010503000070007010090354403140404001c0707400904044208050b2171403800c9828986844c1d40390440081c0b052168007649801540750f00454446c440031034104401d1603800035452800c05051a42050081c0050588282c407458451800803103072a01c0310700c2001c140d01660b185061582d59809002c080c1044d007408450b4080500019a0b10341d00c18800d0038020040d003140566a1490031041d8007405000190136403089030a245030000003900070003280c8425500c2800401d6601e00e01240e1400c009862400d5410760049058010302c2d100306510240a8401c2a10f0130420782e070000c4800d034092011b44d42c40d11020751003000100d00050040d100105407502c00c0c4000f1607100c0c80514030017071103159400030541d007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 638970170 1250 638968920 638968933
    0x18070c11040903270b1e07060908030a0c0302090604120f060c05040f05040b0f040e0a0b0709080f0c010f05070807020a120501140603061b0c010507210b01020606210609 74
    0x18640c4085641001e42e01d075031034076045003410030510083c400c1200b074120300d641c4100186045891b2106442c100d40d0080c100704410700d95401c1c081c0b00c1e42c0c802c5a2150b01d40d49041180c20496010f842651802c180c05001242803d081800180781c46c4550f03e0296003103503031080e90000107004c50141141c0c2418559600e0b80b245d01d0178801c00200d02ca181c03c824482d504002c0d214180781c8410302c82021401e400c4a010a0409414451138140100458090414108034040040305c80c2c0091000c0f0440d91038800b11364092010100e41903c80040e078941d60b000032041c00c900c0205a12a001a00600d4028540b01b4a84109a400503e080c1c116600c04c58201510340ca00500b804000c1c418800c1c4404440135070941451b080e40000d840d00b80041a040000140c071404404101030401070382d040036840c800821280c14584000b4003003512500851840422440500500105901840860000c180c00407c0241c0b10502080b0524440e0781c90803c0d0103010010303404030400200025402480380c43c000d04003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 638971420 1250 638970170 638970197
    0x60118081c11010b0d06050618090d170f2a0d0b0a0b07030c0210020a082a03040602030724020a090608010f0806040f0201020a0b0907050f18070c11040903 68
    0xc4140b00340000d240e074908420824652141121150003542c060700014596031120009121a212030000d582141c0e04481001842a000a2440d03c0042c00703494104546107003c900041c441c00440f0308402901701e42d000301d00c6c9000065503912007c0c10807500c15420381814044171080d90824070303852141e180c0f151100005400c09850707a10281c01400001c40c680501d688014101d00c003d640001d0040005030074039000c0070b20a01075140c1c03a0347c1c1321a01984c0e48903164403281c100c1d562a190207040703031305001c10488070315000800c0b1411500b20740c020b982086815140d2042134001401c1c0707604101000e00503401041d00301d00c01094003a8564894140321410030600270300940c0140c12440302c1d1100c82005125614001481940c000c0d403110400c1010a01440102c0c00d0000948004080c03a100009002c8055000f04003001940c20940f070085181e120b00c410041080e1483d41401c442c500c040d00401e0310244980408020f4074001d490192910ba1254089400c07646400c0d03003070300050400c0c240d012 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 638972670 1250 638971420 638971427
    0x4030b0c0d060f0b0a200a110a050442090207030f0921060902060309070303080901021c05040311060a0f151a071b0e15030a0b060118081c 61
    0x1c0a80039681408001c40e041c134445450300d101e00d9210100380f003000c5440e00e0031400d0030782101d07141000b43c0040c1c3d14921880c0c58813145414204070014440d0034001c401080070305161081c40a016141100b0103198040c0103d40247c2c0703d640e0008000320300c2d400b18038251080b0902002d0006010101005a8501450038000c0c0384560703481c0e00320108071a42c6410088040d13200c4080b00d0100010707840c940c460b8102c1c5040c0c8020800054000e4110b02c002c0200060040302250690444c0d0094507888040d660341e0f10302a01302d100f0703a0305680748840468071002000c0050792010b41e20130700c03d0800c81071201e40403030345c5450800304071862000540c80303207039035100c162a500410341c1920324201c0081115080c1611803846851184414a20000114440080c05a0103062001040d0081c0941102c50703250030112030004011510512602c807106081c80050800184c1c440001d81c01500034034440d100c680046841d1000c0c0050030810115a080120303192105002180352601c40c0b40b80e111100e0148803000d0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 638973920 1250 638972670 638972681
    0x30d110d0516080c0d15090605090a050f0a092a06021902030d1803080d0f0b060c1c022d0c0306040c0e060402040b2b09050a0204050a0204030b0c0d 65
    0xb84000d24082030098940c03c41042600460b000080070340701c0d000300d12038600515590008a40002142c075001510600310351101c01500c0d8242c60300c2159a40d900d5003a016610241c4561486800d0740001071400d41c00d0307903c200c0c84240302d901e81c4114504503420800d102200781111981000c411041042056010041c00c2c50f240300c0190b50100101e00b94001130349400c00607480f03200b406068070742e107000181e00c94541c9001d103520030302c103a40794071030f04035030200800625044084040c40c10b003414069141560640d19101081802800032403c000f0000c2d866208801c0c080095104900e0090f64070815600d212480040104810b0150340c54800f00c5880c00e03c5012001b40660030072428440841d511107410710039544145e004402d00d4542c64080741c024840c075030104118840c04256881001c401450225010004031581409000307c11586001c54008140080081c4d2041ca104c2d4014100307034102c998092a24500181031541d83d07160303a030707422008a0b031501102c0c80001d0203030503859140c80741 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 638975170 1250 638973920 638973931
    0x20f130f050d050a0b071b06021c0204080309010e130e100f020c1b0607120f140a09032604060c1202030301150c2109050f06071a09030d110d05 63
    0x20300807000d5850300d0382625a204c282004d09005003000010b04161f01444100c2d4203d21001d1000c0084c02c0c003802c14600942020602245c1e104112201c00f8180e4031034000e90342030301c000b10040d52805c00c401e001550146103140100e500040500302203407103c146403181001401c20040500f079155a00342c03000c01140c080d441c00380032191041c409843e000c01c00041000d00a14810703041c5102d0064030000500a0150000041c2401602103002032103941c804c100c4090018507858010503038480e49034240240c01480202000622400010000706035550014100200701c3c1d5400c1c44005600700c502030705175000c1e070448004100040d8400041203441d0301c05000d12281c52001d903040d541051459a0203004c03046001040011925030641401145a000204040c00c104808448500020003034140d50312882580d1107029500c7c0b0030840e0713003041011070729560307071110305c0f50046465a804514240405080389a062109001401c0d10444a1003210140200c0c0e00d242c0d616041e49216035016200001d10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 638976420 1250 638975170 638975179
    0x11806051005031b09152208120d09080d0c02060a020c0a11060913060f09091203110c0a2003150402100e04051e22060906020f130f05 59
    0x14482002980401600e801260260b02c8480c1e65404c003910010502400c06400c0d8001000d40c4240494403480c4002c0c001d000800070414141c5002c000c02401007445441281d50540007140d8030074401e00c02000510191520200000b5025001c1d25500c903680c02004448801c3d5030745070b42c82c2c5ea0f404d030108900356010070203400541c42c0200c90084652210540300f4000c114800111505034996100015101443d00240c0000d00002c1d010f210800903040c0380c0325004600d40d070301c040841c20310b0040c0641180c0e250000d620004100d501c000c12030042c410181030080400c42400300b540c150300d050203903c0c6070b980036a11b142d40014030310760020042c0c2c0070710110303601c43d50054401114030303004070043d550b1060b0110350a40e042d01d40315500382c800e103540c100b000d5031142c9404100581c407450302039141a644030b000025045981c449581c50100740e4044810f40c91140c0d11a0140700150079600b0106049202c4d440142c10014085d00e00541c0780c00031000c040d10241402c009114034451510381d071004040864 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 638977670 1250 638976420 638976439
    0x20f010324170615040b0d0813031416031101180609060219030c0609021c0b010801050a052a0f030702031b0c010504050909010212010b0c0c10050a080a0b030601180605 74
    0x1c00341c3d160b0040011680c002d94803101080710741d503100e002c3ca000054100c211549d8a8000da0040c004072111408101ca070b5600708003404d144a40000795100030f1401036030003c00d0460542e10f420310002c0300e400f02039041000a10340c050018a90640c850020412600d503d1246410038902900340a20009005a9404139020341008241e0000d00c07006500d800030000100d1400038004544000343d02c01198040100c010070344420410b5603540c540c1200c4084000304810b8590000315020381c0c4080d505000381408c0c2441c41c41042241c1507501e880700088800c40303450845c112403078064030741007207488001680001c43c01c242800d09111006102c0008200a80102ea0207040080c045025500500c0e00031071400700011611b9030250304591604650012003c003641e034551190000764000028013500b0f02550400c04110300f40084280315015103500c1c1d05003841071075003040b1a903d4005201075080c60700d9030241030b200e44091000d207000c2d0401010789000c00d2800d221030815203100f070b80814003e64000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 638978920 1250 638977670 638977681
    0xd050319051920031b0610050a06080705071b0e07090305030315031207060b0a0e010b030703230405070602150606040605160b15180402030a020f0103241706 69
    0x44084081846030b5080060020308030f880c3c030000c11004030020a01034840040d0494500385a48000e20b180c400200c100c1c1c1e0340342e95640032001c0c015070038801c09400044100041c4200740c0146101548000300340f420134204030300703501c9000030720103420510301040030380d15000c0c000e0811009040e80e01040504041e89100c1c6160b0b9881c0e902e20008224000c0080e083d041711107181d41c10f00018060054640c0f9040d2100d8a0307040480013003550708a21072040c05280c800045550324100441d04882d91074140c0383c159644c594043d070281036001d44898883d01240d540010b0f500b10355181300d0041e0b0107000107004803030030418040d152010800e200352208998004011841c1d898204441c1614410300d0566190403c04007000130110128200510115403082009514402e0184003e141041208c4400110326248111168910107403806501034010441c60710260900c0385c000503840030b061400042004038040603000c00c400101c600e5051023007000041044070301c030301d0a0410707510b048001f4040740d0502 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 638980170 1250 638978920 638978947
    0x301050601020d141606140105011d0108040f020d1a0a06080a02120708060c09040609140a110d020d0203090c0306191a04060b07051216020904110d05031905 69
    0x4403c607000c2000718982c03010f140a00050240e580300b0040c070303001c920052040d00e40500940414828280ca80a961000040661050210725410428014403030306070051400115241e042c0200107940c011150458200140c440240b20741d0503d0107401d00b00c61011182c40500010303a00540440300d035508040003485202d401141c07124405a04403141c10020611050290410314282c0c0710744424001c5008001d88208018010700000348200c41c03c20100c1d0300ea803464012651540700c0b11500c00d15181c0040e0b0340c00758a501551994048115441c01c2c04418078081c0d0581e4016402e03c0049500401440003902040011404641c406c40142c441480c10807884030054280b00410f50803951103851001c0b200840f000c140990f40b0024009226064550251400640c1300460072100f030300c100c001810070940003c003590070710515030400d880607a100f60204804940090803c1d180d0000106802449644140214912a100d0405107490f8101c000810280e90307010030703e4a050100c20800c541000781c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 638981420 1250 638980170 638980183
    0x6080108100203150a0e09060108030301060815040b030d030902040e032b02040f030308040326061005040f03060506032e270302011e0b1f0507150b010e030105060102 73
    0x180c82001a101e07918640300c0c40518981c131105035003090305840d02181d40840b41c1000b910902182d41110a2a6601c60305c15999210920403807000480490102d0709801440d0920b00b15040d0090003c680e06092100007814030380381d03070048008240e0311010b49046040c9030207807070824000700001e1410a00040100d03107060032002e082d802110b42910322007000e070f0101e90548024080c40c031100d04100fa101c1c500a0158042910309802140002c04c01c000c070b88503410585000010842e11b118000d45608050025100003070741100c3c00c2c400306001c0414951090100040110302482c00842c01c0d00381a02413504083d229818240c50302d030388000c03241c199040300c40044190800c0c2200003444041e241c0c81250300c10714000d0040e40c8440404140300505905400c49460742c18850018011944010490800c48000b011080d411503090200d81c104504c01000040f000ca5182c2001c0c7e207001042d95038403085010a0110450641d9910502000365903c8290007003c5a820307002045542802c8001070354441 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 638982670 1250 638981420 638981443
    0x50c030a0e1206270319050d090506090607090f0e0f0a060306020d0b13090c030f03030e0f0a170a1d0103021b0616020604020d03050c0a0c0306050702010606080108 72
    0x10000750012140e485550a50980c00340d54030a540050504144115036501e040c1c440642070a030000d0384c0ca01440c40801120301c03640445c642480046a050000d40c1c1d15000003180c894074583c0c2c5c04604020a1050111a01c01d01078140a890a440d1000001d44401102e41082498186031034080c401301264001c40c5401101010081c0b16079500c512644025145035000248903600101c0e5900d1100403075082100d8040081b80d282075202e02c40d19a0408031a5111805420714044e50700400100c3e00b40da0458082e40d0180c980070661013000d0f0115840c101100c40c140728a030340030660301c4c02800504a840d1080450345031510385412440c8070014420f039007601c61503000f00c050010603560b42c0e020350704448070f601303144020b0300c000051954019100e40c8200d460300b940c0c240007824006c000d480403499912843e401440c00c00450040d440888440e005040e05400d903109241805000c10403241d40d150007184968000b14042c50800da0003030030345086070b11013030a104200005101c0c4540200d070811506 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 638983920 1250 638982670 638982677
    0x40b04060e060d020d09030e030105060d060504051606080412030204050f0616050d180e04020d03050c01180f051507020304181d031905030717130507080d0f050c030a 73
    0xd800304001540b41e2103001d9000c103800c3c0c4002180302010340544c00841c0800d00030340b6401d00c1054042c0600d4240c51080320603540c0721071140000300001e4125803020b9040390003034080303c03240e80c0c1c40c1d883c59a060080380c000d1030200b0300f000104420424041c004081914071072905508240c03401004c06c0c22071510f441003e01c14840460180915440502e80301c40c21500042200c00380c444e81c08004d0191601084400d509500b44a030201e018603102135841d0103564046c2195001c01c2080d201113440f5040070481030b105540311032070700c0380075035000d01d01c40501400703507100101c0d406007494046d24002d4080300780b0820a008400304801c461b0048261000c03181d403041c20802c0707140c20141704801024030303209228442051000c0f600030781a000014200802c0000c42c55031491808440036591400104c40f0100020985d001c03600d500e00030658255003140c0749070f94030000703008690788050904005e50040c590a40c4498480000e803507201607080c2c080c11807424009e20b01803100c072143ea102e11034201c102060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 638985170 1250 638983920 638983937
    0x2109030d0c03120c0807022e020327011d0a0b0105010305070e04050903070308010828020402070203010c030c140a120b220603050c0a0e0708091905071703040b0406 72
    0x10b05028103200003c181ca0000100101e015402c0090442e041c2070314040011b00c070382c0d070380884c81031a00101d40030000038208070107002c05503d0f41080003079880100f00981c00411070900d403000c1c0c0c106000071554a280d041c008100c803284509080c042c1a58106124804d0b40035600740c8000c14044010315054400a20300401c140d0f443c91419031701c1200019a09402910302010848101c0c0d0110203015110300c42c0e51640d25503643d44124980d101d81044040e100c585404c01c0016005201101118003644058005810408550000307403c40e140c6100540100351240c50141c2402e9014200d0040c1510100c0f026040592041c8002c0041400b07140300c1e410b441e940c94010402d50758040c864998945c80c941c110240900b201c0f440c50243c441440f04039010302c01c3c241c29490502e1308500c0001030740c00e1040100b205a4510784100c495000182105140340101203010800200c5245188005409000100030203441c1101c0d02c0843d400110b0748407059001480103101650004048070308076422480c01018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 638986420 1250 638985170 638985173
    0x601030c09080d09150e0112020a090b0d05040204050115121d060c0d0b1c020d11060d1a091005090907151d0114040603022206022109030d0c 62
    0x11a200e868201c070003144583d40c1c0398514107902081d40403c0d10144118825020036010017603a030606080e01c81408140001c50034081d00201e46e020b4611600380303240c80001283d03503075101502d0f5440070425240360342e00d400410055042130302a039030052103012481c00101e404104010048051800610513040c0c6412401c078064007101074840c054151502a590f0604014001e0141c0b130380f28003402d040e15030900000084034a00103040c1040e10680d403042b03004c4115942d0800102c00c040380e20490780d40c880c980341081a500e0f20303000f0702945c00c5462030003c2c0b0003120303103a090321981f041c0c1d08035446814044100f01c003580030044103108940d025120f481c2c00341c0b1072000041c14040b83e508100480045040c1c0f01820560008a040300700015440442414465100440320405a0020702900d000100b101304203076407007035000306114401d40d00080e9110782c50051850292246c0c1e80190012b0780107100307401070030708552004010103240804103803522081d0b00109481c0c24804221505116a03120041c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 638987670 1250 638986420 638986427
    0x150105120c06040801090c0906080304060809030d060f18051e1012030503040605070c030804030806010504080f0708061014060a0c020303190e120705040f110a0f030b180601030c 78
    0x1d51000500c0c090b195911002114000c3c0844d003410758042c2041400000c460b100342c8141d0041d540500091840c1c90700340340061721a86809895565507100c00c01103148000e006214020183c00040d910110303403881d00b0040c4081411185200510724030b001d090150408080031002e4071001507480502c003d507106000741000c6502c650043c4822601d00b4040760816900c00d005503c0786d8071030303102000710341c407400c0080f0340880b0703002d100401143d1040041000309000d00b241d50b602c01c80c14908149416260b408481c10552858480b0602c0e50008406004e0382030103000702e41d8011710399403000170304529085c04200150845c480e464010540092841102d81c81128003150841c0c01804403682d0300140104411203d25a440070310006801d15400006c0b407030584500451410207000074080c0c81e040c00b04002c000d029445414103500c1c1d494000010811201d0041c2184403000c0c2c80d0603102030b94454024040d24403c0701100c0c8182c01400d803038030700d00790740410b01c0f60402000c0c43c000a42104044064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 638988920 1250 638987670 638987683
    0x30302090604060e1503060d0b04020a120c170102091804030504050a030803060312160303050c0c01060e090601090b0a0e15040e03070623061012050a0603021215010512 74
    0x5908168002008030b00c2d1900104503c60020003078694445c0603801c0d140700016404103036000c6905c1100c144100c1c0205824101d1140c2042c0000d044d56420b5940c0c2000c605a070502c144215140d802c4003604101c034594032034100002c025000020344ca08002c0e1000200c0640800c2214151042c10801040525100b0030654010b050301411700310350300d5240d05080d03d040e04203c80b03007840b910492082c4403903448076070280c480c26000c1c505041411407560350150301070000240841003002080c400c1246403c405d025100c01415040d040708464102000c805081c4041604000541c43c10500bc08040751504400380d400c4a010714500c206640b12803102710413661600c0b401951040c109920244a03010101c01021301e544600070401405200b6002d90b040c1080714a070b01c0320002d8000c0b0000c0d0290a00c0000c940a0501518100f182a031075140e0f443d0803600140c2d1400c1c2c50a556032418021420098140100090700c54000c003044e8034101600c00c41a041400340c1d41c01030087c2900800094002c2003038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 638990170 1250 638988920 638988937
    0x1701050919111b1915020c03160c03031b021509040f09060203010504180b0a1d060703061a030405071403031204050115050a0b0304061505120715170112030302 70
    0x103d548030449051801d0318901c4031000c81c4240200c5a0000300718000d012058002c2d43d000c018012107401d120034501c001d4200c080300b01750901040001d51000b40a000441701d00f1407103000c03580ca6042c00e500b4024041740704045c08001040c24603c0e001d000d070765041d03042201e0b8000218015600d18101e0027040113016121401c403003031801e1640000c204039030391b00610305a4200350340c104502c51802009100031001d0030b07405001c1c0900140403c00c5c041240d00700088105801c20b81c60750030b01c99a0186d5140843c21a298400a81d6902083c450991050345502d40d9400e5402100d003981030030b031250b0340c40308241d11907444803400162000d03503030740c40500a5503811100b1102c1c0c100c05203401d0a2080c060003449201d1084568200c0c0f010600b8a4901220303003d803580b141c1c0e042d003184d60b9680c40c0401090f06891320400c0710440c0b040040d450395107038000c070480320700d502c0581103141c0f030000782840c211800f44000c0c083c88841d000c40075078a058111010304541a00310440c1c10030350b16060175002445030f1580e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 638991420 1250 638990170 638990201
    0x120c1305031606030b0f010c060b0607080301080d02060610051207090914011401110d050d0603060e0c03280b040c0e1006090e10060809101a011701050919 68
    0x400742210502e10000e004803a001c2d1003d00003154188200020340e0342d03806245021519480311003010442e10342c490b90040380080e000b2450013800303480d000c07042d41090f441442c05600402040c1d6a4030390500c18250071400c03d807045240145e400c040682280900303821080400124000034204d0391103070795840001e01003a1010400c0114500403064074800174000c0070f03100b4050b06403451003035100300c500000300450356000e4020a03074041d808070741130380c800f0110b110210788a03413000c004541c00b0700c12112210f0041008081c04603240d414503040043d503030320703252022a420b40a0341090b69000004c131031980e03014a000074580d69030300d0a071080310350390f07044000c4058450081045804c2540c00460964140d625032245055464402071092042261005100651900e0800429002e80e410b540c0100b99107054902c030b1625003070010111200101402001c21508001c80803958000c2c5604680d41c1074841c6020143d13040c100800c5100c3c2e8098910244e80d0038042d01c01841b20440d9220200f083c85d80d10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 638992670 1250 638991420 638991433
    0x60a020a150207020a1a0a08130c23010c201906030606170411150c0a03030f060b041202010c050f060403020a06051f06050a0927050903120c130503 65
    0x70031400203400c442c8040380140600c14002c2400308005045112216941051070300c1c00c6070340581204d4100001d4011039035071110080c01c50001d03030041400d0003e044007401d1130110220140d09904500c107440b1005050204649401d80490f01000c82c102e29146154004544980c0c54000300d200c0140d076060022200c3c0740c50303501042c02541034003d40c04942060f542c40c0390100030300d401003000031000d407001808881300c401d0180d05400c105004108240c40c415145080c403c0120265081ca9854942280002e9903001d100307060702c5c0b540c410300f000703006110310742030074170781049140101502238680190600250380b0b000001c01104004179941e08050100b81c6195042c18540a5a142c400c6c1804580450400000814049202c09482d104c0d034501740742000c00900c0c0c1071080e28140d2088003030b41c00304640d45801007600c944040d000700008051282840152141c40742c4035040301da01410210468008010040500124405c038941110380503d0141c0d40b19441090750320040b900c0d44c070403a01401141e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 638993920 1250 638992670 638992703
    0xe0109030f11100206070804022b05010606020f03041802031305031201060206060105030f040f0510240803090303040b0c1507020d021509101109030a0f12020a020a05060a020a 77
    0x16120380b61100c1c0b060b18030f5910b45500d03100981e25103004844420004130200c0c000340261405619400306da0380b081100340301260171a800440f000721422019030702a0f45541e007c01c40d40760304001e84007404040d4806107080c40c5c104072250040b0840008e112900c5500480030036055101d094560301c0455000c800c59030340c1c548941040d60741017001d1107180c0c05800340350300190995005408413482a604100903520a03542c0d50380368071105d40c04000a460900c105d0182d0892800343d0f00c00d02c0010030410004078141016102203050048042d00036030040d410a000d44145501e0000070303507099813a048400360302c40002c0540c03103161050710310382c0403040c40b400c03000d0240858010130002c3c0741c01125420b41d50651546c1c2c0030084030b030344291030701e48241d402695050619045a444480d540072461800307483c10308540002860151501015240924000c1c1b0b020304110f9509411012001039001030035084001703800066030801d4034410140200000582c03118011710a1200c00d980b154031049049001024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 638995170 1250 638993920 638993933
    0x2b060b1f020f100510032319051002040f06081312030906151a1b060106080106020708071a09010c0c030327081207140303070519031b0e0109030f 64
    0x44082c0c18481c0600c1041400e03101d07080c022184591290b40010344034a1450761400500b809020142c1107a0440c02c003944c004540900c020480710300f804940940c01c1c169030400e03a042540380140121443c0c0704020400500310000e49800454810341044035440d66040c1024400500d030031030041c943c01d001055060365030b415503c4124014094072040100b001c880540ca00c8001c424016140f080040c01e18400c1144080e1004000070107102c1d28021754104141200352802d2001e0b00540040391041d001840044c0c1d04205040062460000804074589491407119030034001507011130000e0740001c0c17800010390182c1048182c2d50784c800c40401d12142c1d60305008000040c036007103035980c9080c3c0000c180c002c1c0d11981c00c600e0640343c00501400c0340303680741c0440303802c250f10140c0102c0c1c3c04c5512541c10580d1030310030f20145110300c0054a4071a614510000c22507404110005580207040c9403440c0c0811812020365908139001407400c0c034858500203000141c0781c01d1034039800100030302200390300b09007003012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 638996420 1250 638995170 638995183
    0x20319060c091d0109050a0204090e030c061015121b0306050a050d050601290f070b0105010306140904050c061809090c090406020a1205070206062b060b1f02 69
    0x24503990341140030f80c0320110041d546661106865403003050b040144000c220550010350040150580145007660304c1101c90140c66450300ca81c1c159420104035078840702e1062160380c1d401081900300851507800c0041c4244401c05803504402000400a02c00f020711031030740d01100c0d01c01d0441040d04680c2015082c01009000a07000c1e0074024032400200080c01c4c10541d00e40ca107481e6001c3d014200503802c0c02ca00403134040312001c0051400402041515244480304010080140030110f496656056420141d1180c1810f03400f450405140c2601080480410005c0801403181152019100d45443c20214138100000c100c10754448000514000300d0b0481101c076445170344054460204c2030381c8042e1041d45500421050315000741c0340d900010f000800c00d6004007070200131800c200b0740c0c80f0102c11040c81203400403074841001da403020041c44050718140100450039200b50000300701d507005c1700001080c01e03540c104004140c1c54850fa62101c880c0d0311005010403c000d4110380c09410752091000035900d09 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 638997670 1250 638996420 638996441
    0x70302091c02010c060e060628120609020d120914090a180212072603191e080406050a0b010519030908070506040314250614010f1505070b0a0902031906 67
    0x8903d84901009e6001ea00000d1861400140020042c03490034a8007444081d008000f2201036a07104004001a13840d40c1c05402c155026000520401400d204050070549040d0001d0019400c2080f00e01d02c280d07114002c00342e0040d410500801da169188140103120014118000c2d44440002400c00044038005282000c4800030590044202d90444110030300d85034840051440760000c2080210390991342c40a0712201c442d070710b4004240800c5d448500c1c05418500b240000151421041c402800850f000f51030b0410141c0302c041211205210010b40107104980c004116044030b9545c010102c2d00a40c0481e802c0c80c3c000880b55610f996624042c0d0b11034004490440104189200143c000c500b02d006481c03200d00709030b003003c9400d4124480c1c03010301248030340b08864180e100c0c43e600700108200300e8518000c0c0250808007040904203447d0541c11a012a103c00c00c10070309000980204022412403900100705500014040046001007410030a820440074540c48041d03c0310000c001c860740c4520f080d40c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 638998920 1250 638997670 638997679
    0x61701050f060c072304200c071d0a14090703021203040302030a08070308100602100504170703020a0201260a050702010e03030f010e06010c08121f080a0506070302091c02010c060e0606 81
    0x20422004006c211071803110030445400c60b0100501070f80030b0701e400409400e226042160242c590b150801000c100b079620003500342548810074031140c01c106029002c00d200c58001c0d002d100d0325114a565680384502d10000c3d100324220394020004010034411240a03640203070580c2d41c034a07950308207200d050784807001c22000207035130b0800125006094014041900d160303a0240620b40501881c40f800750001800a480c0c042841600221261298008046851194024040e43c0314140009000040308581410400d010300c0704007090842560a03003a0b01450421700010b40ea00c8100c03049005240f20b1892a00034032001007170100c0111035045640c12940410480d9400c0c0c0d440b0b4004481c099a03a5800a0008400303019220384a80380303200345030340b01c65041000c0d8003064034144540b200b00c08960008025800403110601480380c2031103c0755120895040c10f6103000710250124008101d082c5121080320504c01170441103a01c21429803c10640003001407100c01d210113410b9407144d40503642c00b07106 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 639000170 1250 638998920 638998979
    0xa24120e010618090f0f0519030e03100203131403090d15200d181b080105090102070f0f0302030904050a0f05070e0f2b0302060907061701050f060c07 66
    0x3100c010340951044c4070b621200a144041c0a0780d25038080031b2400c003044449018075a090814102c0840710130041038041c1e03a41d40c0000c000b070000d150409000c18000790195004004200b038070818120790380c0702250301110200c03840d00148e000d24254015520400d6018005a80130400d02c010601406a000c0c1c2c0c6203420000801260807500040118200503000350790240002030300c8100c154040800c8000d003008164010f01c080d540d011909440307000078005c01c2022502441148824412640d00c420000c008515000c0c1e56200e840310070444200080800d4080341c590002c151007841aa58035500c044c100b40004e051001801c0c0113400d20a214041080c500310004228511a11980400510261400d80300f401c2640c00c0c0700701c00d804c1d040180244201c02490045800c04110000301480c0039501038020344c108552404c0c00d11007a0381c0060200001c01c15503800c00c0ca4442d07550350450740c044450610400780300300456114044c0700c2c0191124010442c0000d600740c2c08450248141c04400e081200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 639001420 1250 639000170 639000209
    0x60e040c0b03090601120510110c1b211204090c0f050307091401030603020904060c09170304091a1810121502090303070b240a24120e0106 61
    0x280800c8a0000f01c540c05500100407801c41e034a400f000807401142610080c0d000c10f5030032000c0d540c6527898134001031000074044248400900c440c1d040651007000203c00c0d00c66000001e08c20300d0500c584d5007c0301e058000403510f0940100101d01060950054503519159544006002412203041d210b01181000d202164054402d0303080742c0c42100c0a40f1050107090a00e41468420f41c00149130b10705040d0b07034034000300150352a080146d10a40c07007164045480481840000e019030034650188070024034204940044c1c0d440442660181c4420940001c0c0c1c9140301c810310b404184900c03542903001134000903404010b0301d201c4206441007240c8081b07540b03e6599000c01c0c2c0d081c5003c40304041c1c0350640c622000420460150004c01d000c240c010b04803404c183c0f00e034440010900c0c0980d6021240348035902c007031707400b001d040c83e2085403020101c401218036443c03c181c84000100c3c1d4903900c4035421304600a04010ba02903000d41c50042d010070703000c1010101d41035445008203658028a450700d08000210070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 639002670 1250 639001420 639001439
    0x3010b0a0825061b060b0406090603110d0215030a0b061902210a05030415110d050f0c0a03151e05030106090e1c030905011401050916141309060e040c 66
    0x1e0846031940d03100fa40103031403120306180c020090304c0201d400989445511801f56514001c02c0c02034007214030000303811440d614010803a01d01c190701e640d0080080c0390400d03000da60782c003906111141107401d070a0b40d659940c824100042845c81020b0768801008650440620040700d0550444002a002c40700248003441030b001c899400f4000f0782550000410240c40524030500103141c0040c0f00e80550780400341e40c0c07000d00c1c0903144181c43d81e52808401044001044896009650b0021488013011045003001e51482c0454858144820207254507800c0c455800c0c40307280e90010040403010160b0780318510707211aa042601961048611940c01c0c80c001045407001c52007000400380303105d4014486010a695083c68080c80c0000103014181c1d101c9207080419020300400326881012003203000598185810000807000140c0905213504664078620300c4140c0207400101c0d1814a0745161b512228580681c00c410703550398003c1d0b4003440c1404000103500341756414035405103218880c0461810b45904810 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 639003920 1250 639002670 639002743
    0x30d0209040c0c082d0f1314010507140c030a08040503070806010509160c060c0215071e0503060301180f050c030313061b020334060c06020903010b0a08 67
    0x80c00b80b8204200d40d407400142c4600d16145c80300004450a011501c1340b04120041c3c00c4410b662010000004103144440c00e040c6a10028000a4030b030403100e181c003040020b10b240900071000300310407045259003620110410941c004800001e003242c440140a207013050b115009842003a002c0c0c0310701c0501242580000c50b1a0b8180d84019141c0c0d00c85c5d40c0e0300c031105c0c85019220b104031010b002c0654a1280410214060f071182e0a1150300100f140080e4107801e0000c3c079400914010420030240c004402c0b002d851083d04404240301c1c686152a521060002801040140b128003424401366480c141040380c00100181e405000d0303400e0380c100c1e0600f0720a054aa1141d82d100c20740c9203026000c1030140500455907420701d4500b080c0b13844000754584c0c0c00310340740c694648c280c44c0d00003c100c40300f003a2500f40c1260249844440000c1d0910091070400041c2c074001c00f80200400c4250041680b45a903182503004111041006003225021552185916150045030035429245010b98001000c044946490f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 639005170 1250 639003920 639003923
    0x90105031b040903270311090c0d050a15090b0306070203090604030b040f08040b09090a0b06180f090c1c0504030e010507053405030d05030621030d0209040c0c 70
    0x1044001101d4100700c01031140f0f100440a018410400c40d05000e60356402c561100700402c0d001900c10b0840c240170150000303c0c18400e220f8030704841005044030601003941c200104042d408541500c481501501a10184103100d060300c551200c00181c0c80407503045601001e5040d0166000d40d03c8503002280c0b41d1149151139904080e0802003040000c11642c2c403a5130160140c10031211042250352410000d41c82507010807044180899119840d15002d40040e07001000c600c4104005081800440e0355030117802211098420111100c50712030f1124040d9000e07560300244000c14501c0c02840b0250709800c0440030304c1441030b5104034020f031103100d44149030195800d03446540d44207100030011100c030341c498007088509010315002e0807405421600826610a044061202c060303e016884107401e0905d64000d0b40310364007039601c440304650000203d036040507044d1050546650000a000e4420207a076451988904c4006929401c80710164080d2480750011a028001c2c1c90403800100c40c070075202c110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 639006420 1250 639005170 639005203
    0x5130b0a090b18031002090f03070e190902030a240920031903110d050f0d11070507060509150307020619060906150201150806010605130312090509010503 68
    0x4240305541140d0b01414003c0c900644400c983d0105001081c03d02c120300d2121401c00e070f00480d008401c0e01d0309082e40030310820b041e00200011840d0011742000c08001600a8454080d99180159a2001900001c20003500641298003040641c07914118469204617558010380d0441c0725040d4254903400394000c5d4582010903c185111740c2002081400a60184142c0c18402c200c4e565149242031840940424041d4a911228003050030b4041e0800b8801103000c0c0401008000480b07048041d48c095504200c0d800f0380000780d10f41c0342c29503404c03203116003c806031103172296140002d03c007584200107190102c82550041010b038160401c4103543e020a4071507802603003210b40045e00b0603400490922201c2400213011600c035540f130754944115034080c0c0041e641c544260003138030304594090140e81c240c010a84030500103e481c1850301900d40c2418003403034040000000ba200346881203c0c001c10080c40c0c00840c44604c0e020348204c094454003a6104241c06104d00000001e01c614000c20b11040c40030303c062 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 639007670 1250 639006420 639006437
    0x4b150108040809040c2714190320211009030813031b060b10170c0702041b02100609050106050f0f04030c06080403032712030b1005130b0a 61
    0x420011744102074442c002c1140c0034407044884001d01070315034a0106404070000c510350a00c124140b1a801204800e07004039810217280391504032034040f400840f0780040301e010740c000701c1c0c410a24004a68071803090348020000d41d0310190042402d610b1f651101910111038041840040720820b4030380c03121028000c40c03100300000d20008081700070401014030901d00884258030036021404005030030a82030f03412a56031038401265040146000311081c1050a20040c850380b00211100445c400501e191405c00b40403030711100310b4446410402d030048010300c05900d02c1e14650002556023501c250381c0e010f45818071800140c0211503124050683d459a43c40502d0300d802c00480001c65030010307000404041040100001240c08000f882001d0401ca6441e0900342c103250070003d00f9640071245403044110002013002078030b01c5407001030400079840101e4403010190541c007580240080da000381c2d003020b11071010f40d6105503c200109102c00ba86c0e200680030075144c0003541524010390004a01250f44070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 639008920 1250 639007670 639007687
    0xa2c06100f120f020a0c021804020a031205090913120327050a0c0e180106150804060e0f0606100801140402090a0308070c0f0e4b1501080408 62
    0xc1c10800814124441c2c0401c0e1401405504400c90b440408504000f6034020740c03c5046141c03440301039415904c041900c20b140d003059000902c42100341e20008214241040c0901c01003402001aa54803510013441c104451802d038240310070301c001c540d00448201c6018010703100458001e119014410019011100402c0003026000c42e0003035044100361224443e030300084001556207000e0342b02070412060720000f50f0a20110f00540d030b0b13445078071001c20769040482c11b211094005280c480205024a0403541d19115420050010601000030381e550740140040f403482ca041c00030700f07070340a05000d41d03069902a2400c2011180c1036420700501c1241c0c1c0400100b410f8502c0d01d50041c10305410001d00c0310841641d02c0d034a032820b41d40103140c03c0342c10003041c407420040d8082c880188002440e10202109452414141d200b07410410000211500a001030100301c2440b60b940c00034041c40b00ba00f041d41d44200200c100800c00c0c1104072200c003003c0e02d040c07032004007a500c41d20200340140e601c4004c8038240f6050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 639010170 1250 639008920 639008927
    0xc0e10030308100b07260a020d0e0612150108090d0219060e0d0207050a0b03040b13060e03070b0a05010909050304060c03051309021222110a2c06100f 66
    0x1900d00141c000d00c0410128428000300002c007903c1b0320548605c00c0d241640614000001e0301800c0e4a12400c005000580c0816000306e6407210301c00c0b0b6403600c41040006000050507900401d0000080d010420040111040d44080300c5c0c4840c80303017601c40c104030760f54002e03541c0d41d00d0840070039900041c3c015025603c201d501090315140264461040480d03208002411030346030004908045006034043c0900b00800d0805204031405004202005444d524103611103007400c0001505c0e03d46540c00001d0103000b48100741c0c0c0708030500040c11060702d035240005e05000c0b000c50703010356104143c0d1b8074000000030104201d1041c40143d992002c05141414035101040d144601e42d0001901408010429419004104000c02014243c017035001038860b21002e46010443d034004003004061440b07640141e61503085683c0c880000c561089645648020715804909000d605900049042d101e070b0b0082014080d8258969498880c21204054142d9134101000035514040b60304401050f40003491900c005e20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 639011420 1250 639010170 639010187
    0xe010f06053114041217070c0515010b0909010b070c15050d060b0304050105090705131a030d0c020907020a02132403080c0c012a0f1e0c0e100303 64
    0x20054001c0182000340039404103071500646a5041441003004110070081010175002d407040251501c140b0541c0d145c044031421a10142107001848007040e00c507400c11a08100030b1030500003003040361050b541c1d6514003083c590840b50b203840c03062100b01c0c00451011141c6046d00c50303080c3c000c043c03a108030b0703c1c0c1140103101110008902041007010048040ca142041c000c04c00148420702881c0e80c0ca20349410501c5c00c40c3c5000d0450030450304038190810050740c614903203520800103840e00040b1090000c038032842c00b00070350040c55054019048814021504a164140d20b18020740f58500c09a5907070200b01d0b1244c4180b00c00079030051100c410034044c1c08040e485020002110f48080030325109940c1600b8200ca0320f41d00440308e02d1400150314881d810117000b0043c941200782030205c000d0010391208002415002c41400d07566800400000501100c82c0c2d80024054100aa81980140481110040e129080c1040d240400104000180103030311902e481d00c54451340924543c91070a6a508640514 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 639012670 1250 639011420 639011479
    0x10e0a030c0c0e1014060901020705060313060e030a09151218020402070605060f0d03081f0b03090d09060801050f100212160b010605090102120a03090c090e010f0605 73
    0x1e00098002c03412203c04501c0ca4024100f070f00303405910ba46010301030b4000a8102d011680100c83c144141c41c038607600050301d842076610072030740305444c1e59803a00720000b40b080d403403006003401f4103150501c074400001100400c14580701d65664480952104039040d000d148900d40b00000581c80207c080010310664840300e49a65000f980300e40f50303a00e5170001b40aa1300845800d6a900d80c0c0c48084c0141444d1040407a010210196a400b42c0d0007803a0703c018088100041003091605220400d003800910a0034201003d40000c074501c81d102e00784a5009561346030003071440004039000390700100d410360003285030310304031100141803c06071184007040c0041100c4907030465040d4030526040303d922480d40342c050102c2c01e8000010481c00364840c1880361144006901082c03c4c44000c00c115412a640483c25a00e6115140029179035411034a000724010000520007401164070030344086400d180c40e4105000f1503007044001d025410015041200b101e60310310440c3c0e0300c924404007034102015880300c0c044520 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 639013920 1250 639012670 639012683
    0x4240201090c03050c01110c030c12010608010c080a0606090f03020609010e1c0c0e1608041b03060e060901060f06030c02010f06090506010801080f03030105010318020d23010e0a030c 80
    0x80070301d607403540c201180a4100700c445800c01c003040301716943d002d0104e551380950310000b01102e582c04000310b03403160103024140e8041d44074401d010711400e0007500808001c0c01040c0081003e040d005c83c00601d0305106413820382e00c0300c0c2007840002d10240b20301b0b2540c0903a41800f452207121890750742008540d50040408505102c1098006502552110702110a0804081480c01c020442d45040e2000b001c0d0398111481271b0209a040c006159034204981c00020040d05284555843d1407c1446c03102810a100310086032420308080b003000a2900940030400258040720313407a488420583e4241c8855003e40004414075074400c00941d0720a03040061500c07290b00000500a0701c004403c81555919044a0f03209922071003803000070f503030140c0000c5c010190000582402c450810050b9101c1c0f0041c40340c40c0c105a2a8680104c42d404840405e601c2c040d8014464404800c151404009480015007040310b11922052117182c0f1100c12b006072068040c2c088e004c0c00448841d60b405892005915405480c90f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 639015170 1250 639013920 639013931
    0x2220c0f09030b0f1e090708010f020c06131403070516090c12050c1201230a0609050f06040e1305010c050f030109051005060a0216050103110a030902030c0301090609020f0604240201 80
    0xb107a01c11081e501441b02d00000d0415981002005805d660106100030032040c410030500c2d00500380800d49640008450640340c480364250300300b64805c0b441601c9c00034103500000071420104800040c624200001025031103c0300341e55180c40d04125a05102402c000c507402d43d0010041400b80e80c4002e92100300e1510240c20944601c910a40c840c800741c008142c0740070b070040514800030002d9036118040310201c0d0800303081c034185507005101c2e151620600340111700780c2c103541e00c165541c941a43c018080c0c28256000f20b2030146150300c0c0907a00504192065480d10300c04000051182c01110259003907070b6082441c1d40d11b026182801014010030040030210010808a500c1d0350705002040b420a403070b4001c102c10700505509450040726a4045414185000c0d055024401f0600940c3c6020010b800d000035044000e001013806c040300314500d0b540c0342d4a400441420003030641e011500301400de0302c050b0310141d00d81007840810310035801090880918494420096a00303003406a0041081d880045503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 639016420 1250 639015170 639015211
    0x114101d0a0f06050715051033080f0105010908120c0a050307030c031b020a060e0f060c030409050a09030c0b040c0b07080a26060d02220c0f09030b0f 66
    0x1080c1865041200003404c006000024009144081c0444445400c0e04001908000c060305042c140b00d48640e1a03050240d00109040e101420142c19408030f404c0b1140d0103407414282c0c000c0141034219041100d000d06d240c00817425500c1240c0034000d40703410000400070600107400c04071a07904095800c0d40f243c880d4140c00c00026405001400440e84280c8035400c0100b000d14001d002c01244005070000f628100c40460090381d6401c1840c0d0495401d810656001c00d40c0c18082074460700201e10b62038104800040c010601c040c0000140125840d408013000b9640329102164142e4241d8200a00011403082d5000f0205d881c00c81c400c0d030814842c40c3c444c02e038150f4907064203840d90002c400984040c60302103007610b00b068010241003100700020074018010403a00802403401000a8020341c0540300c0b00d2a500119101c045294a0034004c24818074820051400050017600131091a40002601000206040e0380120308940a4a510100104c40e40c0d840c3c5444264114004084001403101c403855501c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 639017670 1250 639016420 639016439
    0x50a080309130c0801031502091011100b06180102030d050a02040609082a040e070e040501060b1c020a03020f030708040209090d090902070f0206120114101d0a 70
    0x10042181401864481001e00d081005800340d04000600160600720304541003644040d081e41580d520800d0800c0d00d11580f800c0b00300078047c02100c5030304041c035441790030b4041c0e80100e80b0003118541d081c21100f5030308000220400303035611401101d4106005001400c08000446542000403070188103da0402110010780810741c1c0007504d003500c0b10343e4006028041704c1c3d8007138140c40182c0f154030300504c034000340c1900c58040b83e410400050034068030740c0d4524079203a90300c0e00044a070003004c100300d0780c50584500c080114018103880440c0c1c19072818500040c40300011065540c4114107107000d560a00c0040c26040c060752111402c001003650030020034012501c44400345000720345640c2d03044054907040c13040c0300d11000c005d025400c15501c10f10402d0f061a5200d05550152081c1000242c0c45211034500940410a02c01d8029403100f00800c81c40c00c14160022954101c4001e4005007100100400070300080450314a0150001082a00c2c0c03850b4003980a52415050680039020f8000560f4074030018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 639018920 1250 639017670 639017689
    0xf020a120c051b03010609181101030e0f0106090b01080103020a1802041d0709060e060711030a0803011e140d120c210201050f1509040611030c0309100506030c04090c05 74
    0x2c2410340150f14554000e0070240b240300041c0280756001c0101101c044c0c03d40b09040c000201c01030542c82d45e0810f008599100342c1040200a0525003118281c070f10041109000c4c0c4100d000ea10011881d00c030b01000e03039600c1680b010f81240d401520f02c00c1c5071400c0c0fa029038402524848900d0340f0680130400050f10b400003070107801c040404c4007000b948508280e2070041c01c84010354800740401c000700a80703148580d01e020446000b1070344103c0130080da40311440424140300a1900103025044003100000303e0680748800060040707141070060382d065884000000941c0e086080c01904517202504900004040c585194003441c4a8200601c2007404c03681c840300541c0c0002000c850341c1442e481000d10654090183c60340040519204800c81d00c0d150500668440c00c2500392485603003180c003c1003c3c800554070100119000d952660307543d03e4200d440c03880d00d40c8141c49e010000d100707200700c000c0f0050380740c41b1f054000c0341c0c0100500314100c864020030001e0300002c28103640318491350800044650f14501078 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 639020170 1250 639018920 639018943
    0x904080d0e0a21031a0f181015020a030507030e0616051c05120402041812091508190203070e03010f1418030a1b1209090c0f020a120c05 60
    0x3c0c180d030140b0840c2460030742180c18014409240c1070980c80000701c80d40c4010b21800703202c1610001440c600342030001e0140070701e2142d502c0044d0008000e2000c048070900b012810384001c9408152a42400c100481c0c0c9c6c4e4801c1e210180c005207003440031000191003000440a4842c00074074a030b091550705c10410f000510404421030319030744501c900c1c2e48206032110088400a100f41442e40c03c00c852040941d004040041c4021300c10742e5288000300d0100300c014440d0203103503000b20240c201c103225060b0140142800b800307500e10643e821040310403024410700c1c0c9503100b070001d483d0a13003c00c107640034448041d400c05018101840240c41019a50383c6003442060460108828080354040d41090f41400001d40640049058503068880301c011000010444001820501c5c0010b00401c9603881d2a40304044501c00a229012400c404590327141c2c0040341b0130540301003072001c02400802c0740090741c501401100240140e00703d15884408110103101030f4001407038909180e0b28071226960b4041c108045142da = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 639021420 1250 639020170 639020183
    0x30506040905030d0c1808150601090b03090705091501050d090c1d15030d080f040606030f0f02011419050906130b03042f0609220905010f06050904080d0e0a 69
    0x172030740e03415071026058004001440c01c800f001c6003402241900c0d050312040100005410794003080c2c0c0c0e83d104807208801070820742251500d07402c007085100c0d1108a50701c00d1900c80c002ea6000300780e034034003d04507449521038161181480c040144070040007500d8a01d07801c1d6180c0c40200000076440f00b0034461800f000700c07000d020b00e2041c600b4060214030305024244080c0240d1002c0040a00c03260005441d1380c100100d0604603000360f4a600d80b5902030011a04020000c0f40e08000030340c100080007104203200351007600c40701041c40e07080741903644500a84a00c0600d11380100c0c0a4140103014000800d0b41c0c0a006e01f9803458aa801e0154620100081c0e21692444000008000902c4401e6003800c1c800c1800c01d100044001d00100d00482d449400c07100c50f40300d8640000d8200b8603a44500700d01c2d0015481d44410020f07200840118801000717903203c03c0d29a0f500b050081041e0000340e01c40c80701500c0000380100010340b55529000c00300e801480300c602e8003540c0e03403400007001c00c010440080090300c40e09 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 639022670 1250 639021420 639021431
    0xc09080d0f110712080c2b200712020f09100602210a120f110405130212040807150e030901030608010b09010b0c03070611180607050a0201030506040905030d 69
    0x54001c00c42c022905103000380707422810040c0b01d0a1180c0b4203441116401c850800d888420b0401d005003000d0705031110301070640030580c89160400300d024580c9900903c90b100d04000410b6020480d80d8803401e401c0e0000d15411a000910040c040c000d001c141003030002d0302119146032420040b03104c9034010f85100c03100001403817040100340e9041025101e0100b83c00301000d03c0601d44040204c2c1806400e2504003800180108488040d00d2540035030300780c070f0001c0401d000118001c1c01e41002c55125000d000d00400b85684445e030b10070300c0d81c002c4401e0300e0242d0600804a64903511840d045402c140b401300c03000e0301440c1480000281ca4003036110501e40c030801940e0f507150031600140440b1182d41c084c1c00c50380d05010800c00b40c0d55510740d4050440d0900e940440d1341c6d015190020f4118440e001005089a00c0e02d40c01202640c3c111018100300d04014001c03d9021400a00304901401000001002035100004000055100c3d80040d03130042c0c4040c0000c203480541d50365007410b50304010100b0040b80d40d0703003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 639023920 1250 639022670 639022697
    0x20c010f0908120c120103120c0203011b030c090e0609040f0b09030301140d0b040b1009020f03060f01031e230403020105070816050901111009050708120310090c09080d 74
    0x100d20541c04c402c000e103801d80342503880180105801c0c014400544405d11070b9411100d054042d150341e80c11503038001c1c02005502000d1951603d0414401d9031000000d142c00000000f4078003462409059450641c0e5550300c9941d01d0b0304200400304000d008030b41d81c2103034040e010002015440750034002c08039600615103030b6040c406c2001000d880c00514600c2041102e0740007000c0f0780304420464200750010a0b20f5090746e02c1000c2038588117800e80c00100414400100c510860100c20060342c0504012a5031050030b10110004405607001c0305218a000181001264903004603075101c5030203882d80c01c00381d40a50384001031190518004132070540150351507104004060b64800c2e0030b258003400400d400e2017040c484001c01400e0b070003055511414010701e40c101d03495031102080304007015004011b003401144020b103840e41e15011a4460318032940b10300300780744190505c02010b807840b842d07000000c0000140707000080c0700541a881001d0050040c9203e011442d40024000402400031980b00c2c104098600c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 639025170 1250 639023920 639023947
    0x503010e060a2405010e040e0d03060311060705060106050304060b100509090f07081909140d0f020c010806041a031e070602010b06220b0301150801050121020c010f0908 74
    0x1110356190000c42c00303110b00340a6524201c140c2e41a04c100b80f0b0105840b50707141d00800c0050924101511311481201c00e000507003545500f1200c2542c1c03103001d400d42182d035200c007805558000e4150003892600400014802284100061a48980254804a10011031802140701c110595001c180020400181128182131684589030404210a00e680300f03850720100050003060b000d002e642c034100307420f11004401c0d02c20390003075022950081c1d415112020b000d20b50b160b42e030a07a5580300002c591040203076203110707002241442c84908107840b03440300c955981003040000c00c1c00b031781d05420501e1094941c05c2c51ba04d0410116608400782901c090450607000701d010701c0d0840a0f84040304580c1800081280b0f5100c2c0015583c01d082031565203002829050b0b0f07020780c40c800640103004540d502000016409805036155080c07090192292901644c88030011540c1c00b070004807150140700d40002c00c0149041560007403022800b0b0b50000a1444005408102916141901590711070004145031901100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 639026420 1250 639025170 639025181
    0xe13050f0a0c0f02100f0f11190f080c0a0c060f2405060d050408120c0d060515030f040302160803090906040501060c1203020909160f050405010c14070503010e060a 72
    0x140d401d0044030100803003c002d640b1100029210b50003611240b04041d940d68a4002d4000483d1107003013031000c140340c215016030313a400011010340074091211901d0261406001c1004da8014a6901d180b2103030395480c05501258000240c1c081040400c00076500440c0716480741c81010340309582c0110b0348074404552550b808004507014001140c1d100e0b01080313960364035030883d02c2c00020030388040742c19a19070070041e4107406419580d54459801c80308001d802c405050080c59800680b040400504c0c0c0c0310828020001c0c201d44c4008801031041000c035030804894000ca42d4058801e10440310885154030300300e08803008a90000c0310aa00100300f01400b8a0092841c9520803401e4030104041e600d0090000c1042d20b1040000d00110620040003803054440e804440425201400d00e850711b040161f190b07030130b81c0391050904000404c008058204c0e103105608640c201c82059680c104d0012098983c2c0d110f03c01001103241443c0304010300001d07917481c01c1c000d070f800046060020f014285490300002007640c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 639027670 1250 639026420 639026441
    0x70f060c200a0c0b1903091e030807120501030b010e0a06050a0f03140609030f0a020309090c09040f0e0303071d10020a05060702010c051806070b0a0b100c0c03030e13050f0a 76
    0x15030900200c410005c030001e10481900c402d24003c2503080f806c0c10400c00032070090440543d16a014110b4906058005008500403850355640d10900441c44001804489081c00001c4c180c1810500400455007100212600401c2e4882c001540d15a034030000b41c403690f003961010202010076a01003080c011641c0f0081e901501c480040c00d84da06d00b80140c1171b2a4410700150101e0000e010a4003c4201e100700250f6440c03003800707845159107007007603140300e4025000340610394490341c200700c80154906060f0090320345003030782c0c0300c000c40c04c40c0c03a84002924440c0514041404000f13140c084120300d556242c42c844112000c94004c0e0001c40e00c036091250a002c0c0c0148084203583c101003c86900320790240c22181007003000e2915a21a00c404000038542e4846c440021b8110104007050021204440d844121b088000312a2000b010b0054034080e10407298104000d06100e0b00100b082001c2030080296a00e480401403903600b1108441c0c61000c1202e805640100c4000d03c89405c20245001a01c04d901404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 639028776 1106 639027670 639027689
    0x108030403120f020c04050606091e040612050309090a0f0914060a0b0a0902030606070807140714030a141906150b070f060c200a0c 58
    0x2a003290209507507880c0118100c4000600402d000d20b580c0c0901e4000e080d407000024204001804010205034101804102c10000381d81d03819401c039401e081244c001603903c892801400210790054002c840801440089640440e00010941d00b03070002c11210041c070b03940c846241e00041d00c100f41c0760708403c1e07041590413010003001c0e059106611254904450065403903506450594651608181d00300c1c45c2807409002c030280c0c54004550010024003854030388a6295101d003850360045038251032600c60174108905280003441940e00030840100c001d2580503000000076221558500000e04500307411a100c60414000d00c8040740a40d408402d90346049000d04015014205040240745040500e11010402e02c01c5030701500d119513005010041004699960703800200300030450003003030009041082c042d0891100307041d1042c410703400142c0808000c503e03010880095a40044030328 = true := by decide +kernel

theorem cover : BRFrame.Cov 638848920 639028776 := by
  have h0 := BRFrame.cov_init 638848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 638848920 ≤ n) (h2 : n < 639028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
