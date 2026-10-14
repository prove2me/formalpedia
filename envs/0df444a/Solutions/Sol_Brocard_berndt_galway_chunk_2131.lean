-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2131
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:44:28.306009+00:00
-- url     : https://prove2.me/submissions/e21acd79-4da5-4dab-a116-345bfca55ceb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 383093525 ≤ n < 383273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 383094775 1250 383093525 383093537
    0x60501020c06070b060a0f090902011209030903031d040501030602030f0c120c0306120616020f0304060c020d0201020f0727020703120e0f0d030219080f0705220b071101 74
    0xe1007525548216582e0981140090144d61140d40c0007a001502c20390004410721401d040c0850000c407250700440c5164402d0300d40841051070a18a60156144010083c1c08540d0030981000428005d082c880520a211110308125510700d00010307041314803c1e082610381540c0801000040308400601030340090702004c07007900f0f200c0288241d10000c0e5005100b035040d120040042141921840b1220000b103070500140d0342c1d14582855140200428000080c0040c4141080745a1140f008000c907000e4030226903460800c00d003160248600c8115800c012030441c4131f4903454682c0d1403001d104000103000c5441040306410302041d001d0303d440a49034598400c040c0304118032000660050101c10002c198140301080484944244904101c4009480902402042d14418865a1550040030307565108600c1210031080800b00300d6056404850065003100c42c54040780b101d90090020308541070400084d110503030410001300846a09030350bc903419403080407980e081040825000101001e40a1a10f1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 383096025 1250 383094775 383094793
    0x315040c06110a081b0d14090409050a050312100f0f050f040603080a0903030810030201091205102307032009030f250e070c060c03140a05010906050102 67
    0x66500c41981c8034a000b8807404080c00c80305000b041c072500f2030031600301941340d8030340070940004203208500c010001305900410904445803402100084190b00300303110120f0502c0c603008140700003000010010b4845229401c20503000840410040450002901440c652030800035254115000c00384c20040c090461180c00340651001701031888226407044604107080410b6401150062005400180c0032001c0007901d8150147c01c0011901120300c603030b035005042d603908484541410180d00000340080c3c40d61030704000c0703401840720910b5100d0040f070640e00351b01c40300111101200c202d114501140012610014a10211250001e43c0304c1e0703482c02d0a000340c0251100c0250580c1b031103403002c042c010380491010345a440802150003820070f08003c0700d208850540646110300718403102003840a0038201c0209252250300700c424041d21458840d1202c48030720790348640207060007600c0b0b0400c2655a0f4186076034800d007692000c2c012803041100003070950400c1c1130801555943d800c554195881001c1e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 383097275 1250 383096025 383096033
    0x2e2309010e060601031802090403031d150610110d0e12010b0f01050a0504030816112b020402120f07080109060602030f07170301060e09070f0c11060c010c080105031504 74
    0x10991040f000d29000130080c80c0c400e001a102c4a0a030006500403007824204001c040c1c040c1e124011303000d140503c001004c09150740c0507035509104ca01c0c9105181e00403000c40d013642054880208480c4c0e180c20644190b212401d8041d00c1e00380c071a141c45c0c2c00201c100c81f03800b0260070035101e20004035000e4002409848070500c0461803880000906c14100708001131600a0b140c03041341598091603022414541c0e500220005544406104409a484031102540104603240c290701002d80c05290305078102c46604103907075104a1503d41d80042c0e07000394007000b80c003031400c01754103070b041c49010b14015070309440c24241c0004101c214141c006605240c680001800900e400005803140b41031101000c03951450036141c09005041000100c004030394001c00040703003d0350460300d0307099607080503610001c49a468600456003080074100300c03000b1400ba07000300b030085008017500901d52301024024a261aa50106e05400c49440700b0603038001030090740040c00185428003011880c41040b840a40c440d040c01d0300c0f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 383098525 1250 383097275 383097283
    0x50915060304031409100207081203040c0b03070c06050a0903030e030c1f02120408040603150f09021815070c120b0f07020c060a0305150109082e2309010e 68
    0x260510144e06800d40b04855080c0840c4c000003006050441c3c0c500b80030301d01070341d50302050046502c98003034940794815041e082410780b481940c0003a030250583d4074050400d45c00360310241c40c44c000c004004111901040e0300b801118005d084610300010412081e04000b01100c9a030940a542a0001c101c4d001050300009000c041c01c181840080580074030024050000f031141507041d80c04140c0324000c11003400070400192003100d92540302409190240c10030002509043d0040c1d0b003400746525828400c40c0d680780c0c0a460502501465000d0b09064800080c000d4000d410b0038410380c0c04001051400c1209410b0020000d040c4101104466440740d80d40108015004081c0521002248005a0321500c2003042c00c03016000a00603c1d582c11180200501070b00d0215402000c0a40d12041d41909503c540e00150495103407801070300c04d602e01501040c0034440040c00d00e80e585c8041c142061800240f03407250080c8170300c0d50300b2141c1051030b00d52120700f07610b0300050451031a17914182e42e62540020220f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 383099775 1250 383098525 383098531
    0x18180706081f0e0a0501030212070f35061603111b12070f030906080601090302100509120d11060708011505070b1801050105030a050a14070302030a0c0509150603 71
    0xa032104491004200602e40c2c2c0005079404080030301d50420501151001583c0001c1c140d0f40266200c01d04040c88100969603030f800b80c814031440c0000110100244c0d000c1903903012032059264000702c000c14200202482c10350306146400706c103070050010310061a1244016100c50034aa0034144004030301c0214810490181c000441504011414030707100d000c00034450600d00d95009016142c4501c2c0e05e0615811012010200700d02142507014040380d1140940102403244005070740e01070580d429a03080c0012003c40484200a100381402001100d680b0900b01c0c1c0700384000c4000070024070a04842c01410a03a500324010000e8204a00780100268802102c034155103c030342c64549d6800c0f0f8000100c502d0312403500050008a47d140620072001c0d194403003860702c080500024045a6210002c00d502d81140d0200141564016000e110000702258400c0e1085100d0106036411643d0b81c0e00413030309011440c1011254004120380c01d010030b04d40b0250352604503000d014030134100c1d0315000126a0324440a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 383101025 1250 383099775 383099791
    0x910030305030604021312050303072a20150306030d091a0a021f020705061b07110a0f030b0124050403140a0c080106050306150604061b021818070608 66
    0x809986c030702006500c410040a451080040300e4115040c4031751203030011f5542500082e921403c400c040c2c5483c00700b455425800c000d500d41914000c1d80c46648040102c5c0e07403408003400d85070f61001c450b41c030300100d150318001c0c500f866a0b072480c004081508080d244941034003072141034042400300c40d0304c0c1070f9070048802400400b9543d030b02c0700c0c1c00140d03d00042580500ca119202c0580315280e043c80e50041c00205100b002101c0c00c98a940400303542ca8007c1888952540109010361404151404d506550188002c0c02080d00c42c3c1e12207900038619003c5401c10b903501c03071001004001c24000c041e180d90540b0441c0c8641907480d000c1080090052041d440f02400e5001e1510000391071400501100e24a268410806110f403691006003902030310191043c98882d0081c0000a10041c0c1034481c40c0401e0400140818039041c18002d003954a0320884070400d081c002026803280050700c6c8d0240880c41d94041301c00d030820341c0c64040c012030240c85050a26210f29008000200306460b08241100e40100e19 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 383102275 1250 383101025 383101027
    0xb0603150d0807050709020408100b1302070219030506091e0607050a0e1e0a0f030f020d0c120b0f01050d0201080a0e011e140c0f04090507050f0d0b091003030503060402 74
    0x41d5040008480c0100c40b00a0190f0040030750009070024154014800ca401c0d000c251594400204400b008480c03560f0540394001c84003801c0710074200d4242d402010000d20003842e80300d40005607480440e805909070005c0b1140e80c844020b102a58008000c104516461480304400919901c0380312a140c030030140c1118180140825403403111030258020340406440944040740b000ea010480315034440038225044e011b003032030a0011561652094500080d01d8002c0040d0348030b9400c07135080c0252030351800b10030342c8c92807103440020810b80448400c04150034021000039003582004801c650b503e20041c1c2c403203031294540700300d49030060341c210784040d502041003000003840740318121a50f8007400400102c511014222801403201800540c07007541e2009900d03c038101c10356110402c48842c1e100300c94804040c88418041004104540d802103507000310a4038225040c145030619602854000d9009080c1064039803994442a042c050b08440d4031a40070030b0070400c000e15548020301075120141c4000e00441d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 383103525 1250 383102275 383102299
    0x6011701090213170703081303060e210c060c07020612070e03070905220c15050d0507051e0d0b0402040e0403030c03020f1806090306010b0d0e0a080a0315080d030209040b060315 78
    0x4400c040707034001550044018825140c80bc82034644410620940d0619401828100060703d106401600d00c00d003200d00007405540c5038502c0d114415001408126481a01000450180413030018070901420300340e04d0310604001e1a80406040c00e806400c0810741518210402201c2a01c00401c0b040d01030281c04859480d08080c100070b440e482964001721051043c1140640e101948031b0010300c95a040030300108074940311b40c241291b40d441200b04441c56010078000042109800300003d1042c2c0300394000028208160201280070380e0007070352082c00404600d0b001c10041c16018018900514100d190862030104070460f0000f1a00810134200d40070481c211a840090b12032604480082c0c800600300c409540c1e40710103940d0a6802082c00d03400a41c100b09401c801c190f0001180e044c0030b80d02101d801d042c8925103504038010100715407c55280044206d00041c01c0c5818446668101c94030750340541e8890812003400103840144409500407041041085250311207502560b06c5581c1c2105c40c1c0010031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 383104775 1250 383103525 383103547
    0x6052b0507030501020f0c0606030a03080402063403030e070f0b130e0f0103170f04060509130603060501290f0318011401030c060503040c06080601170109021317070308 74
    0x400c01d5000101030758400038410302c0f6009890003802e600ea00302021191261796850070700d03446521040300240800e1540010800520340100500302c8a80070703d00440650301c0303040160040f108070903602002d40c81d03086000403d2550500800c1c605c2e981d400300034603105151001c1d00b0b801d510f192054400045000c900c0c000c501c10b11101035001440d81180349819421f00c582d00b80840e04017840100d41c00a011440d85528800560980705880d00390348803103060502d000b005403501d9004035102940420052a10039203200d040c80741c88065030183e00001120b6042044895404507113400e451003840f035094465048070b11145c101d0398070300d032505086d6807280c882c0390714081c030400c0014103007880b5424555565605d1480c038030350504881c064004002c400b0f070703120070503282da04c810380d005002c81c00f89040a01449000c0c0401a4200e2810724061004070000251203040c42801c0c0c01800c0a660001a00d041e48800300d1940780c05026031804100a0207941a5030035030303d541d01d1000421141001c2001500c0c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 383106025 1250 383104775 383104783
    0x1a0a0509061006110c0301051504051803091c02101106070216140402040b030a050402090a05060d020405060f1905030d18180209041802010f0509030a0b0c07080a08070306052b05 78
    0x20b0013038002c0c0040c0c04e20110101800c9ca03420302c403a0103107142c200041e405c00d00d103000e080300b1440308802079071411480d05c1c140800703010581c5280a4281c0694a2140140c03600c0a000d00b0300c4884d551200e0800c0003160740b0508010010702480219400a81c25058009007902d5280031a5103a00c10643d440c2c2800b00031802900a552040055040120402070240710300c1d04200d02c01c600c201c4002040c0d45c0c0d90501c080403078501f42c40d001d401c24081c0b10154010304165021907080307400240000444e0827048001070300d00e140e600c1e00e040044844402040a82000c000c407410b0f584203414500341c103040200001c500d5a00300e100b0072881800c2c181c04000c081d0f64030b904464480d40080d0081c081070751851010128140d186004900180000d034510b0f001c03511038820781d40448000ec024009900454031a014020b0010304401903032001080303903c00081492004184c10f091035101c400a0345481c003c040d040720119030045024402c11b0100c0070711030040d0f031a400d294144600c2417184210030350510f50301d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 383107275 1250 383106025 383106043
    0xa1101030b03031c0f060807062606060a02010f0e01150e07210204050a03030801050102100b100c05030f0c0a0c08070602060712020d05190e01140a0c05071a0a050906100611 76
    0x1407506d810300206003c034010a040c8280c0d140c948800140e5915001c8181e410001807400182d94001c42003c5444c51800800904000685100115060203011148011202940f4980d1610707992401c103000e40502c2c40305080d0090090144000080c90046009482629482220804403540f840384003c0c0150b203a05a602800003c0c0000d580d0640f03c0c0f4000d060301400303009030350261050449042c100410382c01078210103200a04440703d80d281c240c9050740c642c100080c00f00c580d030000380000c5d100f032444c0a0192030041c2c0580000c00300c41001d41445100300f1082d81000b401c9403c2040113000e49030b00080d086411060500c2c1000d000c1039400080310080c0115011032100c0741c10b0a080c0500a809400306007004100d0741d0341001310b10100c1d000d20342210642ca82003540144442c002481904850303008070980941c5e400c00c607207407d140d5910b44070305402e220402a2265400014040b41155030300c60194040e10100003030100b0b0404c0e403055100031009102e1002002014528880e01800c18486210 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 383108525 1250 383107275 383107301
    0x150118060305010609080604170904020403080c03190c0c05011815021e0f0a0206090a050904080d110c060f0a1d06160915051602060307020a1101030b03031c 69
    0x4115480c0daa00401400080c454031000464130040442d00020215507240a03130b5204080342499a07150290300340300d1300110300c25503100d0741c28040040407584500003414581d142c032002d035584400e10030f00c052002c08000001801c02c62212042400110a0019802a50030034201701d01c180c4d070040b841812629168014243d05d1f00d411148140440d000641d0b00d20b10444110703202c110340301e0b00c45107a540e400c03840701004141e40305081d4100076042c141d000f0060030740c0c050046410242c0314808980b80300d44c00d44044613950b80004146040024038890902c03035100705151035280204019070140e80d90b00c0602800034010302c0300e01062409aa43c0d00c05c641000750039952516804962000c151212012291107005080c2c1e41030111680d482807900409a580c07203580c0804142c40c45030101c1d619002280100c3c00b004000040e007025a5030900554480c4485034020440e16041d450509201c251a05145051501700000309a45a801009035403400d4032002d440c880c03510b60f02151001605001400003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 383109775 1250 383108525 383108567
    0xa140f09040f0f05060303090d03030b04021b030703230301140f1c0209010e0f1b120406061d2517040803010303110f0a110f0406060503060a050a08061501 68
    0x2041402d020b0700054240028031000704407503039401d002d1584030b00c2140c601301e1b0300c0751084041d480043d0003a40032101c80301c0040c000601309125685001005075024580600f258030104100c000c00d903105440303c0440c00da0352246804800c01000d080003500060081d491a2290321061802076140c5218820310a10000c044a04100030301c01000c00e4803c0000c030503400794144400228803040000c12141c000c1d02103403071200c000e40e00e81c005c03032143e411035010021100508100b10400352046141c0140500e0140030009842071401c201c004241c3ca00c0301c10f1001000d1359002704500e0001c04e1140710f55030b00c8002000300001c00b4100d4200c0d00004020640846800c0c040c0c18441403003074143c00396050700c1c42516601c011099043d0529907407034040031601d603264080b4030460001091400600b140e400040c0c540c04090110200140030744019420620012300003004121051900702c207600002c003401e4403001d42007810808016102c001c014440c251688a0010181032030b441000010b103c60034a1140c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 383111025 1250 383109775 383109791
    0xd0c0507020d06020903070504090209070c02120102030c0d0f180308150402121b030f130218090d030b010c05070536090d111f0b030109050102040509010b0a140f0904 73
    0x34100139084149031130f01911402c7d6000c151810f15105a00c1c030560000c2c007010b107640e203602084030b002d03400100032a080100703400c0310311f00c0701000d0000d14001c6440e0b1801d952101340802003001140c0541840304203c07400d007408810346900c1d1044108040e50545040b0344a6914004651801c0861103030082d0014800a10f55280720a4604c450340920000400d4000400301c01034858110700003901c03266001c0a245002c1013101006c160404062071004e88084005481e260602003540300443d4101c0c440c0d0000f100941180e541449080c3d02940b007421f2041c2241c4103030310b500da507490a41c040c290192244450b03225a44070b0035405400c2e071a40b8042c003000d010005000307440e03005a06079030b800642c0c401d00c10a01d0405015540505200802d20300400030382919111900d18004840b032f0225405603030b491064159142802048582800b80002594561420050013031106050744859200c035010702c500c490382c1e64032050510320791007204502603c400c08480174004034426921110f92051510f940 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 383112275 1250 383111025 383111033
    0x1d041d0303040203150103020a090b040f050406090b090718020706060801090302071a0f070807032a050f0606010804020d3f0e2214090a12020a02060d0c0507020d 71
    0x1140b007107109a0580b488a4800c511342c0c0050304080c00b00030b5106e40c4078641480303988019802001c2a58000b4004034a484180c01510100c0b035060b40c05803510354840c0101400c0c0010200d0b07460b080807041380144022440c200454912174540800290b2240d0001004070501c0110f400140152249100800046145290295a80040c1d205104031a651169022040c9201c030302a60403141003224103503e8004aa0386150722940000f20440c284070310318488048100b02084880080014031201000a441ea410a2440d1007480c1400f51003030761100c1c04020b820f90b440310303541c1d4000b907064800c203968000341d103805055210040c04140340c000045041c0345001d803c000c3c0b060100f04080d4090000354405403011110b071203d503030343c443e0068095a01905401940c01b02c2c400c0d00b40c2902e800080004140c500400503500941343d494050380320742040b50611513000c114088114850004181c0c1754041d0f4007142d4140034060381d8404103030b60750460006850141040300c00e003680c02840d0800280941c54 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 383113525 1250 383112275 383112277
    0x1a0303040f0f0803070507060e1206010f1a04080a03080910020f031006020309101404080604291003151d011b0e010e04050405011407030b0910061d041d03 68
    0xc128a03500b01000c034000789625010085540d007070b030400090f01e8100e040c96000c1d620304202d8051b081d005044506414211402400010701800456071080f0b0518900a1a050550130603e801c40050100308020003d80100046c03550901d541402c0c505010780d50b40c61b815090410065400008500010340004005107201c0194420b10400d49280034454071084200d95a0007010350040e00030800105448009004035420501e8980c00400a85890380311090203041840c1503d00325142481c60942d149070407011086180c02e0805054564040c0c0390003072407000c0101042c803015003040d01d04442d100c01542d03907800000714003010264400300418440171180c02082c60780704c1e81c520b84408403103402c1c02134402d02840781d9204050795040300140302d440400004000c040c1c01110550740c3e40f03a041d556120258801c9201d4251518002100c0e2110380a002803600c004105800020a03200301f44982a003100841000b1b154094400040c012a2008500101480c8d003120104041101101740c42000001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 383114775 1250 383113525 383113529
    0xe1f0e0a14120a080610030903051b0718090204060e0f011211040c110105090111040b090420030901060801090332041509050d120f021603140607080601121a0303040f 73
    0x30324041c4e036840ca1b100045045890212000700014820460b00010016900c2d1004540049100f907a40c465600c880e005809404600c0040d006c030f403500300080941c9800d110300740c01032041c0303d6200f4062405131000703554040140550080d01c0c40c10485c1405002d071020b000381c1c0a1001810800150007801805404400d66100741c24003582000000b42075208180146001e00f11208222030815080140b4420241c0062104540160ba5580301040c0b11030504034240000ca803d00c0c5865590030903580042c20341c0c6480d0841440f50303060000c00320003c1e078000d500600000010403203590000c0c400288400101c0304075030510751001d0108002c00c0c0c02140e010700b030300110b50326207420900c01c0d0340740c0031701040c00380414000e0944a401c049081031039000700c40041100e4200d10646044007805c0410038207100780c50f00251486148444801c07000c2d88204803003504401c41d0700b0706000c14036041d00020007400c4048460310095807501c0b001c4c5001610741681003e95035004003502d0b150b80e181e000781c1003503291034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 383116025 1250 383114775 383114779
    0x80a090b01140301051602120705010f020a0c030219020901060302090607060e031314180925050109320105250209100605120c0d0e1f0e0a14120a0806 66
    0x4000410301c81b006000700c41542580b04d0300030f0000104494013241054011603002d0720a07540352841081e1044252005140303500060f11205c01442c038605000345000c1c0d081948504103194184603401682d03400404904450386890050394465030742002c1201e0b8040e02c2001030255042286100c502c081c0400944044800e05001d070350340541d45c5083c0c1d4801401c2004090b005085810401003034600c01c18140ea011403004103e0380c410680c01440c03642d0b540120074508207402d0002050205603800781781e54004203999941002141d002e40d07d00d90110119115840c040c20b0300003200f0344035901032410b450742d00740801442c5c543c0e201d04001c9415281c5110700128411150f1000086240700714902080c1034990503a0344a04000800e90a04010745029240c00140c0b030040c00781420750038181c01000311180380400a0280c04221360f054911680034188181d4080781030040f6400340c0702c00040c0012000307801014520318445140d00c02401c0c14900e80801091000000303806450700d400080c894054002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 383117275 1250 383116025 383116031
    0x1300f02040e120d05070324030303050c0408032a070b0408060a02032509210c0806011a0304020a09050103200117070804020f0a091401050f0d0201080a090b01140301 73
    0x200d0721603c1d162544010381c103100d400e10a0080420b82c541c03099901c10124140080c0c4c03101d040d100800007211511111044c5550b20700d0038410141e0500905030007500c0700c0d201500b807609141b10141c42e4010840c690f42042c0554101080030908a844640f44801c4002a0782503152a08640165684580203480c00c2d485100045071942c03442e48200d0707114040256100000401ca0b2900240144000c01d5a5003040b0001e030010a1035180001c0e40100c00c001c036894255905c5480c42d0204404903c2d6101807200d41000c00104190085c4007000350104d42a070021a5a07030f034a520004920908036000001e42a01e030070008020030000d60498555040c40c11185444d1002c1c1400440340d02c92003100301340001c8940404944c3d00343c0039185e0584c21610040481c0740e103d16201c04036050b0b48140c0c1c80b0701145a00d03410030507a401056041030b8050007040d2038070340040310070001103040096203480023410494810f0018100a81d19841040010f074030007080c01007569603101050703669245c03510147c42541703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 383118525 1250 383117275 383117291
    0x70b0a0c03030e07050f1504150c02090f0702060105130e0a0303020c0613110906030c030a06150f0806180a050111070204050a090c0b03060111030c07031707030801300f0204 76
    0xf000007035500c201e41c3d0051007500020b000714207004409152040310702407240240808a082e0703406803112000a80240c0c1e80c2040511940104544224081e0007030460415070002d014049074041402810340fa401c2d2080850701c2c10344040c040080089045a086c170b8000d0360280c404060b40f58009003100102d94085030020b4403081e940740c040c40607241000b0002e84010100c11294204080340a40c8101c0040c156030f4502c1c030880c0845c0c00c101c5040404c031242d580d07a0300c501620381e003480c1e01d480180a81c070300a190001d0404244030303aa500c0240c81c0e551020f6605490700a904c0c0204420301040740c2c0800240031130a002c000d11015a004540c08920407800e00c00040c3c0625100e208440800d5005484580503500d04920910190b00141485040000d00b0800c614000d100b0002400c403c280c44004102c03071882c50401e80390090400b10443c0214004010b03030000301c3d0344031f010700d0b041d2891884048141141c00b240c3c41e9185500800034000100082d82071014802c850171008850750003941c003801101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 383119775 1250 383118525 383118551
    0x8060403090e0c0415030204090203102405070b100b0f03070e0d021c030315120501060b070f33020309070605190509120601030b1602062205070b0a0c0303 68
    0x9401c40c2d8203034110f00107000412860140c0305002c0040d102904005103040d84a9800000766401110013603150044000d08100c1c100303181c4050b04000b9144480d4180b4913904000041c0180715064000c2e00ca84a0913000c03400324410080b405c00201114044550748900060000611760030440764a03012594016607600d25040112f2042c600e954010142881c040e803030781c14641c2454a6040a808140d030320403148140c0c40c0d5807030f600c2e0042c0400910712041d0b1310b4035150081c05d58540c0e4001c854425001c0c005040010f80c0188100d80704e03607108031182c105500300d40d1402a00c80e000102c030808040030007050203060300140c1c0214020301040e01541d010076250710703040c0c9503442800f0071354040c00111581c0b4078101784204043d003042500101809999496410b060745400c100b80c10075581000103a0a00c0a4101401c101442e081c225001400103454070b5824072443e0200d503141e2489198070702d4500401c00500740070070000340010045190700c90900b91030040c041c0100070001c8020a03c1c08408211038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 383121025 1250 383119775 383119799
    0x30702061e1501032f07060f06030b0c0307030e060f061c0b07031e0c1e08010b0a080402060702030d020105010f0b030408040501030c110a0501090221060f0601180806040309 76
    0x8a01080c180b503081440031004400804613508079945c0310403000740c00c1d2001701c0d40381d001154140003403004903200d003410306000f800c5800c90754503880921b18042041000440008140e039000441c5400c50307132203984000040d000380003808908604c6005110801c107840e50401d9555000341d0b4150350344405041441b90049501243c1c4401a02c4030f207150000070303221442a0040d11a10022030703400c11004038514074000c1600c09840c281c5000c50302c695003a02c029206010400700101c80f510304005c00e9450f10b04519014071441001d00100400140080c055444240840b42c0c0140d0103400c688484c40048402402404c080c02a041c0814070b0b114001600c903030303071390590303010343d4000c1c40041c0361900e0000190000c103131301d003502014084405200c0c1d0408005100b43d618140c011707000811000814410402c842666418001d12180c803680c08221003000011842d600c5081c049170ba00050300d4060041e141e0300c0b00c0400c0e10440d0086018046480035010a5060003030b03120342c948009546c0c680e64003440c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 383122275 1250 383121025 383121031
    0x1603060501090507080f0408031f080f010c0c0804060e06041d090c0f03030306450106140702010818010603080408100203070c0f020d0b1602070602010203010501020a0b04110402030702061e 83
    0xc1e0071880804100030803231040045411401042035030700c0400d0342461480a160f003642c0400c01c02d4100b4440c00d03240400a005058181580c1d142c410b0481c9840c0da5511010300403402002c0030407034100d001844070b869100c12030340901056103000740303050341d20b40c0e00c0348404604850503a018090891506403d0400030001d443e01c201c000c0c00b840c00c3d41e890a040c40200c607210709d104400d00c0003c200180c0d1000410030104180c400000c04c0f000e001e1042d14001880030f8040e407140080190f4003020549a10070350b0207a40c0fa80d5070918011a072a1503001c28000400244841000c041d4a010130000030004118010021207003060151050700101d44400d00490008449010100f00032000e000c00242c000800342c0d10445c40201408030600c0140c640d20908001110180443c00701c0c18801c08025804008582c0144113910082d0702c0c540c1001c0c0000d44890440790f0080440e03141d803010a040084200c403001c2007000c0984215100e00d09007000960350801540c1a14000254841c1d86104110004090b88 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 383123525 1250 383122275 383122291
    0x1305040c050d090501061203090f05090408040605030a0f1b0207210b19060312020c1e060c01020706091101090803030c0a1407020a17070e1b0705160306050109050708 73
    0x1091100b8100000054040040111640c0d541c4002c0459105200d01104203032a010381e40b00c0000c031307040c21008800d01003039400c503501c1380f0a00313020480014918400c55003601c54526045440391200c2005030050041111040262401c007482c004021240741c50004d088021035007110b1001c0d1341d1300036200b05410141c180e80342906280e9144804241c1c0d2065581c3c000310303045d40d2a250030780c00c000040100c4449030011140c4843c40c004940c001541004441074922049400500c1100c044001c0b80080003070000d550301444012590702580d120031340c103036106150400c10605c04001c1c145024804420124000c80c0401c0d1070580229959400206036072040c2c65412880d031402c011600192001020040c05001c0302100300a41c01c0143c58030000d060082030f0b41681300e1424900141c40509141d5a9005496404180401c0000c12810f850085080100a0400d140e80b102075080c12418152149880001382d884070000100308040ca80c0140d04076021210704000c251618003040750410410b94440b6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 383124775 1250 383123525 383123527
    0x504050705040b2706010f032c07030206280207080c0603040f0203030c06010e0c13031e050601060206091501080d030f0209040e0a1b031a07031805031305040c05 71
    0x2000d6418150302c0b1030043c0b80014040b546244082012040000a010340084401c0d4000140441075800c0611403991019908003801030840c8282646025004290411508041d50507c08a200401c1c084040650340103810b00c0d5844280384040c03600a4400940c8090f403861079a00c08540c10300c003040e18401e0b6510301e0090300c2c0d00d01c610001c108054102030820780da04e024242c410001a601080140f40b4100440c0140102d07600d095202c0040410040540b50414401c11404441d0390700d2080c0d013010303a640902101401d1000341c103400004592050700800f9403042c1c030700101e0656000184248240d694804880c5002d00c07040c01c0100d0340c1e00a10400c0c44581c012510b00304900d000360801b00413039a550b20f0050404403000d001030183ea00c001e481864070341298031040180716805c1c440049401d140c0d103e90408510f1a6150180789001808a80055071079802066000703109401c010000d905001d81614003c160b810400e44a030301c5544440b82c056250140050705044c240242140d0b0714007174030380c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 383126025 1250 383124775 383124779
    0x131a0d0c1503060e0f0702100c12061202030105060609180405150103050a0c0504060f0504020c0a0b0a0209011101062d0807061214090309130212041b0b040e13060902130c030f05040507 81
    0x1d23405840038940303c405203c04d00072a8006d1102c41d20400d0001c001e184070401c0c4400071030041c54210790020300700c01d029040c2000f140b122a200d90900806200742c0c01e404560650340e5003410b9007441312980c443c42d1a183c41800000900600090540c070303060007043c84e10f04155072030042104583e8580318090039031071500b10412061800390702521307001114030240d0340321070001c1c1e4668044450403170341c2071140ca40c0440c040b001941e00c4500c02a034104520001c01040c3e00b44983e001b008010860701000b60181941d01001030b03440410b4030f82c020308152080b920b4080d20b91101503c04075051040601180c5070054511010130401d40080c050140d48000d145410004c8080c00120a05800d07125a103a0702040b44100900902c0b01041c030860051005120580c841c4002e101d0200321035200103c04041031000b07003e148840f809440c4c10143c5071002021203252440d10382c0190a0468003c6c0d440f120320394807031130207030400c0c1c000c270032100c289036410000480148030100c201c0b02d05a83c00390180d4001241 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 383127275 1250 383126025 383126053
    0x11d0406120c0e010e1e180d0f030b041e021b03070c0509130209010b0d02070803010f030c0501090305070b03180303150a08160510020f030301090605131a0d0c1503060e0f0702 77
    0x66a403c942d1080c07546c0c5100c54041f5500785015011301e01200041d0394407800d2040164984102469004103c400780080c900a40f256905d07201e002c03865060060780090358805044140d000b030180780c06490b0a480d1120b00504290030891080d20400c0d016141c2c0500060180703a86008101c55142d000380000035036424610042500d401a40c20b1103045507080000102080004e13014600030030ba0880755170300c1d0740c0c03d502e0502112407907548000e05000c00d400b02440041c50200c6c07944e00752100c0c0041c854403581c5444c8a40e41c0324004003c1c883c5103000000912850702101c0200e4004d0002c01e03502841111ba0341d50015030f5885002030000c11009290300d0a108074908800c0304000901140f040b42e507030800381080c850440d17000780d1100400c56590b030700c10403160501813810030501409000410000003901c410018014400c3c1c640c920858010701000200401424558040c10b400d2401d404132584002c4064018409130084050003001113001510328130009241c5803040340c00303a000d00058621504 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 383128525 1250 383127275 383127331
    0x822030c020f2e11120f0904020406020c040b030601180e010204030605091533040f060b04030b0c0a050a110a1502030117010b011d0406120c0e010e 65
    0x4100e03032111000620001d6030340c900b0744040515501c41e080070b40c43d041c082010803d00041c42d21070414401c0e1018400400340e8003281c0b02c031240b0650411150380c0d464000b9000140d00c5018070326070b801840890041081580060b4203040c810045d2801c0149070400380815503510000d2141b98003107880014400c08500341d603085100c03441d501c480050700380b54aa40d121410307902e080302e85c07c9255100112030590502a4200c42d038210769810742004520040e0012030102c40004c0203c45003103050b5101e030b814907840e168448600d244554004100140d22620f100c8030750b0b40184401d0b0740b01da004e00003180650782c010307089074448445511071500e40909c5441c19941c07581c0034444c01040f4040c0e043c402000c5064060200b9070004200c200690707960410b0740c3c80c0c1c03c5441c010419a0260f00d400f5540758981d0f084607441c103140c420b001141d40096511400100a007070650840740303002c4c030300102c078004000582e5140826203080d01c1222005a803283c891140c030400460f0081d0b0809208841c3c0881345010300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 383129775 1250 383128525 383128547
    0x603080f0f0702040f090b0c03010617061311040503210301050f060d02031e091f0e0f01020c0102180d0804031b12030c020301060609030b041e021206010501082203 72
    0xc5642c10002c40350002800c44d255180301164240c2c0790300213982041002e24209600500b100e44160071035040c06c01c0240000e202412401c0a081c0c1700c8081035840ea1540700844d00d0130610310f81400240c002201c42c0c0c1ea0398005115a500034420078a1040780410020740341100054a203061505588ca0602000503e82c6140e0440c0c0c0c202c00308004141d40082c0c1c070300041d486064000d40104040e1030055008130100c00c0102040300d030f508412103194010245861030303070349000803290102d0381d414490181d40c1400c00c2d45200301102d602c0054041d0350300c84190042c18801000001c60700c500010707007040c01854015404000c1c0b08103802c10043c000030b1662481403143c2c10341134084800e4947c403606083e4209401540580100d20b003170311184110314090090101600d5103107080e168162071030b501d46070003e01c0600300800108120341b01c2d0101c610000c510f02c80c9150003d03d00101c404900d6001d03600e400c0c081c024540002c07000d20018040c0100340020700c003111100c001c41a030b040000d440032034090f6040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 383131025 1250 383129775 383129797
    0x109030b06040906110706060608010e0f060d0606260d090e010303050a020a0f3f0e180f07030b06090a09020d0b0a08030d0e0d081b12010e0f0603010603080f 69
    0x801511720364109150140414030f2003094002002410008003910380c80050340060305244840b420008850540701b103958000b0130a6441c60f400410314a441400392455411500d88006c103805a82080150f1948180d41400741d03d040c0d440200500300103c5a05d6864080c41c1e401480c1d0400400001c0c0c411002054003080a1064036226803003661341e81c3c09819103400503182d0011304e22040c00d070603101000e00c00039481a00c4492443c4940d0f6403086862400040c07401d02844000442210151122400040081000780c480c0407580381118000c4100031055a00c0d00000b407a20903015101d09100041b80c095403001001e894a56142c007403560041d40c40a010310003039544421000c245501c1e030b5103003840039181324030255460355211040c0104a4403500c0000720325620080c11a400150407500180c1c0040c050fa0340c01242109400d8810428410480c8446028130700c0000018405000b28982d40618220f503000304103500c600c41007500345c03019030202074141c0c402001411148840c0e4001000003c0c90 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 383132275 1250 383131025 383131031
    0xf020703020606131e05061305010807050f120607170a0504020607081b060106051e030606030105060f07080a020d1409010212090d1b0608010f080601030f0632060109030b06040906 79
    0x6140170080f107a4900b419800c031140d442e0002c1c0051441e05540383c810745c3c070070f841007048a585803240103075803550944035040c001c03c1c0c42d50101045889120305041c00c0020781c402c54203030f804c0c0520010542c42e0900018103a005869001c11b1a0b40f025025460040303400800c0035062001c20344604106a1002c401d030f114407030290003c09038964060006500800040d00c400e500d801c07074100b81e03c00020a01c2017212071220b01704100241592800305980c1540c4013a01c07142d48600e85004410160701c03034000d0180c030215020603144142580020800b550107070b11744c0d44860b00c0780701c210b60081c540650811a07002d6004403d20400d450314210240401c10707001030184c0c2c00d04a99440b1000d00c2c000300a40c40c005501c4074081809030039000100303140102000e040400c181e80c90b201c1016200e50301800000c2503030b85000f0b41c0e54288121608170a030420007500f507011120b0000d582c0c285402040b130541d442c103080003500080d41e0b580961904021a5002801d9a031a655040c041200402c0c1e180d20490358165 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 383133525 1250 383132275 383132291
    0x1f0f2105061501140a0801030f0c051507150218040c02160303020114060f03030a0507050309120c01090b091e1201020a090e01080d05090607030e1c060f02070302060613 74
    0x4410010180120200300902d00c00c020090001060300348401071011100c402000751501042e4400c018504503500030b00300081d1200c561501442d0040c075548403a030311441d0405c0000c0c00e80030315002401f92502c13a2295120305a96003401000742d00a80c4085003018010404104c1e90742020b0b04682030020301881950508411800303c0040242540c0060700107030340d10fa40e800900d8a80700806074101c2c4080320400703000741c081400240d40f0701c00d26802008100010681804000c020810340e1207800c401825003061548505c01e10b555661000d80d000e0004076203010000700c84980070110703050480f01a0050b40445041040d15880e803c1e2400c2e1150081040b0382e10b900050000e101800540803207988482d082c40c900100705a03034280c11381102d4815001181c442070207d03000800c865210000741c540b10b490704002e05040c0d072000300c203030042600710110480300c00c02e4050189800598900c035407020800c0c0281361012000300e0160100040169000038045106850002640d1541c05280b52001ca100c0f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 383134775 1250 383133525 383133533
    0xc020a09020d0c0e04050c2209020a050a0210061a0f040504020f0426100c1e0206090706030207080306011b0f06060f050d051005090c030105040b1f0f21 67
    0x10340b00400c188420380d50703840c42408140d400280400c0f950300c00c8074140b009050100a08141384505151081d0b09800c61400c600103042030b100c1c68000700b8000d01c0031911052a010040d000e540540c035108018040c0e100e20701d04c241e01d1449203e00b518a980040e0118000003071145c095680948034031412403409010006490b6914001068410080d0f0945515589005000b401c2003840440101c2c0320105007100800070240020100c3d8010741003200070900c2001d01006407507008280d61441250340c800201c5803810381d00001d03075600801c0844216001e0304d545072422022030280100042803a1010000f1501c02e40c420014908154001040d646115484d44c0c1e6044140310004000c485045c0c131703000d042081041e500000c00050000b1741e00c52420290fa903030f4440d144c01030030f5101f901d010f0303441d030105201d40810004d6480300f03880500200714a003803600300003aa03823030116001100c101c20072000040f00b0f103164444408460582602d010070740d080c0394003001c01202403d1102244c1d100d050141c4042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 383136025 1250 383134775 383134777
    0x11e080d210905061503150702030901230703170702030c0c0603070306170a03030f020906070f1104110310050a0e070c032309010215061e04020403050313090b04090b04030c020a0902 80
    0x1852501e120f240c6540105d100303150030b01021403504404405e011080201190300481154007001c4240f8241122a42c021107892801e000400020405000880c50004064200040c402c20352480040201d05aa5410003203a90f84103050b8118002d401002071031040341407400265400c00a54180454200d890f25101c2d48860780003495861103900050011090640510030381c4050011554103614258141e00490310703038030502c0801420b4000d800d05620601c1104807250005d047d0080003406800360482c280195900b0584100e444c01c60701d050006490f02e4445081004c4030940070002c030565403141340c207851503500305030180c0522100100b01d18180c8141c1c582c14000603021500540c0b140e500400091512145026840c1031004c90001c3c004151b941502c2601c01d0a80c0c2006068031000d0640484d010340295800140503100100b8124555600d040911040d646961001c200612140e07040105903245044054000f0b03d200c00030501091051625080d4240094011280103659100140c12 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 383137275 1250 383136025 383136031
    0x901080c2403090a120503010608040f020d150603021c0218180304030807060b010c050318030a050106170d0201050121020d0c0b0d0e0f150702070905011e080d21090506 74
    0x2250018030031355040200c03501000003184031915102c0e04640c1021001350001c00d0103400604901088040314007155544c51061428651105200305c0300082c07101780001030156400304a105041c546014052412060307000f43d0404d400401c201d0a042c845000840101e0024000361030154007400e1200c144042000240011489080c926661340c10504004049522301c044003070400000c403080202040c1c0c0002a240003203244040c0054400c0040700080c6000c2000c4001800c550030301200094850040140200070500c1005980764051420345c100e003280da09020303510301302202000c00c030051802c0c80969136506102416030001c0320b9a03520f4a000f441655401f41843c1e00001a4207a000201801000302171580080100040c901090490352200c0c50100f08034046504c60380021700043c401c03c440d000410034804100309958640548100807240000320341d0702400034420018a9001c002996a12140607907202244203544202503408100301d024040308184c0c0700e00c500c0c004111309011180c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 383138525 1250 383137275 383137291
    0x1b03040f0f0821040f02040f061d010306140405060a05061201091110030905030d050a060e01121205121501090f1215202104060e06060901080c2403 65
    0x5103c101901852042c24550881160303001441c00c148000111440b81c020400c90b0b045a000c2003a50440c880c01c401040280c0c4040400700720b403c2c82d404a005401b5849060380d0080d40140032001c1c4c800c250310b21803c000d5900406660042001520511103503010300e030861001400318010b00510040c0e242501e000a0007a69180340560300703a4881e207401014028601103c1c00d0500c0a42c0e440e0f120301c1d0301c070302400c2001d5103151344070382c009100904558840c1c0003900340c80b441100c60796122000514100b0101400b143c000e02c42e8a13280320414094001e0360702c002202c0c1e461094503645c00303541201d8184641d60460500c4848800858100400d11034880601000340d44285140001d04140e80050741c2180820b00d450318004100d01c20060005480e41c0000111082654607800c0490700e081c2101d102e170180d0700c41b25101040c0005c11055800043d9040000b008a600d00e844001c1005032014003881101c0481c0d1140c500d280050a1168105070380802c502c84003030f00300c0d00082000ca6079034070445600c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 383139775 1250 383138525 383138527
    0x90307120812090d090308030a090804030807050d1b0807030c06050928050d080907090204180e0106270b03120a1103031611030903070e1803031b03040f0f08 69
    0x581030310b4001d5006a80310000200405100d408904007824000c40d034000645178031400000a1414406500401c100517400342540f60b9956032820801215001044225803d000e4582c080c1e0b01980700e00c0c400c051a111034241e084443c0807503a15102503501200b400c80a00a42e400040007142c114030481c1e21034410030b0050000000c20042c00c00300d141d042d10542c44103d8404003c000032440024407240c3c00c4405041c040c40c0c0d501d948840500e01203041e40b003100312600002d4045080904114245001c140d01482440305500080c0c107a82a165140600c8107d080c0210080c0342022160765000400740c0c84200c0000c2c0c491407040802d0901e00d007502486443c6d040040d645c4503840d4401c2680d00b004004401960550404144e01a10307410b90110000401019040a1b50804400c1c07048900c5d0b81c0004044890003652040001c100800888503d90440154600303034055080201c00c03a80b085d2801c1c401a48541c800184420351a00050000d5079206804a61103000424100c003096845000300105 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 383141025 1250 383139775 383139787
    0x171005010e03012d0e030c0d031104120c0e01080f0d080703090209010b09010e0d0f02010f05041805040c0f0e04080c070f03050c092d09010f0218090c1204080903071208 74
    0x1070094891052078201c046d0f0003000900c51115011846901345505450003085e4802c40a407007150384d000b6508050801484030030721804100c1c103024803008841211040300720983ea503501064030380030b50015144a41d04001d45841a207071181d40259844511801c00154035003131500460030000c400d82140c020a5000101d00045680148000c480003500300c4448144082a6988003441c15400400038148410306042102c5103001d41c5c1580c0160100280e4041c190f0310381c50301c200151000382d409445110144e00302040c121180d08185c1e041d81c00c50349032100c0c01c0d1034071368a00c515a402614200001e025200012031080411401d6100442c0500018691107441e6810000e14240c050f200307095558829100c018042002190080001d00040e41052241c0d624440903000d44101c0d0703540d4016070b04c0081d002038003c3e05400c4403034006006440d0f030b5159644200b408591446103e48107071b81d40308440001000030305004000d04480380040c083e0303100d641d550b000350300441c041c6640c201c2d10080c000c204 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 383142275 1250 383141025 383141111
    0x403050111192f1501090908270402030a0c080f090d050903030c070f0f140a060e01110d02030d15050a05151210171518120c0d171005010e0301 63
    0x10713034050b100b0500100403460320307540c4200302803007403101e001c840754085085084503000030100c503908840b000c0c109658034609900068002e01d0300c0305480002c1307a0200086404041c1042110b441244000001c3c401c2c211116001d6803960854403201c1c0e41480100409501200288800c40080016a04d0803410a0030f00041100080803034021061884001400c56003e0b50703008030302c00407a0b9070390810350840c0c090180100c84050501710003403420300c00c50144510f416400802484090300c00da02c104000411098401070017400c41c812250b0051003000140540e103402003840241e8400d411400d882c111809001c42802d00303048854030010b242545040208050b10414440b00322650b6000d0701c80291110b00e507948810014100e05450440b445402058440400000382d80b40003a2b19201d0f258402d21081ea41c0d03488041c04000700060542004114511f01c00c0d03055806081d11101c46147c503030a00004580c03e1140c240496232545d201e401900108489051508500b0384801e20440c0f4a039030542c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 383143525 1250 383142275 383142313
    0x306050613020909010e07120c0203030105031006030209040201080c0c120d0c050c1002090609030106090203090106170601030206070c12110a060203130e070e030d050403050111192f 80
    0x78000e4840c0c01082040225a144464603040d900300a8100c481c580714090700721980445180d01410a9282041081f0035540000c0614101e035001c608660b002080b4400c06025290544030080d08001c00300003180040d0301400c4540da01801b9103e05504104240d00814a09035248003801203405002881c001004020b01402e900c0700c104c2d0900ea4a40b004184280b542c0d0307800c000814048681c0450503ca080d0303203448c01c4611103880140240b1845890744070100017035000b610016420340c64080e0000d580815694407003844a008809812580c1c616028000203621849048039407119522002ca80707007084040c242000e5000d100d0301444004003c003400140d2400e6040081994014040c00d403840b81074454075420303140c42075aa01803c1c2c0385c50070251820861100169814050b071250340300d90740c2d40907003e441207070300540080c041c80e00040b03a10259440b802009400c1100e88071144011a4044c0c401d4490119826000c90685001301000c451400441204000b69800114000c1d80c8031284007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 383144775 1250 383143525 383143549
    0xb03070902070809040b040f0204060302040e090d020a08091305070807080c0301080c0111120f0304110603010605070b060a03021009090b031207120e15070501050f0403020606010c11060403060506 86
    0x2600440c640348464a03100c079a401104c1e0001d103c3c9450380c040481c030b03480c2c54110000400100030155165911402e02501940040c007a080030b200145d0b00040380e142d4000348202c1a100c80350064010751080d506d6240b0740b54066001035400c101500d00c1c0c1b8101d26460f100d143d10624803540d0f03559450818500041c803210020b01101d0f581502032006000f50b803000b18804242280c2420b1480190151a891034200148032408004020011807814a40300056009500c42c0d0b00c0341401c2d5503440c45010400005000038000c010000344140442d0300041d03030865a80c0d410031801420302800c160341758005035520401c460400002040240c0c02c10900c10a80160045844103c010317002c075400306101d4400a024040340034207081448044100b0f5a40200d80450b40184080d00482c0702188003181c40d0199408038100319645c0d0301e050006103c80c102c0e1a081e0307014030b9160780503011907110030f001100c0c483c5c2c4880080d01e000c050003980617110341d0703031100803c0114818540884c80d85059010412080c00c05 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 383146025 1250 383144775 383144789
    0xc0406031805121b01020f030103030207090207050c060c0f060a0b040606020c0d02060a171e07030c0c170c2406010c0c0905070e100216091518020c030d0b0307 70
    0x80c510711400181c0110701c40740c060321034040c190789450381101100003503a100080b42d002d95100040a40c842d4414900440c1640e00980848001e40d5503440f090049101f100c00140c2280c005084a451b24a0310400411000c000c403822171f00f5005250030454104401551000c4c030f00383e80c440804066041600901008203624000740c182c040f0a040881c01da00c88000b4000c1c81040300090100c012030046034500001d14604101c182d083c90b0801910000320400c00081c4031945c02540000c41c0d59110380961040c14071a5034a40b54252020b42d81e9580c1095080d01d2050380c081c1c18849003080784400c03c82080d181c21072426001e4040355901690400c0e640203000b0701d0400800c88103000120310810100d0007201c0d440c40d0000782e070b90796045080715202004803c0381c0c0e0103103410500f040d015074006412420381c071281443d800320316696540c03d011900d201d01c00c081d40c40303907688003001800b0403030281c111102010741d40546025408400701e81568805150820305540c0c0e40101c4042c0e080070804d05018041c0c3c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 383147275 1250 383146025 383146061
    0xc0c180c14040302061804091b1806120204270b0f01051f080702120d2c0a030c1e1a0c1303020d0201021204140312091c08120c040603 59
    0xe540114417940702c1c4541c0080b004402c84204c0c9903946541e40300842c17154020065100c01c2900409241780403030b0314410401d800d080c42d07128210502c0944541011103015510314504000070b5424000a450f00c1d0070382981400341c840c0c1c55400d1b0041c030901c41000300d00c01c075155489480c01e42040d0200c8141a008903014010312a603070360140040100a00485a4506190440381c0d00c20b4408c0b0701d840300350440c0070100c0c02c0c04200c0200d02c2e00716412950003000381010a03164035181c0200064811030061a0740d500b0380c4419803c43c040ba0143c000c0c4404a03001c2c0b0300c010700300c50190300c1c00940c0166100040725030000307105040b0381c01405c070175089030400c018202c514504110030320340d00e1042c0078038000a881400714075408400c581c000c11244a40b114811040b50311159103000016405001c0400c140c000e004107200d2900c2c0e2090b00088680b014030083c0380c01e41880030385100e880c5210b0325120071200c5030004c004009001000e80c440034403807940c05400365039590030054002c0a440a0840380081260 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 383148525 1250 383147275 383147279
    0x70c0c0e0702062a120411010807320a0504030b010806040201120c02011d0705030c01020a0218090f0a260316030222080f0c031c0c0c180c1404 63
    0x150110303515403c2100e01c0b20b080c10700c040348041196000b11300c040104804c03400103103445240c85010309007031050b8041c506040e0112901c00055070b40c0541141c02900240e10010100601c00040000020912104000c40640b09100c1c030300c3c0030180e12160100011840206e130410802050750402405058440c0250600e418250b001812800100d02031500481c0c0b40d1003003240151003540000b01c0000c0100b4801e40010f04114031588070f0301c0134050726000303007e003480e0b428035540005199540079901404400400320365001407101c40b00d02601c1a604da005440c15800045002c018150300c41380503450b41d812403241c48100e05c80304111010303110b08240003801001106442901c0c000340340e0b599403d01680e10980d408820f40ca85140e01000f03080e14040040110702d003000080c510311600d0000d81292240c00c82c0c40700b01540c0d544130740e00c08140e07501c880c0c6092800c43e100d2201c0c01710541c8540041d103183c68031070541000c178420901c5400c07903859132071007003859180d4082c5030900c21941c044400ca1500d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 383149775 1250 383148525 383148527
    0x10c020304060e0d03030b0301091119060e1201090209090d080105010921050313030c0f0b070804090e0c12100609060807380c0d02031216090e070c0c0e07 68
    0x40c950495144c400d03c0314015640516010703404c20f12124200070000c000300c404c41d240000f601050f500b2030070f0154000c0d02004518164014408042e60601d07291a16100203c600700540540b0182102d84203548800320a0016100c04021a000d1120b1801818000e0340b0028001c15000c0305900c502e040100c0a10100003000020201c004c2c100c50702009080c001089040c501e00d18412007526030014006a1b00000901400940840a44e200320002e2071800b956001182c1d2180240030000e000800d041004202d02c6450350301034a0401456800d4840407414100001c20a00d03006601c001c40e5003200c488050160300382d115074000351100610070400c00d401e00f007500d540c80c60f45018142111015440802002540451945150b64a0403030781c282d0001c0b155880c20b0079082500303c0c80d2140314118145480707500100985102d2052000807494075a19040c0e4031043c04d503000d8102050107042d450108000e140100c18074810710741519200301e00c04c040d161031040c20f042507003d0340f240e101c0742003031040c95 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 383151025 1250 383149775 383149787
    0x70909050411031b03060c0301050f0d0501060b071220061612020a050408070905090606010309060f0501171e06070e06040e0106170c07030212030a0f06030f05010c02030406 76
    0x55261204002038a54581ca40b002d04400024038081c0c1c984110b1461107212801c843c107400389800300b6026145141c40b0290f004455000c203015060380f01d40740d954414040d042040c407004000d4015000031410325661000c0103255072228009441460f070200c3c500c0701994100c545842a16604645035038907850b20440300d5101c0401510410121001c0030041c2d141030b21609011550a00d088811580c072599140003808583c4584614142801103280008002e001031240c1d034030826103c405820b40e9560b08004500401e0300d0001242c0d01560303070b1130803800c140c0244101c5d0301900b114035180744040c007102c0c400c0340340c0b09050300c4041542d80c0303c50900b00c1c004004100650000d5030341c140345142c54a030400003111401590070181c03070068103400000714158884114010311813100010501500c5410020f000e9200c1c0381740140141e8810741190001c080e11200455105138000c800081e900c00d48204c90080d180c6c10b510a0b9503480e100707400d200c1445420f10480100d000240001c42c5054900f81c3e0180030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 383152275 1250 383151025 383151029
    0x40b0108190b0703060803040b18030601060903060b06121303080a02180409050703050a2105190804060b030706080402040b10020a0b0a14190f150e10030507180b0103050709 76
    0x74103400b820114943c2402500000040d102c0380040d02d803616140c0d6403000003031300007101150b10021200340046440c1408507000d81a0781c038030b82d00da040b214103545030000078044208085406c800e00300720500303400340c94950680c0120390160b00b62100050b01e040003001420080e0a0110103441000180e0381c260000e20600414070f02524045114106400e01a040582680c0054054001d09100c0004c2108d18012102d1082e2204100c20b00d0000002c81108d071402a03144d84040c82c0c0b125142c010501c0e0050070300e29030144c0704e42c10218402c100100403a0a03c9031070b41c40080411110001e21085190902904003003100075580c00c46100441000207588460112004c2c1544444102003804800380d81c0140d2003504503004021201d08201400d0700001d031090911240ea94078040301d4a4640340d2500510b002c0d0791443e84198102800c1040d400036504001d4680c042d00550745500200295062150310024514074400f400700c0044110640140d41e0081d01e014109803a0100300072003542c1014010301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 383153525 1250 383152275 383152283
    0x23031312020411070b090d0807080109022a010207020a120809220203010f05091014151e0403031b080417030c060c0c07090b030a0f020a031505040b010819 68
    0x8103846800458001d1040d00441003114600080c0c16040c84802441d5030700400e0200304665500051044c00c03640b03d64141c403604000340c0120010400f62010b600a00543c044100242c050490a11000c00988402410100850750003013188019490081a03e82c0200304500a0300d850204a42d20001e2511611824502c5290048041c0e104009081c2d2500040780e0240000c540e40e5844010650070890b25100341c610800740308000600c001210f04480003260301805900b810400703600108465864440c0000c5150f01c801c0c404015001d5100c0c030310881d600e55200031640d5460942c14000c110f00308a1081f010420b00724981da40000d4040d20482c1c003100c02c1c00c40c8040100109502d918118416010504114407524040c4490499040010140d03c100841140e8000344e540c04603405030354080b2080c0b54150050005003011400034500810000d03c0248003001d50307a20796071006840e04502501c00c005517602d20800040140840055003d400e000005203102140314402c204981400c80000f4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 383154775 1250 383153525 383153549
    0x8280801080c030106031707030c170d0627050705070611040503010b1002060417280201050601030c081501110304090204082407120b040e010515010f0503070302070c050a03230313 79
    0x1401d05104ad25055034103a4851505600c50182c01194141c5d0741015004c0d1140c5450100005010050209400442d600003807000000032580081400207010090810091007810882c0742e00203030f09031154119202000e88a40c0e01c0300d0419040c103013140c8003049028000c100c800f1204c840c0d1500000d42560055110180e031010199407507d614850081da00106100e4507000c50480292240c1e004801c00015143d00820003951814011410f4a0180d00840041482d003070108498816000911a00d41818103089848030389101400c0c1c59030b80039030310058409601282c00d01080d0800d0180012502100c00300802941e18525005110b6001404140c18042210f405007030700e0601e1303080b52054490082c41081246031806c01a4040c01c000c4072140410b00080301c40c01c000f0b601444450071003a40d0b5075a031070b0a550f00d500d4160001d602041b002d598008040070001440d0740c0d05040200550321401c9040c0810090381414000c035a0340548100e4150002e00441030044513445c88201120034000c22a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 383156025 1250 383154775 383154787
    0xe0c0a0b04090e03040b120403020d0e060d020c01090f120f0203120a0504031701121103030f0a0807020c03011a03010c090b0a03020706020c1204080d080402030a08280801080c0301060317 82
    0x1c1c3d46148500c0d8006446060040740f0718100b242c542e048640b256000e07400b0ba554040200b0412156a05a51800c940c000000e100000140103903134081c00c50300400b800005002c0385039440e0040c1c84050a075040312140424010721710410380c810105003036140c040c0003c3d401e29040140d03002418130000e200c0340c56250784800290615125200848144000ea0012442561038004855000c00c50701d00c10b499020650303800462a0500001312143c65001200c0c15040840003003044401c0c0c03001070221340441c400d518201015a800380304e050368410b03450034041300c02810038040c9420b48804849803018002a000c041040319542011207d401c4054900144e40c0c000600d0440028003844100b2207051148403924045c03c2c1c1144014020f689030304045800c02c2c0a00002242d940f04120380c0290075801040072580059100406070070221807081748411000c0381e12034002c0c03d40e801140080005100f00d001004861410b00841c40c021009600902c451403e54843d4078232003918207071400074040c1c000341c6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 383157275 1250 383156025 383156051
    0x1511060411030316050705041104053106061e05120f0a020f04081e0a050d031508150403080702070303080f040c32040c20030c0d030e0c0a0b0409 64
    0x844131401c61080200801610038180103903034007003e0055034080d0385009040300c0c00f01d1800c41a42c0c100c850041c00c00084070580903150307806c2c89480415114000040ca02001c1d1400c03140120406420141d642507500c245d04503c89111014141c10034003440000c002c050b036040c80ca071005a9000c01460550640d07900c0d914540b000a202d40f40202c034401d08040f501068010000c1041c8211250710311302400c98080c1c00000d00e0300c90541c142c0082c00c546c00095206a0036019400030344402010b19280807880d669004a182003040340e244071584e001e130f01800c000070180c01c659002d4000c000d40c40284800341c1150380c05001900c001d06840054084140081c0c200500007030680094114041c0401c0d0035498640c42032401c61030350714001c2e404680f02a0030001400c00f032040420f10401a560b24101c00c210302c244680c001c2d1b0b002280500c50104024100c11480204026405072501c1d550001d0f4500c521420242400c0e0407094583c0300300600c4108000e214a92420340d42940c10640780003c5152402c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 383158525 1250 383157275 383157277
    0x40f06110c0d020d03140912061f0f060315050402041e0902030903040302012a120809011a0402090409060203180610080c1201140717061005160606090203010305010615110604110303 80
    0x1c0c0f01b035001d40c440a40b402080d230f004ca580e0f03004d5103000c262240b2128030b1200c10020204a40901b44034248540070800441d13100c0c0c3c000540200710b404428142940304c80c045010303a80641c01a46c02062883c0a012610541c0001300c030003031082c00c0046046041c080d82d507d03100d1250748000380c1006040c0d43d401001b03180d180c03507226a2407190400f4003c07114203417500c4461400042c5440020459400016810a4060240103081070010780a5034a00000508001c025041540138039002660f031030303684002600c103200450264421420000740385191207031507481d1a43c010650801005819400c000c5281c0014041c0440c50b01201c10284011108401c07600506641800b60740460f114414000c849030481c2c1a407449c102440500d00d0141d45038000e100e00804d010729000300007581081078040c15100801c20000342403003500c2c04120940d4400f403d0069030001e03081a54140d41d244420000c4e0321380501c211540800e5400c0141c40c0400d03409203a600c6800041014000d003582c100c0b14021a54248 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 383159775 1250 383158525 383158537
    0x5121c0c170d06030b0c0703021509010207050d081902040b0a1b05010504060209010f08070c0b0c0f0705070e01080a0c0302130204030f060b09010b0405130c05040f06110c0d020d0314 80
    0x21041c0703502c4916014500e0301400c01e03031105607a0300c81803002042540540314111811b9a0700b640080c0100305560581c1c1d001000e0042c43c41015560030b001c20400900d003481500c1400c000c0e81d079803062606003500d5524103100b40c02004641b84d0310400040044015078030640c3d4801296081440c100556040300042040d900c400040c40381d480e000030481042841da001e0088948280d0380c0c03860301b140300ca805480035130b4169030440114601d007002000045001ca002c540c00b4130704002c814145076030000c00c500b40b600b060b40100e07010380121f4400d00c00440840c0f00300d401800c1050081c541e4000d00d885041003002a4000640908000041c40341c0c1c08a95404a8008641c485040398400300715040c54002400c40354480c5120b0350302c000c0009100c000341c00c25074054620042113001070b03c41c070f4000100105052403c660038081c0c1440005920662101e03124014074460302c03030010707480014800340d0400e5080380220307210f640c6000c28000035803074901a0780505941414100c403a100ca00c0e2003140140114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 383161025 1250 383159775 383159813
    0xc021c02030f0f041e0305030d05091e10050907050607110d0c0e0a141e0a0902100801080c01020303010b0f0d0b09090705040b0d03020a12050702130605121c0c 70
    0x24035980d000000400400440e074100030382042c080b00280e1700c5542120310b8030010304076030300600005460070400c2c0d20050700b299141040720816a000c10a03910f4039034030b00ba41100c02e90402280106a5034480c0241a800b10103103010b050b5103070406001400c50f01485401070140c0d08100c0c102c24036502c5240c0f40f4103141d43c00c41042443d45550b00c0e41c2c44940c800880e000441e0504040024200040d005c0a141c000d1260342290340c01c014034645c8044210200034411942140c440fa0008007503220100e0401003c03c01da81c41509540c104860f0919102c02d814026046600810040044999400c146c070005c030742f82e10803565125412041700002c0c20300010001c0c0c0c8040640180700792040c0020326101180e006071014070401e00c01e030040001840000001070051381100c0c40e6080064802c2511204908440c10f1590401341c464010031520b640081c64000c030301d0307603852081c0480e151000d0092140384041e0014110b01212800c48a11802c0c9400c0500c1032108a68071002044481c00c2e01e10391070541 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 383162275 1250 383161025 383161027
    0xc01050c0316231201080f0a050c0105090f040911031b01080c18030708010209010e010c08030604090311010c020d080c07032705060d05042f09061309140d030c021c02030f 75
    0x301124840b140004e2245007031b540f042500111a91002041000300345400030040c0c000c207528200196256070026048030313804030310826a0460f40d559881082d614030300403140b400900385080b0505141c48507844074641c6819901d11400d0091382d0007140541c2c44103c1c514007035102d07100c1000000880c541c50100c980e00d0b004800c80030903800300550192081c18802d03650390803402100001503603512007000010342540d10030000146213007090f8114805261007031800002c1c2d001e0604529003103400b124190801a000b0981051003558491b01e46a0021602d41d109407810f02d0b0f0307582c050104140c90103010b0b10b111000c2103440d1204820b42c1c041e4010f01c4003034100e5940320107210005008090495044138200e50720307103049101000c0c50845440002082c0300a0030507002c07160800c000103000900f02c1d50b020401c03403c07541c0201158091043c440d407056240300720390340301d900300c4600b40040c0719465801c0615001d031000020303074001410310b18009494090160071402c000c040f42548960f103e80300c01900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 383163525 1250 383162275 383162287
    0x30c030318240e0303040609170f0304110105030606030609180f030409060821130f03060b010801090c020a0611041517090a0b150f04110c01050c031623 67
    0xb03203000750b100d10089100c2c60107001d03002c28618a002ca482004049007103034400e1002a001a4041e444221654003802540c108080302c100d601e05180c3c44110006d040e01c901109020400c075200079244071710003090030031500314540500400c2c2c2e5800000d05141c8038000da800420081d510f256181d62440e541e003025184082c03001607002b9034075071040c460482c0312450000e00007409a00070680e55210b0b80144600040d1a0711b000d641411508090003240c0785c000d61510015400344401c3d118401144545004900d0a501000161108005074000c001060400c10103458071507020a00e12034107640080001106240c000000401d4002d0382c02185180c1c00c8485207601d106d800c02e11400444044448036400e641d61202820f45505106c84010040280d4001064034154035400303289071810702803c0f01078899400d43c0010306541c0b00d1103141003001c0300084d20003503010f400e01031140d00c4140c5141d802e156040c410701658045101d00d00250410451906501c0c00b60528010081080200301e0900d403200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 383164775 1250 383163525 383163533
    0x210219030c080a0b010f080a030c1a1905060a06080610050d020315030708030412080901120c03150603020f0708030601140d1d1b060a021e030703030b09090a030c030318 74
    0x6050840f060324940822400041d05550000c0001c1c01d40300204081e24030706803155002c2d11410071b00c0c0e10895207500c203500300510044802450368800c825080b4007021800080d1151000c403000034101600071305c2c0420080c000c09410041141e0003903410f49084070000c3c00800c007101d9501540003000c000ca4000020b200000380b00c81e1411040034000c9003030310860f6a5030400c495482c491840340880e00e02040240b60007081c0041d0181c035041c031060410302c0c004282c100c440c804170f0706802e80900c086a82d034094030030f000510500c003101405907130600b149003203891032502889d8040e2010003880c0542c000005541648904d09920074035164803101a2217490b540d0614010f0416841c640c4048041c0242d00c9441036030015445c00344541540c05141440070683c18010190b122048880039031043e107040c2a0b0503011044040319a181a201440d00c901051a008003074850017142030f40701e0408a400e11036a440c0c040f980e58007159050a02d0001c03048580b07819409007031242c0b4401404001c80e014031040c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 383166025 1250 383164775 383164783
    0x1d06060d14101d07020a03050a140309280218070203120109230f0a0509031b03190201020a02030301120f150b130c020718140705040f210219030c08 65
    0x2030b8054003214002114401c4410480f41001c9440d100141d12000501300428042d000030400c203402880c04090740d680012100704190310640b240e0004c2c0e840004c3c1c007000c0b00c0341c124141c03400c240c2103000040d40384565000955100d0314984c001e4100e07041000460441402041140c074100c10188403044190394400c400c1c0000c0c1602c149000394180d0105080c0107103500c540701903114450b0306412140c03175100d00f885039000306401060302040e032204010303c0d0b4006034424000c0f80c41c032220f0801507036a81c00c1036404841c00814511800c0c2968018800c150310181c010058a054502150300c1c600702d402c00c0d0400c031259000d02a00906801d42c0c09000c0b413034050180d080204503050545000428003407039641301040303c1100c100c40b0010380000100740003540200280408894042c4404150b4001e450803044081c02d09550483c046000042c00304144040e00e079400c0000c01c0c181c401520800740d030750306e0040d01d1107a00b040240b00b01000308401c003603090f81c030000320059500100b400c0b004e1a01e9603015070369 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 383167275 1250 383166025 383166029
    0xa0f0c020703050d0302030c071b030611090415030b010b0a0c120302180a0807060c030c05060703090525090902010c060f0b040b09101203200d091d06060d1410 70
    0x80c6002e400c09404544d40a030007200d000744510030700180707080050b4568482100d10f000300c20fa500031041c0c80c00004100e060148103011200540c45d1652251910304100440d03070102d0104107a50f001440c10004541c902c46101c0c1103c42b00b20001e035941c120702d00100c3d07034180d410301d00404051114018400d0a6490740c06081c103014206101600c5090940c00c1003850301c964420803401d41c0c00884240802840341c100c0c801841d20a05142641c00b000e0703560309041020407220580081e5540c004001401410440b8132007904c2c0842d00c0c183c10743c2030404038140c510b46500a0400c01034803034414104591246007940309080e0415810070820000c11a003202604581c0d4019100350304104200c50580380051045004016403250300d12131170715040310383c0c0440403924016018003083c2c04909164401032034150700d6407943e060240c052181d2800b0007170100240c07500b0041488020401d403e021400c4240300c19080102184c41503164448001204007602c18550520114243c00c418007400c035403401303503d01c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 383168525 1250 383167275 383167283
    0x71505070b07110c040c0210050f0f011a0a0806010c02190f14061207090b0301030b06190e042303040b0c0d020d0504350303070306240302030a0f0c020703 68
    0x4025102d2060869030381ca408503200c0c0c01ca401c4101038000a14155011904220303c90060782c0302509140190b80c1140d2089030600c0030b01001c14200401c610840f00914007400b002e80151902c1d0041c0d2003030000d075001ea44800d900380001440800c03000d038001c5104003825035004002400344680112440078a485a2240c000995040307a0046003070305003196244003000b00945694140f001c0c040115400d10006803107131080c4000c00c0004030720400703540c0045007e18081c581c4019507040200a201382d07a1002107100782c186405042c08d102001c01c03e03203807542007904140c40e044003141d00085c00003501ca03001c40380302e024072000a0005900032a84040d0a26010707650646030b0480e00c100090340c881924001c08400580100400d002801c02c50300d90401504042c49a100d14500c5030944018402644581c05d129910200800400f40e50600410000d00250000c144034000091900110709242403154004d0503008800511060031960080038248840038080c04130090110b4003944030095070100352 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 383169775 1250 383168525 383168543
    0x30a0b041109010f0e06090d0f0b07030612060c0e030709150807060e0d050c0901090b040e01090b060f12121306020f070605160203060106030218030604020306150307150507 76
    0x41c565039a0a064601c10340041c4c4840304400d22a041c04c540c07085440c902c440e171107003040c401842c0980f95401d800b11740c0c0b0310513003e4001a20241c10101603003100100a41c0816003440414003548000c8581070314901d42c003105c00700c1c15540108007610000301c0c110b146901841122000510b90025030480500586804d6011208540780c0c08801d48401303c500901000c40d400d400c3d94941c174102001c0c41e4401c18001d100b6515003083c540006119170031300b81d20440d50700d40c540624555924080c8600305020000d01d00030048544560396001a610f4001d204500c40e450300c0c0340340100342d154040009d40720ac070b4540940b207103601d5885100041d40c000821200781510303030b4180032941e41d00000c1c0c0381c081c00007810000d2200a2400743d048685900456610224654070720504005850401c8014042c1c03429407005619001002c00c0ea400b40405002e01a201c0e034408814040941c40204205400c0b14855012302440820000841c0c54484540c1c8090f041040090903090b090783c0c414041c04070316120300c0c200c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 383171025 1250 383169775 383169791
    0x60406080a0503032e06020d08070f0e040209010912082503020703080918090604150b0d02040b150f0a020c09040b06220c050d11040b030f040c0b030a0b04 68
    0x30303603500c800400100281c2c0100080340b021900100c1c2d01e07408002d40c0c05c940d41041c241c4c410310740306a03407254041c8006d41d00c42426803250720f130841043e0341e114040d0703e00269407a130740083c01484482c01c214281c0c0150303400034100b5100e9100700c000d0009000c07007810f46459840c142c40d003031016903c00745c81980110103001000c0c040707801c00360001d104242c02d5801018000d003140c03103824603a404074600650040c4140031109051380941c201038072980e00d09000d0b210902c0c0c10b041254038045a03c943e900750a2030038046688507a00c0400315039820750141c40000c1d89800e01c6c030200b40c050364113401d01c50032108042408150296910700a00c4011515800e440780407480c0350600410440541d401040000300740001201d82c10048240c00700c4e8680002c04441c022140f80c044012030b13202e100030740006140055017030390500c12406075030031170131016108501e020b00c0d0080e024504d000140000c0095000c81c00800c0c1400825210f030000780c42c0000c000c5030390f400d004810b00700410540c08181e001c0c5040000f1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 383172275 1250 383171025 383171039
    0x1d0d11090c0309060c030901090b042001050a020d0e06160f110306011d2502030d2009151e04091a010519030603140d17060604031e1406060406 63
    0x2070301e0040000030f005003441d844c0d0030030456454000070b0151290b50340c2c1300d20603000b01c0c1d44c03000114025406400d01449601e0041c4c40b10f20801c401d084a90306102040000c1301c506540013a0001c01144e59107804c04951200e1000180c203845085003010800340c090074603405010030800d140c0c01c6284249041d0b001c201c03000062645640003441192556010b0843c3c90740d00030070300300c1751641c816010441410484001588043e00401c0c410840005034400f20340c8844240d4a407050400c130701d04031400400340038200c8000014a1103a611694000e242240004141c12040c4042c0d03001c02900c04220f0301500d581c0391040c062500302c0c0c803d02c000c840c06c0c2014024105d00111000c901414182d4615142c2198011030484030407903c4038120815648800000c0419041c2e01158101c10000700900420080303040020210720a80507107100c500400400e00407070390703148000c44044075800200a0380d84003565924a80320422200083c04c0c4416035501210f81007000f09810f0712500080fa0304209085c0c403205 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 383173525 1250 383172275 383172277
    0xa05040603082d0307030f02130312020c0906150715020f0901030c0338120d03060602070807051522092f030c04080d0809010605010f08071d0d11090c 66
    0x1010f403844104201085100d4441d4122940100c10440c001d85484050800d40c15880016881038840404c158a903900d156418411103881d10012991424079040003400900000f40c00c000c10b00c20140d0024142013007200c00c40c1e0f102450b8001080c119211038042c282034a143d84009013590000c0c0c5840001c1050501034410f0494102040c4404900154400e8040d00d0b40c645120200c1c804c102e2104aa500035030340c1040f030404642540b00034207013608078003402405640c81c6420400079500b14400501052000061399000c8580481c0c1c60724100051100b5040140b043e0400e43c06800740030700d08120f040d5a204885401c40f4103445040000d080500e4404072000c40c0c20324078140004461500f100e80c0c1089001031508542c100d0105c0c0d2810ba034925249241c080b0b2050f58a0110700740e5010490382d0340f0b003032003818000c04003030034080400a4200e000038042e0b50018a10428006d02c286088503090042180007180140580b003007880a4240c280614032460306221a03224408400014550f4141a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 383174775 1250 383173525 383173597
    0x30b0901120b0a0b04150f0f120b0a05130f03050a080f16180f0f0e010602120a0c0f02030610030501060f14090405030d020f0307111c030b0a0504060308 67
    0x151035202640c03070f410308810280601c114640d50007600d443c01213980041d9040c408000303044001480101e039182401c1c1010a60040d444003645008001644000c106041501584020301003000261036665180c00000801500b501030424800310034120105a040001041c02c0d500980341d00c01e0b1a9227403d072001c840b034821120b000c4060556403d405015004007811150301c510002500505901d4040740180c450740341c0d12061542641520030403040503d910481d01400c010301c060240d4844a0032020300500c1a50100420081542460018491400905a403080d4028140c40c030908044100350742200721400240e5440d403070301c0000144074501000490855040c0d5a041c68180030130f00c20004207a000602c180c40c00e01040201d80c100a8841c8028068142201940b58617030503c020300802d101060152907403950b000541629103e5400404501280454500440d03480f901101060100ca40c5501068106007400300120400c00720f000a08094050511991640e4910300c05400100d00d0074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 383176025 1250 383174775 383174783
    0x50f0a0f0b0912060a0506010f0906020a0809040209090f0a0605010e0a0b0a050c070602160806061818010f09020405100609150912051011250f02060703030b090112 72
    0x203050801c145a0508058000b411004140044220f00701c10346078205102265501343e0307995640100442076800060400143c000d500e04001d9460030301002940e100541d1001401541c400f1400c07949903034550301102c00303925000c0c294400302c1c14048a01440c213201540d00c02034441c03d1500100301035119008614450000503c6260b0b21030ad0008030603501d61005480c50100030042101126150040203d0350051000354000c0242d0740e41000f01e042840429081042c0b603030402c806100850f503600c04545082640c21070078142c41d403108009048205c0d8510311000d003d5003800207d18810301c2503444a84803034000c0d10284103581c2d03115041c0c50b0040381390181c0c2011450008040c040c00a1409529880e030f140d074201009110340350304400960f02085101200d1907400480d100039a490f070f03402045149201441920300304000500e4038400c88404054844009680300c8001083c02400c4040c00c41454000d40329641d903250a00f001400703404400740d078500801000300005003250110059213005504 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 383177275 1250 383176025 383176049
    0x105040b0c0c0304120203010b10050403060c0503060303031621060f09090206030a090303090f14100204050a0605090a05090c03070206072f0a06020d020c012009100504080307060204050f0a 83
    0x1020900c14074404100c009a07055980c440000e030f01c9489144030f1311000c1204bd102c0039100d034510300d403405c2034509401c032503401c002092003400021b440010540c1c0d0068401300c2c468840200950341200c8400000d403882999401c40b072111100801158046010740d00641c100c0d003056500c84070502e040e10140c0c44001d4002c2820000920b940001740c3c020541c4078803e10b00403803104002d460300158002c00716000c0e81c0c1d074035443c04112410501008030404c01c203c1c80c41d095042510700b20008076410020300c2030034107010001400e200f003540c403000207402820380140f44081b039060040c0207442580080320290094401d2001003051980100c5800c3c007400c840c80740b0f4000705054103440041c20744000e44070400500c40ca0005c1c0000950714005000384c6102c0010040e11440796410450941e458802c1c15156038405080804c40c1100000031588101d00695004422600c80c5000305c0c0c45100700c1e400500140404030b81c0c3d000f009216001002110030407181040c0c3c01c1228010451000814450240c0c4404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 383178525 1250 383177275 383177279
    0x60b03040209010608090f0319020f010e0709240305011b02010b0901050d0602190e01180b030f130501020f040501120209130e03070b0f09070e07170c07020d03020105040b0c0c0304 79
    0x104c2144044e1b800040b500540e00c0e01e1582e25031161454100410200d800c0c5403140322108500e41c10420400c0c02c184280081c00303040300c2d00d01603c0d2100c01d41c1c000d2000c4583c4890307030440d54041c101303500905080c6200070100520fa40e0304000e030090644000014000003144640c0c04414414021286940c10007044481903900c0d2034208180c1810303003c0e0031240e0f0358092100303820a0000c5111061f0000c45a203840300302c403100c1d00004000c0034070122094400018240e0034414400c41c03a0560354003491038544101540c0310b0704054110300c0e81901d4002c2c9150b000050900c40c06542c54094800c9840030f13240c1d00182c85900403090180d00558402c540c10003009000c180070702b502c1e030700100428070200003903a18240050b200c40140141c22140c204132203000100340704840c002044840018410101400018100004001c0c05200e00780c46802101400740c0202e0228150f0b9130880705500c2c0c2c01050120180c41c24600a4040c003002c607001d4440100310f0000800c040c03802c10880d442c940440c0050751620b4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 383179775 1250 383178525 383178527
    0x31a070f050a12091515060522080d020319050313030c0618080705070b0c031b160312080106110a02091005030706020708010510060e06030a0906020a030e01060b030402090106 77
    0x203049182407004000ca000a80103d41100c0e03c40c0410b502e00030000510300f01c0d0341011000035140b0700d02440c81e1843c0b505404125075a0300c0011350718051301c01d08400c1140c5114582d541094915508040094000c000350605d0b4150000000c0440f00f0001c2c610030704a10407080d0541c0c0a0000f1039000021104165000000070321400305c1c00941841504c00040660740e0360b5483e21400b50701102110310000004006d424801d081201500030504070344414904981e541000d41c0328000c00c91071400050b000d41c111070000344144a1000c424203c02100911241d0302e040c08114411201c40c0b0601061964001043c3c407845038030512640580d0b10300070f0035124150360a01c400d41100410340d102d204600040401d199a0510600009000e10fa00070140c02d42000e078007508465002d070440e0040d0100110800c88143c0103911007100c107004840107912540e48d55901310103020f00c00c000400c03452000464214281e01680409034592040d03000308036451311030030004071030321095401030340c004201001003142c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 383181025 1250 383179775 383179777
    0x7110705191206240302090903041d0705040e0403050405091503030414010201060b040806091506030d0318020901090606020c030123040516060302070b06030d0c0215090d0507031a070f05 82
    0x5120311000182c00c8003c4c000703060f51400003441300615020a500810651138070500341c82c3c0101e4540007545ca41403a10741c40e420245442d00200e40300300f0044000a08040c000c1041e54010100301e001c8800e503152510b0010f016074081d0161620445202c00401d010180d0194400a8004068003e5260508012092000600910709281159220f03800459240710120207840100060700080c415810b000600c40c1c2020800803010003142000b50800c961a07800040d61450404181400070fa081c0070b00251000c03654001002a41160858000068082650344074208440550f42604c8016007000d081600361400a4110712124012001c8110907000551101e9046407144080319890095070601d908000c0e41540300030040703680840c055041c040780400c40c40e030003181280500585810b101c0c0c054150740b94090068011a49400107010001c807030300803190001e5000f4000c05d40d0820510305075541b0a613a000c00c8034403080803401c0320032443c0d080f0022400b840d21500c0d0a81c0c00c0307c1c00300703085402e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 383182275 1250 383181025 383181059
    0x80109050112051b0a121a01060807021506010e04051603180809100c1515060e01120f0204120f02040b0f180a1515090e0603030a0c02060f030711070519 67
    0x20200e04d100002440d41a26a601030b00c0f00c1c03148141f179410700c401030107200640340141d001005000740c22040008255002c40d00c840c4041c42016446001c1c1c0351000126a42e010013200e1980040c68274082c08102032a03900f00f04645c103066501171004e04410310103402203028001000708008400c1c0281c0c90f151904030150583e079004c2c2c1c0f620a2508a042e210001c6401514135405029a540c808170f0766003d948211000207092235040c8540314a8403500001c0c160412000d684406540c2d0303034524214680903404460003040380c40c0c5083c8991019080140d51040c913483c040348514a06401c038406810025091440c500d4010401050100c03603421480c0055001030201080c290341350013001c20100300708040d070082c2c0021401c8000e2219403c0c8050700c4a1890b400215062a60104102280d5030000803114011464500304840c06111310200d030080c052505d5804405102108004500743d100700030000e82d00411044900b031903501c4007440140410400c400ca10a507506c2d40a00025000f015101f0b8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 383183525 1250 383182275 383182279
    0x180402090f100c03030b03030405010f0e030c12010b04050a060305030a081305151501080c09040f02090a0b0306130204050904030318120e01020f19030e01020307060606080109050112051b 82
    0x401c448034840002c40e0b290801401c14003050000003000d0505505228403070721007909a00a503d094141000a002001d807590301c02c00b000135011740ca0701d03507840078170026003007210103407180ca00600c40864a5029090703103800c450080d403402d4005041c00c00507014010031a50400061440d0500780402140c040000030700c00e1649a207003018950015408001310400340c0d43c00b1910100504085200c000404d081c8011141041b00e0001400b141c8032441007100c111100c22240003554003100740d0310b00080d000e05000154048160080001c4404140e80110f116501c200c6034240840f1700da9202d03200300d0281c1d00a2541219101d4001030009000c0d0f4002c0e1100d00c0401031076841603005594501084105510070307030010790380c2151801e036560100f02104900c224071028000740d240510138180300d4803924402804100c503541e5002e0381c5900a10445e41020340200302402030b603481d814058003000302031040350b400516080c0001806623885812000391580300d030241a401c000310b0040e00c10110340c800015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 383184775 1250 383183525 383183539
    0x702010c08040b0d050417120604050601121e0e0a120e0604090c030b01030b0123090619020a1e080a110708030a0e030f060c1b0309220b030318040209 66
    0x200f01c450390003001d4500722021410102d55490a86407800001400c5440380a2400301800501c1c000c54001c48000d90088060301d00007010354402004030b40c80441e036000044c8072468000617109800c014510503040ca42c0d0054180000d4450054032035484940300000750400b244814003498640c80303108a10440d4100604080c14a6101d082d45422940003c00c43c00109a482001e42541c0d40c240c019414481801d080070051101c0032001002c072103820a48980095000094443d16907503a032007680e01c251800400b42484d000700c40c8000c0d5645128081c29108114441c0c604044901c2c0940c030a03011561160009060101280c001d40780801c00a001050900174604080b5009108201501c55451241e44080f88483d032001450709010300d003a142180343c0c104c20304004195581c2012030746062100072151a66200708a5040d04500800540b26400003101d01d81c280200050260b039110032542031801c10805500108140c1d69102e0340314200640781c00f0402040d5240f5299024015046002e407800c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 383186025 1250 383184775 383184779
    0x906070f0903030f050712020105090d0e06070b0a0f060f06080a0207110607020a170102070308130215070c0503070e04230d0c0c030b070c0b0106020606030c210f0615060f0702010c0804 81
    0x47c281103914060610040c0c3d90b440400207410070400007007415000e5800c0c51001e134620200403c1c024880d80710040d085120340c101050fa19801c0d41d00c9021381142402c01040030300d13221805100840d4a1b44101c0380041c1003030000c612600382a100b107404403039101d100381240c0340e010780500245800c80c003400c0e41d200c8071040d8001a0400c1d5002ca4070f4030400303440c0005030348400a190250094001620380c03a888002e80704400c00507260007408480d04146201c849403504500c1c6001c5110401039040180c25001d880c0d8002405818626010b0155103c4e10445048c880c42e0304203850031646c1c1180318a010381c8814a2440060702404882c003102d40205032a002d01622a00d450b0243c010035140c4100080180e0307000d401380640c40340380a0242040703201402c014208840060340d03424410404922800c130100a02a40b1503008504e0b081c403030308800036641540304a03840981c640e0404ca8240c801c9090032040c199036882c0c52000c465401c0085ca81c1d17030381000e4054004560740c1c040000201d41d035407030030840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 383187275 1250 383186025 383186033
    0xc2c090f0a050c01030c0e03070902091c030c1a04021f2304050a0609140616150519090305121b070c180b0f0f011b08030906070f0903030f0507 63
    0xc1ea10114000c0008080041a102c001800c480c50000107030708000c0c0740800b48101c1d9a0200c1c03a2011030303c484501603150030440002542c0c0d40c00341c3e000c0000b0f119508111404041d0800c141c442000e00500e200d8502031100181418030003011a0000e5100f404001161040b0a071040c1c0a03a000f600740c42d0030034002c0129411031040c504024810f1100041c045002c001038601803c000f4081c210a25119001a140c150000c41603004d070b02040b4402c020106440c81c410000c90907441ea0030f0b41100050343c3c580303410381d03524000345070650311207079400c00d141450105452140241140698980c1e04c1c0d9203014240740c10212403020150454030034600f0300520340d103200710f0f210241010358080c500700d001d003500c0c104901c506805002c0354040320908294140c00c40365070317948950540c68000c1d03854200c0000300707d00480da00da960781e11a080703409480c0005001d01058202031882940c01104440ca80c1d180e1400030b9501c1a507030142c0400090140d0414800680315030350802c0490f099003009401d11540f507032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 383188525 1250 383187275 383187283
    0x2030c070914010512030313050111040b031b0408070608040204020c2409120d23010909051005220309050303041211100f03021e03010906030c2c090f 66
    0x10140e52519107506010041188000300240107001c00c644102d41135050303417441c0b40c5070700000740001c000e0751400031180244030080d04016400c01c0400d144a030303115100c600050068209440c030340d81c0d0312401030a40d040655540c040f03c0a8800045c0109585860001c00315015480140204e8119800380074030301000008100507000b03070354940e0820030810860528080400e100400b422000d60216540c1055405003c0440d28808035424005c98041018054500500c50031900340d0301c2c82d041d440c00010f0001e480c0d0300a0710898400c200365194002c600c66240e096510994410541089919203103802c0c100d03074064080c40d188641071850105950758002425a00554401d000c0c1c40522079500c4104101408494102d6200f1981003d05141c1c00e14000c0450182504200c140b43d400100c2482c10b170380034000b40745108002020207580c1d41c0c40704403200190503944011100e101950402282d584e140440140d501140424241c2c12900c140005030750300c21025040039010300448994100080040c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 383189775 1250 383188525 383188529
    0x20f070e060f0a090e010b010f02010c0e0d1a09060603010b18010b03100902040915120c0314070e090a03020c0901030b04020411070203030309011d0a0b0a0213270b040506060d0c02030c07 82
    0x3000000d90800d00304009442702d5400081a000c5903d840c60004021390404082d2203080b01c00d81d02c544801051f490421010b8140d90880a03841c040039040050210780020b4961156400741c00910843e4800000d00004c80030684404030500321090050000c41b800c50040c1d81c3c8118400d905507901079803120400b0407a030041e0000f90000d030f10b41d00005400b003080040350000340f4014100e044c0400c45e945071025000694000146507020084840c41c90a00030840d1078003a0103480380408060410726446541d80c00098000c801501a00300f01603010f160a8805034100c030740066103030660341d07541e40c00c000061520800c102c45130142400714002584007040518420340048000189902c90780c4807000b0308020305001c000ea036070b21565145001508014003160030802940015071a4468242182180281600000300f080b00e552000d0f9042c1e010440c1308021107a50060400108004030140802d455085441300e800200400c41d2b001140d130b96520040101c075840c4141d0382000c622181980c1000401d03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 383191025 1250 383189775 383189801
    0x18010306030803152b02131b02070503011410030602090d0c06051308030405062712060f1b0405191703070b1e0417040902040f06020f070e060f0a09 65
    0x141c00462882d080c0302c1d4045c0660404034000200030760305401e04190300400030000a0048403c503084041901880e0003440c42000c2030007680030b10703612080300203503120027230300c1035520039820300c60b00101c03804140782002e0055450040c070600072415070b02c600c070180d400f00ca050f0350000d00d1080300c00c012821a40144d00079220650340c05a8840f40d03905114803c2c11150000040c030f4004110030010765881108407880c0c6c04000303044400b03140c25800b49840da0548000076070703000385201d03060301d09000340450714074403e2440c0c0c3c0c403004c010703252904002100050f110043c00c440c207040005102d03514212400110340c249040c1034500c0562101e0210343c0000150f00081180c0e40041111800c000380a507901c1c1e44134804003080c42d81d2040c62864004802405480038110007011503006245482c1002203034050411410103650b119a60b0b4200180c08009100314001030180142c503400039100071801c1012103017000d60103085a1100010400c503242c00c0d000d400e500040c060400a05102c990140041000d40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 383192275 1250 383191025 383191051
    0x204060f020f0106060f0e030102250c0f050a0b180406090c12050c07020d02011e23210901020c0106030c090b010504080d05160b0a0603050706050c0318010306030803 73
    0x108000603181061620b00c1c840140d06003035003400480c0d8008469030181d8003600c0c0c80103442c00401d02082c020701c1749d40c0c580041c10a141c4059200d0000028002c2c0c40b9a00c9040940c0752150303100c9807000c01d40b084c0e0103007c0d882840140304001440070040685102c16035812003000b1a414240054100c4071350b0b520000180391030b0b0020700340b400d8210400e0002801d0814003030040e85400000003407684107141c8024403401c001c43c8031405691083d410250314400700503056090960010380542181c50080301c186082138800150082c043c8460107480c42c201740c2021929011200900c400c0b2120b070000c04c2c56059640c24411014602800d0043e58011801b510301040c10f0b60030290500c0c1600d2100d44818117106040200304001400000d01007940091442e150303482e00b06650110010403502103000d00000500c1d01072140c90020f60788102e088910540c100c44401c1e5807880c09a031140606a06100d540d001402007055032041303480b40c8060345405147c009442034407542d5541c01030300251013400c50509 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 383193525 1250 383192275 383192297
    0x1e030807110d0509060a03060305060a020304050c011d0d0203011b09030501060f06091208090d052a0604030f050a0b0106080a180b06060a0309050d0f021c140309030409020406 77
    0x1421280c1510805407450103419030840d00403010b40b00b403080c15007060040000040c00e00241e813103940404003a6a00100b6110103080543c4a03034040d4009072000e0f9910301403c0f00104056001c0c1b62174061210040d1900820300321714004020511080c0c3d401030b42c01d9500c2c1c81080e40201a40c0880d0f400d0629140c82d802001821400c1060840e4016009103003000080350301880f0940c0c000b0002c8080b03441c1c80c104840c2e02c900d140380c2801e15000f59544180c01c0350700d9040000401c2070100d01c03402924184c0400848200c80c00b000d41c030440c50f040350441c2e0001c4041100b4000300706c0011580e442c89004d1800c55183c1d1043ea5135840c030040c0264403031400a140308050100405141c028a4210141c03050004a14007040d03c41008005010344010710071440010a50071345030003500101c0c0c0c1d240d005000e4a440103042280506440c025141d500014050078800c44801e800b030a00108500030144e032030361071001c80c0240e041101d51010b8402002884103200014406c03540780010070182c24107590f50011a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 383194775 1250 383193525 383193527
    0x120d03140114010207030210050c161409072f0303040b07090b0909150f03012904021603030c0c0609030f0f1d04020901170a0911120601050d1e030807 66
    0x41a040440c2d80202182141d4032680e001907164203594044981000b482c05112080d02c003441403011080c0e032805400c0e1082c6140d54003100000888500060012085081004000714050222000e0011602981340b503002c03084881a00d00107260780580f400140304200c0c2c600707403442c0c008980c112a41070a40d005c110213160f00c601104010641d00c1c401600b407031a848001050040020f2890307422007000140c0c801c82d0340e0b0303c08a808504101400802c25080e485040150f000712008260355410342c4aa02c180d402e0600e8402c4410f40300e803002000b9024071140e50110007a041d240e500800300070074400b901000c1080d40c484d49056501c248c0341c5401c0c0b20700c40c1c4405408003180c605410280b0420030510a0100404101c1c0b0b589440211001a6a00f4010006950030a0408003e000001e43c5c00700700064541c06601c0700300e840d4000c00c041c0c1001c0221000b00003200819150440a0f43c00c07a9004001e28200038500c105000d01c94028807049100100092408558855040c1c000415034800c2c8240c0c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 383196025 1250 383194775 383194811
    0x6080c0a031109220c0611070506070f020d240c171303140a030203090709021606090303060504020a08041502030105240708040b0d0b180411120d03 65
    0x5008265031034040d1a1958682140184059407114003410081c1e0000d480c4040d600700c1c2c0100b840400c0102243c084d16801e114400c0f00240c0100b03404100420030b1f5122500c00002c07124102c039801060359141c410550345061501422220490700301c440840c00d8800641400355455840300e2180603601002d480f20301d07403010b60b91603500070410302c54400805050075803102e12050b0f000019440ea586c0514003441c080301ca07400160140d580304030b008a04211340d5036143d0010360150500004865141d0b40b02d2413003808920400201025299203000b640f800a40250840040f181c000c0c1000100d0b41e03a04e01c04a01030b68421401440020080300403c4104681c032000c02900d000b030f03440c085055604110100e1205000903610000038540200c1800c0c40304204000c481d000c9a1088242c1e440319964400b09803580c0015500754180d130b040c02d01007040c5041c001440c2c030311541c0000c000c100300c0c0c0700c680b989543d84012100082d00101c4281900400f40700400140d40c005405650006080d2030345900c54001e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 383197275 1250 383196025 383196043
    0x703080c07030c02060319050703090209060613030b0c0715090b0f010302060d020c03090d050a0b010e090615040b090f06040f0501080d270b032e1e090f0608 69
    0xd402400d21200001c00d0f0300071051103000c0d40c150752007940d039220120400101312092000122240c10320302044a69039241c0c02441d0264801c0c2c1d10300c9000c1d20b54400b0040c0902802c40751444d851031340901000810400941950003c81c9030944914145040d00c5000c1c04d0320000d9000318149407503100600400a035940040c1c2d102d003800200c112154110b50014116109a02c00c1c1410309801040c0c1c2ca803100002c0c001c56244001c014403842840c0c0306803402d03c4c0c566601000c00da5040081900008509903205000d600c11101100503001c2d5580d0350200032040c045a081140e0895620b00c0340d82103544900d2481070048540024269661800340c04000540e0784c02440c502da4941001e004002081001031580c0c012001820400402145241e045405c60300c0a440010900c1c0016400152a800c41e801540684410400c40841d003ca0a01c0f01c110a0340705201c0c2101d8490550701008011400d449000002980d88842e952644d5215005011b6800f208001503034259074400402c4144007c02040c10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 383198525 1250 383197275 383197291
    0x1506030506010c03080702070f0e041403120406110c03220803070201050f0a050f030406060819120c02031006090501051309030512040602130e06010f0914010c140106030305070308 79
    0x812441e200000800807855410020b040c4007000000c1070340350b4001c1c40b2040140c07600204503c202c95a03050b5002409609682c15103020101302400da4010001200703d68500380c40c080c640c10a42c0721965400c00a1820720511111481c09028100c00c00c070050004091142e103901445512220b500e42d070307101203881c2d0b600a410135402088010010303608101071b5050740340250025500e0702c048140550301da2064031841c1e481020000100000c00400340e02100a903041d80c401c880d0201450255020f00c00b0900c02d02a020a203113101c0200d085124504803c071700352010b02541c59448050b05d03560f0594440c0d400c039103001340e00e8800510a41c2401c0240d440450050b000c10320064210b5103024210b031140403581440306e913501c0c0001d13051280c660100d03030200f280c941d2303240809a560802184d842d1070030b0714028005044140d4000b2824071440025058418207074092840500840c010350345400350300d03c122070f004c0c03d08100040b8070350f00b0320542e00203601a071122681d03042d003468010130561001700904 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 383199775 1250 383198525 383198531
    0x3060f060a08040303051515030a0204031e050c0a0f050603090a0204020a02210a0f0c14030304150513020f12010e2e02131502011e0614040603050c0f180a150603 71
    0x100d0a070f941e011501c40311004100c8c103a503685d1140002d10004c0d00c070780c0c2c001070310300c02038100d03030b1510126011420310079035024000b43c1c1d40d0001007004100342b000d400c0c403414141c031088020a010320310305000119003140000c4201c0d8940c0e042980810146d0b00015890300140c0c111118241c0c510048101169505481071409031420b0241c0380301400281c91103070303070300108000710b1310001c200990380030a5103400c0400001c490b2607241910b08400420301c0c1080c0c00342003030f003042c0c0852404c464007014113180c2c607030041103094180c007203000303100700c508540b119008a503485114021860743e003072081645060440140c50600c0b18080761b1488044081c5142c24801d0740304008001d01481c01807030f00d0003500c1a81c40071030020015554100e0141645000314003428a200d2440d00801c200f503807098046a40800f00843d501103d1406c0004a40c4c1503c4041c0150b0041d201c03038411890045e64208407410028074054148400740c40744401502c00310703102c2c81c140c0c1c0d44822104405031043d01250090946180c18 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 383201025 1250 383199775 383199811
    0x150715020c010c1803031b0f060c0f0203090a030303051b12040302010e03040806042909060412090b0d110f0f070203010f0501031113020c0313050415051503060f060a0804030305 78
    0xc4144c03c0510028040008103110580030960340c12550304015040000e1411109450501c64020700c2c1103203c0001040e51038458403201800401541c002c500000c00c0500e40600c1e6441c20b0307020707010080418503965403001607003004881c0000602007200704540010740d240f4042c0742c040e013120030451550711207a0050000b000004000500158440c1e03203d841c11800f400091900c6c0745048c0201c20700c000d0031f005807081000e4090b0000346184200c0c02411100701324001880103071b518070810301038010554001c01482d03961030701d6034000c0e159082c05941924904140d00000220700c0c1c220030108034042c68002501c2e001d620f000d0041d04000c0d1404502003040794515501c4000583c0010905e500a20349807021022030240707981955904403141041c0c0759190a51951201c0d00c000724010b00e0300c2540303445070040c14810020b00341b0341564000790118030702c089411518445a00001c21103507000481c12080794031502d508001c0d000c00d4409456280c51400d007441c01a040c0c6030010b202c13000442c041108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 383202275 1250 383201025 383201057
    0x51e040b0403050d020f0403140607180605090d05060f071202130e0405010b03061f14010203091306050d0b040b070804151a0a030b0708090a02010c02150715020c010c 73
    0x54101d580360414690760042d400d58180039000745c4103061403413840400c001080c05103d222950240801d142038038003507600d924045d00d0344510708260001d0f24020000034040640141c00a22031580024024121070240d50340d00c0780345c26000c60780300031280803203410301000980000406c4604004400c0c19414411841e0140290300007034440c4052080185c008201404002c0d4032040c03144d14090b040d50043d2800c0d0f0b8134440070021068800b8001c1c0d450400008201d103c8030105400b03140140d020350325202c0308104000c0500174034449520340b50356030507001405036035220b01d415156100e0001c4283c1443e140c00c08494040004007080140050703002004000790086444c0c0141d00052540026001106444150400c20f10050103070003922880021050101c2051002d204070043c0c1d440c0b01503030b13803548846900da080640000340822174140b075100041c43c1c516800b24001c00402c0c0d0725030404c003845e1191502800d5018900c042594001260314003544e00313000f084454012030511000058240309 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 383203525 1250 383202275 383202293
    0x1020c1c080609130b0114151201030209041415040606090203040320070914040203070f06020a02040207142a0109060e0f0303040e0c0a020d0c020105031f05060d051e04 74
    0x12100b03118a03809400108110304c80c031144c0c032403d078003d54002007940c1c440015042c5501d0b0302c20140d01c11180c5003c42c0175a840380c00102c840381070140b070301501e240c1d01c0d581c28070440d401e024008030b0300d00d072180120350070300002000b41c2d035079130001c1c052100d41d01d0415051100480d00035070006540d060040041002294110303451f0b00c084944000c44d90060036000501908081e62500048000790600a51001da50651441a801a1300850580d4240e81d514a440d24052a180c403444025802c149201005442c00f9409018142d0140c4000603111062140380d030700700030480614003200d2034120f00800e2982d010841610240d00c084c00c041151a0a180028080140038240e0a208030001c2030513a0180c3c8090081d20000d000c03c070141c0300c00e820001000c84803a042500420014445c1c4440444600d100b1049030080c0c0f41c040e120a4590380ba2150b036901c95090200801040b00010b02d000951900c8400003081114440540041e007414003404451540401403040300c4481c1c502c2c030a020118000d59 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 383204775 1250 383203525 383203531
    0x3040b040b0105064848031e0322050303090d05030d0513170a050a0e28031401060303021c02010f0f0b0405060103090809040902010507050f01020c1c08 67
    0x2e0755090700c0481c052006490742042c0803003050a40c0c0ca071001c0340720200014071008401c0744c080c41040c0f00303c1810700b49145200e0301140c20204d222591030046c40c07030102c030b460300364190b0003805444c42c1e504c014411094201c12100035a46660000035111421040b899061000d9181400000f9285107400000303640d82c054a001c0c284141c00b62082d41c01049030030400c4a50a40b0b00d44024801031032314001d0b84c1450040b0039000d031620342e20380c40c075602440e40e0304003190110a100c0e00c90300c0c1440c546100464800328103000040c0c20060050100c030000021a0368810810002e10300105004c1c00e40c94190405004402c8180180e81404410310001741c01081c010310140d005020007506030340380d0760201c4c013401e070b4001c0074042d15103800303100c00d200c42c6c09400094141d2030544040c4400e071100001181220071240d0040d0003140180428141c074501500301c3d0204600500d400c90400d030494880e503042c100d40400049207603500240c8003e1101d001d00054181134a01e00c07403003080d5031054a02138603d03a801 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 383206025 1250 383204775 383204827
    0x6130519020f1003090b09010b011202030126010b0a1403010b010908100e151303030b03030307091502010204050301050c030105010e01180b1c1505010201052d07020109020603040b040b010506 84
    0x2440e95403c03510f11944c0010400c0da0080728040d190300344503120354020009035407011300180310104001076450084c000c80b030407101c4020749034aa001d4101c2d9424084e40361140030302441d540301c617401205540d4141075a00508444c10119140240316402c241c00c4a9071400c3c0c4505200c61407500304403010000c10b404104001c021004100000510001402c0003000801d400d1043d80120610204645008641141318030a4608011550707003101095600e000071200e0307400080c40e03508140412002e00050340c5994503603000142c01c150311140001d095807001c1700c0c0904007407001f2004004035a0300c02c0c82540c02d00e200f0700f00b414456200c5a8211040e402c20302460081d40000100146201d9080c80703094400340311000100201d000b50f4a6a0385140f041d489510300560805e00454201d254a140c60740c000d05d145042928030862080034510301c040000c121800350b558030842003025840b100c004501c01c511510559890307142500e080e003106030040c0c000b24010f82091208120f420403d4900280c0c144034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 383207275 1250 383206025 383206039
    0x120c04050405071508070305010603020424020f120705070e010b0d0b011803080315010201060f090e01061e081b060307030b1207080106051e011b0309050306130519020f 74
    0x141d4101545008115030120980000a40c0c0940455520410b42d500411142d0380030300c2540d07a5100114240c2c0075030701981c01440921441e010186440d24001042d04110b401a218050000340e8801e0510505200c010724002000895a040200c180801e2000e80801110f880c41541440a54251802203900000d1015074403007a801c0b46038000d010b8103222480105600f00c0741d5440703181c01515600700f514100c404280310000846250b00600401c42030b502c0c800c04000c0349915194030b10340030341109070505046550700c2c98040343c400709540481c503440082c0d1120141481c5071802051400304040305513031149030700340c80d000070a03038410040781e810110509d40070581215400020740101d156101040c02c40c422442c4c00038074100d040d001082150380440c0d02c100c2c108808041d03600d220140b000d500340028070060301c80c0c01700c500040c1812200d50103440c1c140381d4540c0300c1c4c000c646014400e80d91000d031090186515820854200100e4290b1085014400f01021843d40420150b1031000c88142c41201 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 383208525 1250 383207275 383207281
    0xb1201050d06020702060a1101180201050a05071104020a03021309020a080f0402010509100908010c05070c0e2806090507230c01091b030c1a090907030603020d051b120c0405 76
    0x31941c0540700b0413030f0001c3c603d87d90317080c04500c090011603001d000c800351542080c01c151172012a0a044070030b001c1e0180c40e980c0c542a814801110b90740d00031541112030403425460701c0c1c000c5e244c1d40301030b00c400300341070324016034a0b24424180140200303640d11000c13030741380100b0155160607880315043e904043d01543c2d108050301c0b144011f0394a40500031280b50480003503007041031b503964099401401c80b0100320013080051341c5181c2c00c40d194404c3c0080034103050102c00c0200b207590350b41c52400d580032031440b21101c07109401701500d500d004911603040c036502c0d80300d1100703014000440c480d003034202d404c60900c0040914400c80110030b4440f2840b020b003004401107030440ca1080d007034000b58103095010856811600b0090840002c0b85d4450000381d40c43c05001034003142800c1010680321190288040700d500304520041000b20301c00c0024542400c0580740c003400401610ba586c1c40c0c013020b92146c0d020303040c60750900b492054180c028910062003586050b50840b80100086066041c0c1d1009580c0443c541d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 383209775 1250 383208525 383208533
    0xf0d0207030e04150e060d03020303060d050717010e07060804020d060c1407060e10020307020601091a100f11010c050403060f091e06050903031605070311060106030905070b1201050d 80
    0x18541d8100b94002c0d08190441d40080800c85000c0d0580700c100704c9241981c0c46140a00116000b2104001c2c0584c0c820000300d40303149025880c16105034881e10031142400d8581c03042c1680401d070540d0040e03103a9115014808221400d00008016002c580b07000406498990001020040310090191000d80c0d200000d00c1c440340300381e50000c0c10081c01d0f0b031055641c2c401403800b40b0041440d407943d45081d0080845121280701d150085a00584041d4010304041e420680703540000d2803901509680c1d039005100b074080700e8955854080750540192281d040510302444050b003800c090341e0440b811a45010304a218076500402598140c94018100188102c03103620024010480c0c600003a10342c0900d00244841a842c0720803001d0510710601c0c0503c403c1d2500600540d1343d02040e903614200d00b2122a06100040c85480900000740c041d10b402c11921007290501818518280c000b0400079407900105001d21504014590061044c22085490140c54240111508070180612842194600c003507030140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 383211025 1250 383209775 383209787
    0x122104030509040509070e13060b0d020a0302150d0c050301090e0601080607050a03090c17120705060a11210105120307080412140715030e0102030411041d190c0b0f0d020703 76
    0x41c2c0001100b01c07c1500304849143c4084881000c216242c0d410840d4500c20350425028549030107a02030f0218011908560800c0820442c01c00ca00c1070b403107000e1100e0481040c407405040080394007519501e540b541046800001c0d105030810b804c2c8158011070040040e0000015000e60010300e07448e0a035116001c019044005d09050000540400240c000100310b01c800c4070b0b0205c403a41000021140e610501103403141e405d01608034041e01580018000802c001ca841e080000c1d41012190020702d02100b608106607803190044100c1e000d04401001403206041c02d00c610001e0246420045060886960720781d511446070303008108052250300c001e5010420184039a00c07205044406541c211a01c815250313040003912060300c40000d0808a0469055206200712400f40343c002d9401c059041da810700340400313450351400c0c5905d0f00d0b01400b05542c940300107010b0000041a0b4040d000082c107a58100221902a150400d001c144400c000301c00c9614500e004841e600d400d142070240e04e8480c203007000c1d00d113 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 383212275 1250 383211025 383211029
    0x11a060a030b0d060204060806030601030f1101031e290609400b0103060806060f190b0301080c010f0914061207110d0f09090b1212210403050904050907 67
    0xf0703849001d041c0c100300032500a0820b07104180d680031101c1e03641f402059a01e040a10000e084e144480811001049200701c88006082c8113040118810402c410303510290318100c4c0c0e811401d1a03807410049a25a0440c9280a0300c881484c00101103c1d45280040c03070350f10a100803c2e108410309000300809003038901030b1034041095142c4040c4126000d42860b5004800f600f00c85c0d00d440c1c0740013000e1400790f0280c4140c1055440d880024020769841b40300340400d81e130400341d809074807540306800706198074040c2c0300c00b0001d808001e6240f80c0b01c2d454818010301e4200d41e08034140c140aa000b907409041c0303902524030022140c00b00e085004080b40103002c12444e220b41505440002c0140040098054200c04414a464180b8080701d01d0f030b405001c000c4070070310810041d903000128004410004040c01c1d4003d81c1c401000103050b100004000001146040746541c180c0da01258080b4048525202d500c0c46041e025054114400c2ea038900380c0c0d002003443c402e00000e148a80d50f41e2000c20380b2003408105880c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 383213525 1250 383212275 383212279
    0x20318010e060f090d090312020a0606230a0503060601210903030b0f030105010b0a030902060d02040311090903030106050d020a0c0c0e100911090d081207030603020f03011a060a030b 80
    0xd00451021650703210041103030380c3e0b01d500b52940080f44508600180d0f50b94000350564079501458110f58a080342c0c904072110342000c52040c14a0080807a60b00d10940c801040c8105140b182500800a131384040c0c0001c008261284d442140104243e8070080f602c19880102407034002c140000c003c0ca04114208030b4091a9001445c0050b04030030181c06520082650b10120303096511810000b04043c02e03608240a00c6001080070300c00000e445009400100256100922941c201214021103d00320b0b002035000707560a100b198401c0c034a03800c00340711071a00040c2131800b5516540c14100d02509902c1b58410311800e25900080d52032450f0700c0b440c3c0903100c0e01c3c0d100403840f81c480c1d9102c800c00380940090b01c000d402d44011010018a1410a01c90402d0f5540000f803624145611001040020a90303a2000c0d82d07030040401600701d0421b45c140340e00d840380c7c446441c00034203a815070041c090800c2040103010700a81c90420341d008008142100d501c07030301c14110b030040d42c0c8081c0c0d0030089015001c174400e556 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 383214775 1250 383213525 383213531
    0x21030a09090b0a150c14031206030a050c010815090f1f08030a080c09030105041211030405030703020f0a150206150603070203070b061504032306072c210d05040b0d02031801 76
    0x1800422002c001403914614441c00f0511a44501040ad030301c4034170300500140141e1001000001950040114a5015041899a8100f480140c01142c0c1803102251f920b039041a0314410040d50700c049440e82300242c203140325980844e46c21700307903240da99101d40d10901d014007144400142408100004451030803c02030024032080c1042d18244110716244040100400d1071280c40100b1600300205503030032900000e0080170340a04d181c00707001c00283c68491842e0821000040401d03001c03051006028a070000d81c0c001c20300c07132602d1003002e040d03407000d42c00d05881040d04105102d0b0041d400000c0d41e80c6290012985100e036181c201c00074590900d1500d07016942c00003c1000000d1040c100c01501c0d11551401c0070024141d0580071261701c4800484600010807002c002c071240c4290703c3ca060994135861001070703451052041c0c00007040041e00820b01000810698414030f0400c0c000e010340034800000f410f110b401c003410a164100340780a4804000c207450303400f10000d010018090304030400000302400030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 383216025 1250 383214775 383214803
    0xf0e220506040c0e0d06050c09040603031e09030b0a020a030f0c05130806010b040b070501020403020d11180702060105060c0a1a060306130209040602030621030a09090b0a150c 77
    0x26200880714603120b01d1a0140d0355905070700070711802a44040003003112515504540d40da0000f44000b50401d44154020301551589448074800c0002650080d06c802c600f40c004071000b00034800c4011340c00d03000c0010501d41000050f03501d5504035040440b0603c0561079080c8040110000c00301c3c040d0402e42c01c0d040104090f0082d03003001c000d050320008010981682c544514010f907440d64203105004940310b04000c2008118050000b80580500c50400581303065503d07000500319035100d04042e200b5103070b05170781c85900c5c0c0341c554003a039882d134020060b0501c60718200d4070294907901d051141c1d9010f200c002880b10107181085c001900075035408890500b1000005100950346441160303860f00a1160001190030050b10810588138580e00612200c150394881e0740340c0010b500090032103070b00b1294680c21a10002001e00c50a404c419156004688840d010709008200207410390180303a003146410403040650300d850040e04142c23015440e003410040c141c00d20445d0f241c010120f010349448084210 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 383217275 1250 383216025 383216089
    0x3020a0c0b030105100504030503030402010503132405070f0c140115080d03110c2805031c0501050d0f1205120108010b09010f1d0901021b070e070206070f0e 69
    0x346044c3c41003620350076400d0920080a580c503108a00024040754000c0c8001001984100019070303000c1650700c03244188454507559441c0950020a14050403560342000d681d00c800c003071103515884551460201040b203201c071806040b41850034006401103103480c80c902c0040d1000d4004c41e1540340c000080e003220b503545100300d03600c0d100c0201034400000c0c1440800a9102400380070354600c55031a402801e07042040c1440a80c0c1216070a034200002541e20300f1040c0495828030290443c2800e0243c40504801c0c80000f41049031f04c160007061064110400300000f103400c803c4101d0241d50b00440411001001000903101400b4921044818001d2440041842d034410f401c2420511029038035210580d032618003500582c03c1c1c60050040303003050035007880300c030010150712150088441e01c001071504104407284040090038450040d40c0350301a613400c011414170407001d82da1000d260301c00751140b0704042030700506d902cac904c01844c41048214525014960f8032100601c030640141291010800f0080e05 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 383218525 1250 383217275 383217277
    0x30c0228031422051302040f060e0117040302061801061211030c0d0503040f0608130f02120717070e070f1214250c081c060e0114030d05190c03020a0c0b 67
    0x1101d00440c41090301d900da0b4202030091f2020f0b10201440407828a0074110122421583c05d0070344c5e030401500d1075204140705c00101d4001d020f80e0099025180c40e240c50040742c1c1e4480d00340400318141d6031401608102c0c840b44440420103040d401410040090614800213180606a04005501076500180703c410007100000030000c45901041802055603030b641c0c1074a16210441c0c02098244031a180100000d1014600584640c0f00421040c050821a2b62042c40c0c0b60b80b5030006841600540c05003a2016002c002070801400751034022103951402000051524000b031032440c06000d495030f004090640c0310341010000b800c299054182c140f0306041901084040040007900901040400801103841501c1110000d40c00140151501e141c4454101a43c070001c0d288a141654988000c1002c1d0382c4804c0e014000c2105920400014910108142c28013000c4648481440300c200141c0940f5602c0005e01110051f07a400c1800030380300503090507810181c2041e001031611201030800719075801904 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 383219775 1250 383218525 383218529
    0x603030206070c020306071103120c03070e030705150309030d050703290901150210050a020408070b04030c0e101e0608070c08030103082503030c0228031422 69
    0x54201d452035201d0701d000b80c840c034480780c001942540000c4001340030380f8090900c80001c3c00e490b0044074500541440800004502520440e42c031200020a10045942c01040300000070307401c4020745086460a80062591000300705076040955020001403d40d950900075134950040c601400e000510741404028001e0603c4d00313486c0c4201c00c151100e44000000e4891000c0fa401c00a01004c10a9083c1240c2280410b040d000c551301b10b110300c000071002e000040c01030f28015550a44096202d506207110076061102580010914140901c403c0010a42d031062078021960104000e031495210010610004030b4180c10040c03012060742818881000b039034070490101d90702907403644d440b41ca40080894401c1c4586402814051080c0010b00c007040e1428001c04500c0ea4000420b110410031181424072052461000d0740442e075200e2201e080681c044c80080c0303030380105c1c000c252582400203122206078048010060108410320036000b010a0400f001c8901a444c10124005c9904038000f07441c4e4a12a14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 383221025 1250 383219775 383219777
    0x4110706020a1d09072007060503160e06071203021312020a0e060d11030106030b0106050a08310507170307020f090c0301030f080f1c0b032a011e03060303 68
    0x240c0501002403800f40261070440c020118100c0740c030f60480854000094403403400d100e52043c00507442420041110000420b001d4541544900c0e00d0b200090220348054a550140300c0042225a0b071941c0d41802c9900c096031140910074a91640c40c42100240140481805072054984001c01e6407840034140300c21403407080320101c00490302c5105c0c0041e049003d8070519009031110a40340001070300b41e030318112090009400001d080341e981e190045940303800e07030146010500024202c20322550010b001a80003509c0080c2580c88404440e06400b1550038035002d10b000000c2000d04810414203201e4a030040854804000d0742d4400050b8654030f0341d111b05400c0f4070601d18444140003d04110604a11450040c0d2205007542c0ca141c984c911390a1480b202190248000c202a401a08610001d0141441400e0070403c5224202681238121010080300520a511078548581c51100341c80700c3c1e007180d0656041c0c48a007269040010b032100c0002165500407440c11144406c0030640c143d005000712802 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 383222275 1250 383221025 383221037
    0xa0f030f09092c0a020303030c0f0f03070807020d170604051906090204150309020906120f030c030d05011202090121050703060e12070b0403200303070305041401020f090f04110706020a 81
    0x1a0518244d42d5000d1010094141c0c209100040400d80940080d002c0c40c140000e009240c50200b00d50000154411560f0502040e0340800740840590304101c500c03022250740c01c10300d041a140c0c07810481440e50050015104a40710340000c7c0440d1080201a004558101018882c1c1600c1d05140d401a410500451503548a0302e01c0d5075509920900980c164590094441c00d419100d003014428014002c0c00395a030203100d560345100c95120100002d01c41402c605001e55100ca58542c1c0e01310940e40180d12116500200c203045002690351f04941504482c20100041ca41c240746003800c1c0a2600011000780860181140020500a4940045030211a204155040980700e82031030400c2e07006850303010380008161000200028011910b0203042441e40b001064030050301c4d045540b1b1a0b000b1604040000c0d251800e00c4100150400c01e0031410a4440081d818102c0e0600d48007094011201d0080c03003181c07008804e0300c1e503031907685c03208801c1c1c0c181441d4070740c0d0f80c9441d0600e4000b03544100c20715000504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 383223525 1250 383222275 383222351
    0x15080f0f0f1504060f060b0a0801180c020c040b010318080705010506010908070e09070e01080c01080919060504020609181008010204060903060b12011a030f0a0f030f0909 75
    0x100101e00e29008520b40c030041d10003601c940c0c9422005150800001803015610300c0041200341064019281d1185140d03a1000c40358109542498180d240180315120642088145a201e90b00400c43d070320040826200002e2000000004034007611405100c082c1a5a149603c54144048500103101083c0900d00074030550310f42500440380c803466846503207080d801c502c106000c1484c004822030f4100615100315081c05460396240c02404030203a1250b561544902c465034140d50b08801180e41c0181520302a1642c0742082d198139490f0311011400800d0503680394005400c65031103500751052500050580190000841261890a0f4040e00ca983e0703c41c00a190004414505000320f40541e0455569421458510b5813240d024152134150300740e1001c4002c41e51040311703101f41b04a407482c200344102d1246140f02da070306040c20000d2042c0c8403560b42e0003c16007007000c00c03118003041c0c000c45c0d41440c21040c2d01c401c00c0e904030f54001c06a0007e150b01e03801c002142c1d110480c1d202601c4070520b01e520001450f10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 383224775 1250 383223525 383223553
    0x90912160b0f2a041a04090b0d020619110f0708070f0303050d0b1c062f030c09030a050f07030b01091a01030b0109080a0605220b0a15080f0f 62
    0x10481e02c025840b81100010001040c1d4140c298943c040e0030301c10242010340303c00c1c224a5044d4004100040654041020071150540340101010800151500c13a0841c3c005d40104410340f065011491400d0035080540c2e500718868502000214603c1003039a401031906140d081e21003515100b8136205120b84440859600c0803c0e950a04076541615030f1840d00468a60602c0a0300140810355400041215058508554007181190152040d40c000800f40d1802003114001c60740d00c15100480758a041c90440c01d40e10000c116504000d00345503c0e0b803289401700c006440c0403a0140001c1440c06a000003801c00d00000840b002900c0c07240ca0301c281d45a0701c90004104444042d0340305004070340401d11000342035000c0d50181c104040185002c50b00076880f4040745151801d10001101d01e16560b10401035071a840c444424403000680e00d91000034940e50310380680a44000d40302200d00380d45d410108011010b881d10000060903c0000e444400201c0b5520584440c40f44c20b86d051b60f0b000b507030b100c04154 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 383226025 1250 383224775 383224801
    0xc03160b100b030f0f040c0e040303060612060503070302040f02090a030501020304020301110a020606220c0e030601080c06030c03060d0b041a0f070f0c0c0308310f05090912160b 78
    0x75508031002400e44d503441c03052035540020013a00958001210302d401090680d0422000c81c407541c002c3d140440c1c1d50385028801440603401d0041218507900d4100e040c0504d5402160754011a50122400304050078981c0040009209084800b54891050040001040307010340195218500850081140009001c43c2108500c030b004038040058004100084441c40e080104154aa0804003040c0222030040c0203182110b581d10a507001040e2101300448003850104a0180584a1440649010000b40c2c0100d0320368013001d03221814982c4048001361040e1a10038050040c103400901000d040e04103810300d40c02071412001c11008070320440300059403910243ca4154001d082a9480141c05c1c604800c0c12100000f642000b140d4800110b2000000309000710f0240900d00c502c6a030012410000d00c0c40d0343c0d01006807038030401403a407091804200341d5080d80c0402e000c0711800d4070a44d9050790303a034400c94284901a80104055500841c114580211000513008614801d14280e10fa82d01c4490b014003c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 383227275 1250 383226025 383226031
    0x3070c0c06260a240e060a120b090118110102060a090b01050607020613060926070b0703030222061b120c0201110a0305030601090e0708010b0c03160b100b03 69
    0x601c0c00c54081075900c2c40782912a48603072040c1d4001410461044140340e84c1d481c00c49040072007911918140300203511140c1c45500104101d07010804540740c2100080035401e25840500306000b82d1001803a82d4000707411880e0701c000f80740711040c0d000300d003803400070302100c04071001d140103214042c0080c02481841c0f1030323a440030f80c025041c2d0000d0b03880c050420519a2003200c007280c000c00c0a200c081c2401c9490001000580b03456156040324900303000780a0b2543d110022a240218511040b50640c0c00d40841c1040550340600d01c00b9a60b403040d4101a00a0710510348064000f6175100e100c000401c0744d490620302a21210350f00d82000a810ba040d0401d00e40d0103040143c4480c25000c0d000405a0103812001c0c8010700c18100805081820200703141400d200a03000d9010420004c104107041da032080c0100040c06198802c5034040c100b0f0480200102414001e514200000140100e40644200295542d248440c1c00e040908001480d000031812400e4074442440010302da80440d1000401041e80e01c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 383228525 1250 383227275 383227307
    0x6010c031707030212070315050603070c0b0f070206070c1a100b0307030f0c050c070b070c1a0405130207051c1101060906031703010302100c060f052d100612020c0303070c0c06 77
    0x3c1c0c8e80e041100f0004103500203454803090041c01c10301080024401c0c0e611034407a802e8045486940d18042102a050103401000c0f0010404140130910000d5101c94140700201d002c6903000007195902600c0d440d4011240d0040c0c281e1400c040100040c60358942c2141401d0344000000340200012004180c0d01380c0142d1400c201e03030f60418901803140c5018280540410f0340150b0300521034075500c1c001c445141c8040b102004000b80002414040c07410316040307a505841e81c034001185415803a031a869100c01c105c1030302022402500b401d0455092148114041800d02080204003040e603e0411400074007013403204849808092030404140e4142005507070480350007034400c1c0540030381d0500403111581036004c2160701c6551100842c0300b4841c80d2050a114089404c1c1404910035110105d101e80d0011900c45903da8011001f04484400050b042c83c08031501e504101918442c000c401101034040d4007000943d038403010080000c1103512100811056001c0c9a15111f50758070b4103070807281c000107600b03008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 383229775 1250 383228525 383228561
    0x3041202211b03070615090b01091d090c042d021305090a09060207030507140708071404060306240806010608041103032715040e06010c0317070302120703 68
    0xa1442d0201c9412040788021015240340041d01d9560404032021080510340c0d00160540c284424617003803250b0101c00d0400d090000d07a051502c95005c0009004170000350b0130800034030118007c21010420420103841c0188140080c01184d800031102d400c40d0100760010382031180080e102419a4400c071241c8204140c03840c030169042ca0207200c27400741c000e000c41017025a0381c4901d50214440b80b014101540c07095441d16540d80b0349003410f803440d030b988228100f11074005034410403020ba000600c0408861f81420300305040340c014000200100201d5101820442c1002d0400c280d05031800c03421000c00e0010b140e0410707116101e04649680b40000d024410125402e8808140803500b0606206591040101201d1402c81001e00010740c00c4111238003049007009c8980d140710640b4100b01da12181c00380c1c82854504143c9041a890315840c0042c104030b05011555041500749440b03501c5400f81004a0f110018240c1400d00005000b94454912400140382600109862500c01c0c0214800031201046407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 383231025 1250 383229775 383229787
    0x20c060411030304080604080a09091503110a03050304030501060501030c050a02153304060501020d08011202060f0703050909181015080703081201060e0a1404110304120221 76
    0x5480c150030541d00a0b07600d03100c107200c001030003038007004001d1180d0b1168006a0326035106980c042d00040c42c5421a0505034103124901c1c07004208152424220f039009403241042d101d00c0c0300030600703120031508064414040001c02009100054105d28100c8000f039a080040e82282031f800c0340d143c000c4900f810b00581042c14403046000b9480e02e0346e5041079140341c0c8034a805070b03406200950810003024920002070360000301d4030341d89400e21580340108403c0c0043c200c070300c451400080200005004614941e1031040f04402076407102c030f05841a0f0700030090500d80e070b075025007005002c6803c04601d540c81960342000040081800c12500308499030504000e059944140c3c42c01300c003a2902c92140c07904589441c0c0c000903241c40800002008602458403e569072010004000d60300c40143c01540a108000c003100030680c458141d420308a0704010b043c0c815542212000501910600400382c48401d000310620040c0700b0f04901b48480d0066903022181480c02403103c12090070343c1c5607032a02c0401d0341803101c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 383232275 1250 383231025 383231033
    0x30703020306030c04020406020607081602030f030a320a02040b0702040507110d0c03021b150a020309030109030525050d030f060f03050d0f021204030f05101b02010f020c0604 77
    0x285410030b5008090f920b001d862040803401726086940501d0040c0c3c00031051211658022078a0f03500a60b0000d05c1c0c0154042c2854040c4d66441441008c0c8640f140000003d000600030b54448d4043d03456100790640099402000c121900640000d01142c41c6d8038080031440e50b040707074400c560880b140c40410905103100d5400b040002e2000500b1001031000000c0c0c0c00b415588107201c424004e00303207a25501a001154203000b0700d00744860300340e0b200742220302c51005080e03980c140c140c0212035070f4400300d21b55904d01038000301d0541c061800708941640c20107481908058114024110703031107540c4108250301040e0255441d100c4000900176015410008013800c18038404c0e0014030000d9040940807511699601c0c0e0b50890070201c1d401940d040d0002c5025000d00d40d4800d5521140c0c3d5134a100038440264034a103000c0442c411440024508000d200d03000040003002c0c0080102101d50700c00400115042c2c0144400f0702052404810055103421b91700604035141348251044426500f0040c105540c40303a43d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 383233525 1250 383232275 383232277
    0x1507050712141f1103040209060d051f020a1103070b07050313050a060c0318030e040519020a020a02120a2303040b0705010b010f14071203020c0312060a05040b0603070302 75
    0x1006507045420702072002482c0004102d00401480c2d8400020449101d40280c081100c051085a080640c0100140005a5074048100e508034804444007403014280386001440c000a1070341c1802c3c20107182d06c10b12454005540940340900d0940c403403003c00c20040410644a00c60f024000b400c0003000000700d004144034401560f44000c0e02503203800204035548425141c51400c200440b80551203140380840e45a05024018003040c0040c18041c0d0010641d5010780642185c03291503000755582c0c40062151080c12203881801d4206900465445417078210080d00c43d088600e05074081e4040160980b00b4403000101016807540142c456130000d100d400c004011607031847d0032021248000e10011a04c2014040202406407158000003819429040058140104201440d052020700b4401c21401004d000448080c40da00070710001e54560f0000041d4000c0c041d032556491144008100e12041010100a55010301422543c40c11881c0e516001c00007522030600046401c44000e2000c28644c40c000d030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 383234775 1250 383233525 383233559
    0x20041802120114090c01122a091805010f090b010804060e010b220501080304080a0f020f04060f0e0603010501060f0c0611130305071406040608040f0209040b0105120f33100515070507 80
    0x118281c07034201c0cad030f401100001c0d02507217003a09003c03540ca00041121144156010300100303610307407040c01031103800f10019010340c0700144080d02182d101d40009202480a601659a0f1440240b0100b0f5a0514101916210f4070700c009040c0d40a00e02000461030540c008141c0e022204103c0c000c1c48610f00079030300c2c800a58400c0100300d03004030780700010403281c0d9194000c14000e00b0b4502c144103408d03494210b034880700c24005085075000340d2603c4010f01240d50b005598520310b80f200c1c00d14880e01c0101d0725040004104100c9441345235030000c125007484400b17000200084034040c508a541d034980390401300028075072083c01d00350301c26001c005c104050303400360f07001c00d5000e400394502e05110b4100c0d8001c251404021102207404070400c0d0018406460f060400d4138130b0f4072030b040003032050100c640000ca82da01b2507410700c410303131105201e00460458024a07411305440b1680c4503103125800c0c2100702c2d1002404a0090510481030702d0405400e80c100c120580b2041034109000f49480c929017012840041c40d40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 383236025 1250 383234775 383234777
    0x6100611030c10021905070201020c1c02090403031b110d0804230a0614060108010b0d0b12031b0609071806080a20041802120114090c01122a 62
    0x9018084044400f44060b100404149502507961000f41c1002006202c06001e800d0a00800384070450140c1da00081c6070382c2d04541a940401000c00d1958120498808241c0081d8440a29030070001011b5050300032217001d0061048180c841c00c20110152658000c64040d50003d90041d5110080300344200c20403038000c2e0040802008154154401459942510340b4440c0594414107005080000c1441039074080300303030080c0100e2142003d00c002400024103202d18a1203040110703c13109908440e40c095402d03443c00620310f0815012541160f6141d40184141c007030506000d50030800076174004030b00d45105a0207440a40041411300003024004420b00001110269079010042a43d4104000403104580607081c00540c481822040440000400500c0780c040d5040981c00c1c161043c02c84c0c61900810f50460301c607041140518032490045c2a03500e18103602140311420f21482c03200119280241000a81c0c0d2400e60b00d01640150083d12505c610f0403030080c000c5c4003102c0d031519040d02226004512 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 383237275 1250 383236025 383236027
    0x2103090509041a010e06030604240207060b03060606040b0a0f0c0c0303030f0c1d042712020114040209130218010602031213080901050d18110108090610061103 70
    0x25000032801c0810111400c40e45181d40c0c000540080c82072904140c010451020021461320b000000f2940314000500000c0419071403600c10b04015105100d0704134030501900007192610b01c141000c102030000c01090700d009004480211348607003440c204072420346001c00382a070700d4001c4040c01242c40780d00c01c241c550b00f00300030920307514001188150803200546c0203030340c042080040d01d00060f00720f500032110700d0140f1084cc8255101c00d91400c40078107403403104a6001640c050707141500c071546015a480c0e5043c0d02d05185009003040782d600c03d9205000400e40c0200a040b007500c0b40c1090320901690042d521030f0846000850020a42c461081c1c0a03102030100501e900020145516489003038208101517013000c696a442611140b40700d0750b0000d4030320200c05121000361100c00c4a07202e43c0100504100740000c00700c0c120b2039250445118104420304240b460081070821149440c10391f11982d00081038003001c04c29040c2c00091041c090031003508000c0740640303011f4040d103c2401b019001c18240c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 383238525 1250 383237275 383237279
    0x120901110616050d021621080105010813150510030b150a180b120318010e0a03061d100b01080c0c06010b0903010b0a09051b0a090510030e06130309090204210309 71
    0x50380c10310501581f0701c101c41124540300041050030381c0700d55402a0408000a80c1d004000503a84411003076081440c00901080c07021040c00d200541c8481c00101c0d00e140303070410050000c0e81480c441070b0000c80e4001c4162115075210b5503840081c502d0549416644000d4004041c804100084000b2030b20303411030f101c0080c422581d64046034000c00240c01d800318913000405c0300300c050240c56003102070350b10007443c006030320f41b0490000420703a6102d800080c10b40750f5165044003e043c000141003600e145d202048480a10480d00d61030040c20f0500511400242c1c00000300d81307a0001802914484022040945282e82c24041488510b130400d0344650360540d01e50602c001540c0b2004a054040c100740700c404250b910700780111000e00c3c00710040c84055001c003080b50102c5564800d001c40c068400446500d000d060403030000700e000c0c1c90030b490540010701558041c00142d2201c0380e0423020051090b200c40e0040c1d9a20072103a0220300541c4281f41a000840b00b00e5001c1c90f104003202d024092003810f02248040d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 383239775 1250 383238525 383238547
    0x516090513270506070306060503040b1005060c070305070501050322171c06060e1008070903020405070302030702070609060e09060a030501020c0d030e01020307140705010e120901110616050d02 85
    0x32146002200342c10360b0840c0c2c00248042481640c0d030042090505000f19481d02d0300040c4184001000a40f000409002081e040c010007400140180700040c0780988076018026466294000d52000701e5140c4110300b00051154010f00550788210f4012005100724400140107040d150800c00003240c1c4040c01c0e5941c05001701511019100799030895032441c2c035a480c0c00302600c085030840e40055050048410600429941e03036190320320107031aa03181c0007199845d0000c00f0b842002441e000254418140780070481c00caa410307405107101c0c070742560031680465036424054450718403900a00001600200080c056810600b090350342082c0068a6100c1140d6242c98031800ca800498400441c1e420050f24403901d01d0341070142526010114000b10f203036040030040580451088400740140d540040380d07900c00c0c40420361108400180e120195400b12400c0c004601c0d465121080e07442c0450000f00c10722660a0340001e105100e07040740c1d90b0000b012050043d0070307546030304192251100140c0800010f034550f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 383241025 1250 383239775 383239811
    0xb04140f030d0603111903140f010f0b090609100b1e04090204030b010b030114010309031815020d081b0309071a12060d11060903072102040516090513 66
    0x2400b07200c000090250451804842031301c0c520044520406550429458002c00c5902a070304580d485034061210003854506c6500f0041200c2480d282940b03400702e0112418080c0d0071030581c0e5142100e18801c2707907a0b80c0b400c0005105007510360015100404d0381c1071000e0444140200300e0258060a5840201105000038035154015005520081e4020404004011b08645028050080f000503a03080d9030405807a25001e40c10300c5202c504068480c0d03084000e00d4000c2405411680c500300b00311020a84440c52400c404024003034004c0140300780180000b079644100030450103454081072840e0701c107030f02c0028504035030009005000f05002d0114001502d800717030503200919542010440791078200d410720f01140214000c04503402200882c101070f0005906141c0c13030305460021100c0c03075190040325011a10f8000c040e00100040e24002500c0c011043d864103503070b503030288205e03010300150391003a200307025a181182104021441e20760b400d10440c0381a02c00011091401c0c1000200058958025082 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 383242275 1250 383241025 383241037
    0x21f0206180a1b090b1e010c03140c070e09010903020a0f02010e1206190b01020d12021b06160519080703200d0c0206060a0303030209040b030312090601080a0b04140f03 74
    0x140c65014010000d904881c000c80300102021100c1e041c075980b03108281440200807820700d60400101c12100010507003e04018140e04404101090301c442c00040e50503a00c100c00c1c024906c1001c370780300c001030905005005120750103905501030b2a4044041c0d403031907181d8442201c200e06100c21007281008984039a41071808105403500201181d0621020585000c1124400b04c21420704250021a05036000143e400a111003440d10848403808169120001c2c0180355030250f615001c030200150510b000030b17413140641030200c06680200c01808040d2a148a4001c1561954081205200c0128090300981d580f1010b00d08000c103001e18000700f100c48020303900e8265298941c02081c2c003070801c14540314000c41c10020f40014409418040001455a40e21b03210083c01c01d500043e1100c07140d120740d04800b4640101904881e280c03056081c0082200b64100d441007818441c00000084141000545151054100108000603122500c0708841c004400e500d03c000d40c070559035500e485050420080c04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 383243525 1250 383242275 383242313
    0x120a1710031b0e010506160803070c1722050d0b0703090803100e060108010e0604090f050f060618070c1e0210110d090e06040b011107060507021f0206180a 68
    0x10b000c5060000036001c40d0b0b01a00083c0c0510028000030000c20003000140c2e4003141c100030019225036407110b04840c4079215a03801000113010592602942003a000600408403000c0346065204007050040413500c40d040c420968800c8100e085000860202010346800405501c1e001c07800711250f80703441c16240e00c1a41c21280c04140020200401440320404940189007440d09000301e5140c00b900d44020340303000d0328851049968100b09000c02035a826400201a8840160780340521a6000700380c4849045445500030203282d40e8000e21680c603071030301c0c520802143d20390207402d500f41d440d05111040585040301c0900611000e040c013580d0391740e41c9114940e000b5a075149000e40c203480302a080840c4a1524014480c40b01814010030306c201407210381c032640076100010b6000c40c0100498a0080d018003400d05030103046008142e80c0d5000c0b000304195030090301c0c030401241d00399405410000300a280303540145c0050010a555115400745100821900001c8841c0080c5580b00d00c1c0f034005004501003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 383244775 1250 383243525 383243573
    0xf0a03141203060a064a060c0c150903120306040e0a08040306050403140c1b010f0c022e030902041413020d061b0e030105070f0504091e09030c0302120a171003 70
    0x3d040f1020103202120350000e80d14141000300400207256580c401080061107070419128240030440c1040c22f603002c3c0c00d0002c00f181d84500242c410144258010f0701d00364007541c01c1000d10401c24000003024940782c1e90000d03a151170a4a5a2250401040082c008601700120800759482e000c1c040d0000e440610300d0070010309200b00301c5500da00300d040b540424442c140a41c40c0d14183300d6641021344a01c0194040e00c8001c511000c8030504003186411440000020001003524000258943d1042900714401d03a0304100b4017141c1165045188800c441d81d048840e440d048000040c144901030340c82c554840c080200d000310822074481000341a007026400022104d1039400824075090160f150060303051304040d00050b001480042083c8114059000031540300d1007224008281080a0358104c0c4410108029025107450001d0410300e5001081d03005102c1e0740d49529015003000c1c1102d61038503143d02c5442070480318070071002100d100201004070004070188000082840000121041c81d4008010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 383246025 1250 383244775 383244887
    0x901151214070914060d09080909070c0b240f0d210905040605060a110309220c02160512010204030510050906090102040b07060b0f0a03141203060a06 66
    0x1400021943d00c00c0c0191404c1c225011215100c100c200c4211001c22007021030b55450a05003240f00e407040324805900418140b04101403654000c03042c180f01482001c1c2c489a07034940040e000c0741c5079a40c07840c45210340c4c0c2404100e031040c039001e60300000c80e00024100d48082e12540d150101c561450008818428864105c1c584a00f50300460b18005000200c4080105034148000708005005050f41c41013848a03041d1500001d0408005580c908400104882c603504602030103074501c2c5106154085c40c035810501c011a141c0c0c00424000180442c00740c0d082082481d042c104020074a44880150403554200008030200c0d4040c04004022020403202003000d040c411324151034124010030910803640305010500c0315404040440d66015080140810350010b0784000603c01d21010b06030320f81c000b80e841800401c10520140800e0740c0004c44050f65501c2e503801002000a10044030740540c8800050014050306000d698807a8468083c040011080c444c16090b03446a00d0788544c00581c40701c054865 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 383247275 1250 383246025 383246027
    0x30b01030f02040b0a03091a040501140c07050c150d290102060f04023609010510030506130302010b0d081201090605010512061210090b010e0105090115121407 70
    0xa280c08500701c4041c11031070a490200084103a0140b660b034401015120b5507004244001071044013a1015442041c0505d07081c185003c4d03008040000c0b6501d042054880041e03511004d030003d03103102d240c1080c00340218180000410074040b055004c0658000b00900800f40720b4012441290074000b01d580c076285800d0107030400903813581c4900c2c840c2c90441d40510200000c001c80d40c006560081d82c151071200f103840340d95405203804001488407854803890a0a486160058203c9481c0030301915002040607031110404901c146039907001c00b40195002d100032030002400c4459403204a80a40300004039905108000340f1140103040f0142d03905080807400c0d10390081122549801800500b008100c0d5904d4180042c101d8080e107901c3c6c1079010480000280241c03100140c0103102d115007401d69009800c50304900340240180c1500340d4407966040004150313030402c0000581a01c500511421140c0e1800c03202d078441102c2d21600d81c1c02c1040b4910810340d28546401420310340d15895a0040e410318110714 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 383248525 1250 383247275 383247281
    0x1212111905010b09060405011802131d04021224040f020a030309061101021303030f02011e0911121f0e0a0b042109120201020106210309271a030607030b0103 69
    0x42174601c11494007004000d501c5050041341780c00c6c85903000c00b50315000040d80a111650301c90303210080b4a2040154111000e091041091081d40b08454600c64000c400301c0311695001c01e001c83c203241005140d100b03c00d000c514843e2980c072512414006840550036404664010310907070040b80407680800e000e0205c2c0d034009054104601c9048000c5085c1203d0711449122440c0c544000390600043c1182c445400340300390441d005403464590403102c18032039201030300b006211032002070703500104420700303c5454500020642c0711191048004c2203001d02c803070700b815058031000341c01006803655685251546001413198021703960090f42c0505841c900750401030603600b00561a003a1144071400e0074140c880d0403181768002d44050184a0100c0c2c552840180e004103600d800c1000c5000c420105094940d20034007001c0d10951013076079440c00346640c0d080b40900368070416100310400040e15066000c620056401a801b107180c5100a81070140d1040120741800c00a68850000070f03140c1902a0b099600740c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 383249775 1250 383248525 383248531
    0x20705011d010b0a030b06061b030307020f2d030403051902010905013002160c060f0807080a020f09090a060305011d15070c1b0f1212111905010b09 65
    0x84003d005030300f00400015001c00e40c42c000146442000c0002c540309031034103c02c3d40c5058004080c034030622a21000d01c00d80d80d410454000b0010311900070040f40c16a0301141e54142d18103041e880c13100700c00c0d40d581d880714070500014203805e99110a00001000c03034010012680e001d140d1000200e40004180001801d100307958100310b0510240102c841801052200080c011000902c11001403800c680302c0c1001921442c00c003c5040000c04c10b40905002d00e01c141f01d02110b0f419245c80010f00c84c40002550301480440f05900400d00c184006500030742281c00400c6841d03603900c0a149003481c2da0000865024043d160044a5595400184200802440b8600142d0940000b03550b045281454150743d41a03007007038080304c40920f08042842c05001c4d61101c8802a441044c41c840f8842045095000c48990300c1103070032441003500c000482181c0102c080846940100307545200103580d11098801e5140c00c025080c1c54800c8020724081c42c0c0f01d85074201e08280c450000400c807070f00700004000460705c006d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 383251025 1250 383249775 383249831
    0x9020607081305060304080316020304090c0504090c020f07090e01060302060d0f0b0406141201090b0708070f0305010f0b0a090504061706060f0918070b07080d0c0f050f1303050102070501 82
    0x108107210107e034409058076813064042d41c18146078490110200d007980220b60003184401c0c181b2024100b440d0704440a0402e403591601c040004401c0d8a13030032a46d0701c1c13920f40c0541480d085010103004030200c94000b6054031041000109110b59641d010030410b078492901300b01d085d03664005179600203596014841c0c2c14142190144007440c00d1020407007500c0c050344000b43c40b032802c4d1404620400029009650b4064000e44504101d240c040c501030500c0c4c600701c500c0800030301d4000905804600a00c01d10341a1041401d141d0700040c00c0204036026907100c80c210006002c41c80d00000b0386596a8056500644401c15800d080300c02c80c2d4161b2860900003400161040d80406800311a41c3c0710500c06661011801f2070342d07403400c0e907400c00c80c1c3d0800b8140d4101107000d0030000784041c14041c07200020031044410a0381000b190403441012182c0714810002c00c000103100b001165402c2ca1402d0150a10002c0214030300f1020790f40750740d52401c903440100201c1e00d594544076100e256002d0000c1103000b000c18 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 383252275 1250 383251025 383251027
    0x304080d0305180a080d0902040621020a0602060f07080403170108011a06211003060c0c231e160f1406031509070c0519020316270902060708130506 65
    0x1666071074034094060f0b040c600d24611f81d86e80c1c40001755901d94204000618030754120a032071215428490100381d07549403003a401102c841400080d15840060420320903846080d8401d11030721400000c940c2001e000c0c2040c0c0822454110290010803001d00382c9000304411000080c204805518070408180a190490320591050040744a0f01071149a0480b9945501441d01c002d0b41e00d45036010030301c0400750030283c0002d1800074a03246403031b0400000007480d03001d0381100301d000d50040c09000601034221f255942e076400901707407003201c061241c0072441d8191540f010340e6500c80850108042c580794070351004e0204014404100318484407110604040794054885900e54904242e49421811280003010b008405a00008608512511081c2209a030080550725031030440c89607503a42d000341c3c4030b00341d11900801c80340500400d0303010f408004840c045241c1d00b4014501c0e005000c08052002c8880401640303035a05900140d852500402c1440d1055000e20346440c80c0e4051030304400046c2d00a036004000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 383253525 1250 383252275 383252293
    0x2010e030105091f0e0718090c09200f1204140d0201150608010b040e090c090124020d0c030c0812090303070f020c09011217040602030d05061e120304080d030518 71
    0x3020829005031f60092000a42400c2e03404203a000916003100c000c0c101032215507010a240c04590882c9141c5860024540c00d046000006c00e0740c28402c0d0440740741d41141c20004c2d20509a40c00307100c01e500c80c2c05000920440d035904034405040c400407009400c0103035551800d90380e00010000106000d0481440c100c040740d03041c96081d4180307119a004031224182800c0014500c40c01c1000092120315003c4c00790b0300c0a5a40e40070800a441116110070010f1081401c020038031480040c03d0140c0d040345070745041c4800b0303241e00c003681c1e006800d01c0c00b03031fa074240300300300a1080742c07031170980c50f03010700b5071100159500d02d401800100300302c06203804181190085031305043c0035500c102442e0705540c101c90f517400c3c4200386403810940c87e841e01c904024402e000407070000350407034001c005003007003540000c0e0030700490382c800080000b0312a0708000403110f07030b441ca0005541801c04481c0790307603d08003c0781224581078403007004a1429006c06081c0700000d848404000d190b403041c42e00c1e52004500f901c02015044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 383254775 1250 383253525 383253551
    0x2180403050714010e0327030a0b06120c030114090d02030f0d0216020a06090609120f12170f040201110f060705090d1b1d040308060d02010e030105091f 67
    0xc400d5000242c002441103c04404501d402e40c024141030407400304a940d141807038036030300145109000700b0700034844d075001d40102c0318200807950321450b81d441882e000325943c94104129400b551000b40c0401d43c8114102d01c03286403800d10820241440c01c43c8440310900c0c050000c0b03407421104c02c607214115017041c4100f0001108503001d440110f590352501503242d18040a101c158000300e828080d5000005240000d040d030f400035040008c1d12840d0b0ba41c0b078151511074a440440c9c40011200600012602c1c1c85000866108860802841d24620307141554058000842c1e480d5001030701c00c0080b03804140248001c668010b51012450129000a0070040300500074442d2200c0e0004e000805105000455296036911007040181d810391010241e03080c000841800c883d8442ea43c0030b0035120000c200401941c0301d0740c070b14425204682c550360710320f4141d83c0d1000380122080410310481c107001c59000756104580c3c0030f0042901c1a58408001c007044946014000d58440351071603805003880ca800ca01d40005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 383256025 1250 383254775 383254777
    0x161e0b070e041803032004140609010c020a08070e0a0506060a030c050f04030b09010c1403011206090c090902101107060c0510022805210613180218040305 68
    0x32200e9400c0010101c81c107400428060502508050410252542e9000070550540d018400c868826425100151910100c031003061103980108503803000c80f08400301203498440020602060189441960b141080d17021462403005a0054138564000744814400d0030401540c0d140c0c04801980280018144100031480c240308810000d0105520791a1b1812114058400c5900c00e80030024407d6580f9a6803c1070114440140c440e1038040d420b111101e403409115510700003102a2140c841c6140d40d20748000c1c41c18010880c0c0c000c032a038a8803042c1240c04951b0078205a401000007a134081200449841000348020011100c001402200300c5100882600060f0400941e0302900340318642540b1030030031034905501da80d00c04e18528000100c0382e1f10151070a02140100d02c45854007041c4070303640d50f800d40300c40c080d80d010010092949500c42051038010081c0d0303900720700045c000e0880c0c010034000c14002d40f250300c9448044440c1442071001142046c80e44403100c0d030710600700c2166900700340d5801809 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 383257275 1250 383256025 383256031
    0x803010509180d030605090c031b1305060a050901120509060105040b010c0204020c0d0906050307050904050403270513180b070216080c1e031f060506161e0b 69
    0x1c0c40164005840000c0c0c2000d961142d540140803102c0d034080c0b00000902903c0c0700d008a034066680c3c3d8021880f01c0009a042e640900c18400a000706281c010146a101da000b0039900f0600d40d50903100001c050b12405c0040001001c5a510700d5a503906940016040103500009407291f14500000c00c0320345100421541d0543d00b040ba00414000c3d000307001240e402004c003502070350252000502042c00c2c100011010800203035910741c21081c80c0d803401c003070b10380b40421a84640440d0007000380380040c0c82c090f0311a40c1c0c0301d0b100c0d05200c00341c40d41100010040080a400310780030782c0d01a460500561600b400d1030104145514810f0040c0785903100c408031a242038400040101c01c0711001b081c0418001d2041800100c0c8020000500c56507840c0d105036505064010540a56480c6502d001e801000380201a01711b13a014000b494100404044250488012500004416980c03400841c103030392040010020300050f400d100364041c0083c04e2060343c2e000e441054450040d40d0000900005103169062a8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 383258525 1250 383257275 383257279
    0x31d0a150e10110a0225060813050d02010b011e020a06111e040311010c0b040b040c0f06020313060f08041e0f080a0905030d020c090c0c0a1a0601030908030105 70
    0x3540103103214405140c01e03030b901d1240c80740e00e0420320718100441107000071301140700b09542125540c0042d075a40d84003104036000041281600201d0070b0040500138806540c01c49894003580d00082c00989030141058014508000140d450701d001c1401903920419400d480d46030940004491414004065603500a15000902148d21350003203c501c1081d190030f444058004060108205083ca4000c2d0075581c0180022140305585c84043c1e000355219002008a0f185d1040d016200f070740703441d15401c421140042c02152642c1038906c004ca02c070034910814000506164009685a014100c140e01c18004142c0240042060800101404aa11400c101d81058002003c26045060a4402040310b2002c4002804101412080f03208006940c0010304840106a440c00300ca0b40c3c44208264440006954180069005511041492400005190700404e1500d0b00d5032070700814141241c2440c1d10110140c840c462040ba9514400c01c07401102580708800740f90403c0442682e0340d070803c00340418080c0364 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 383259775 1250 383258525 383258531
    0x6130303180302030f060901050a02041d0a2c07171504080408030406050409140f240d050a12032a1b0b010f092c1903031d0a15 56
    0xd5075000e24103040310145802030242c42942c402e030141595a407000313480e88a138547ca490300040d00c40c806803003950266021210303459450043c10884401840010702002c8901d941c820300000d42381c400121030003281e0072400640703020304088103805041c074982d030b400104100e00f4a6001c1101640200c3c0482c02c0070000061681c581c1c0f17550034000524040c0745c0280c0e910707110000340496656084009072040350902c0d2418842041e04200c00f5070540812b9134500700d140241c00c041074a10300d900c580349002c0446540c4036200d0707400c040009203001418000568194000100c8581440007001891102030281d05007808040e000031684d220301d001a080c105242105100341140d698401d0050004070724025400f040d15000360305001184010038820200e0022562400007401c504134001c2c2c00c508443d001e100c0c0b188000c48035100f81241c00329130302007819020b09040e0203080640c4012107401e80c3d0207543c0004013081094901e0080070850611440c0541c00306044000151540040300041004d03e4008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 383261025 1250 383259775 383259797
    0x504020a031b0f031505150d1101140f030615070f1506080d08070e0a08030904020f0403120804020f010804021c06021308033c0a0909240506130303 65
    0x4041c0c8120550840d10401c560607900009004048180350192074814204200607240d011f150009414030700b6103250031418440120000c16640a980f8101c0e40040c10031040c4501403500d2001103901c281001c1e28040b8011040c000c050070142e820ba0b10503400302c0110f6142c07201646400d000c50341c03a404002c02050f0012030f500c00001d01e9030081d400600c0c2e03210403108040c80008010380001c0c400c441240006215001c20105498252015411100c2c1c1c0405142b031b11410341f017404040d500201c000c2e203500c441000000005464406452190324150f500e80c11641010b00c100500080c01030802c6040103065010700c80580c1d562170b60310380c0405220740407040b0000140b40c644043c1c000c080c00707100d05460300d80300001c43d03080210040c0211440604281e03101c03007441090100714034010b858a0703008404a45804240d541032801041c0b00d40d414200518065600ca080405586400301c6401c1d0344170012211007080405040440081c1c0740c111400342c00c100c041c0c0000e20744d948044c031005c0d0402c0840781030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 383262275 1250 383261025 383261063
    0x4051207170a0201230115140f07080310080c09150d02030106141305010e0412020a020913110307030b0a180f0302030703121a04050910050103240504020a03 69
    0x48032600c0907020300540707400010704040d008101030703408000100c042c0504450b54940c16800607060b03130302094941754001c0c02824122000300e10032809085003001040400340c00e01006014000141c820072400c1e81e207141c0000291070400241c0d101e80740560000449601503034913941d443c0d07131043d207005400d500a281035000482c1d00040d050040e400d5468080049014229019003030f02403a8182ea00d586c088041120300b60403203100748682009242c107640464001042e425540e407101c0224030440e040420b0940015129070010350750052010360001c1c66004000f40c4e10002e048840c002c4007c0c04270382d461a01c89071003118006104098030b907514400b00c00510901000c42c600340c1d41000000345144914500a50b90f40d08c065000d07004501c1ba2481014030007045d00490b801580041c603442103030b600300820b0001600c000b9152131154065400c88102404481c4100d60007103000c0c280d03401c0072441031003501030041e0940b1506161682854200001350b10380c49440c1c41101c0e441460380702007140c0b107a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 383263525 1250 383262275 383262293
    0x606060d02160503030703150e010b1309020a0207030303060e060a06080612010509100506090c040605030403110102160c15141303080703080610050313030e01030b04020d0e1504051207 81
    0x22000c0d0110042e05110800d0000000245d0b100f034406440401007002007504003122400944290950800d030f1100500c44490000080e08082d03c11200b0a221103813944c613240c060780c114490000060740010010014594107006500040c082c035420f0101034200100414001d14031401284217100c0e801d030103d010386c0c446001d2940100080c00c001c10450410304a0176490b01c0351484050b0855041502088072031600d0001c50740500c1910465614007450001e0644840d04020019024040c1110b4140c100600c00c2c0010038680c030021000c80d009102500e46040404042e0f04007403410403403d05480c1003a500505690005402c045000703840c1d45d0055401440700b08150002840103030041000c1c000c0503040508130380200d5045400c113600030010401225540801c0303071700380f0350003034030341c0c1e141c000700b805001c028100c40c0d010b25000c191b10381031030041401d0340d00000b81ea0807003503510030306055000d40c140402c201d0038107010000d19850516446450f6604d10320003c00d175020100050b55810080c03590 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 383264775 1250 383263525 383263537
    0x1020d2c0111010908180a0501091701090c030b040b010b09062d0f04090c0f08060d0515090313090207080405090a020d0f050103021f020717030f03040c08120c0606060d02 75
    0x20b402807081c5a5585070400058110030741211b030103000c1010f00b1445140031440003095035030680d590080240751912031140c06a0040001400b07560700c4543d000030a41104903a00030311f0103120a0b04c020304291400d0b240008059000d04030800341400109920350354141119070a15060602110501040c031381034038188180c100200714a24000f4503114200d080d60082c10850f06055820052400340b031071b09803075152045901d2030029082400081d058541490103002140c068400c460100c800c1d0500b0200242056640045513800402d49410b0100300c01c03007080161140201c29400d002840d51041503d0080d070003154880d541d014006164942164151004014001010b03c00d1b030044066000007490203000580c002d00c1c0189480300d85000301614500000300359401041118500201d640741520304001e204824001082540c0040c620000034500450007207007008a502c3c6058140d5240500d80343d00d002e841001806052181c1d01d0110340c0c0350380300c1c4007581ca9555407098880c10305c00074401c074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 383266025 1250 383264775 383264807
    0x60c010204060c03120506010509130e0f010e07080c031e12040f0302010905031b042c0105070201060519090b06040801181707020f040902040b120a0201020d2c01 71
    0x2040014100b40d00c50f0003001c3c854002c0e11149803540d1046001c005884084a00364041481044202d01d039091641c000083c2d00d80e18000024010590b0181e9803c14007940038030032044c0c1d1a03101d046068030301405841d0042c91075800900300642248082600d9880702c458003000c0b0240d01004140381481030064050380005100002d81e90390710750700d04180302070080c00180d000610b180720106050600194440c00c04202c041044849041c01c010800503002d0312000d1010545484038803078054800704460801c02c05003400210301c034502004002c0c2140d100d0b9103e240b01d00c82c3c0940f4003030000b9a18050003303035415840d010860721188070220348d00317110342d601a0589628008007024135001d2081011541407140e6a0512020015400071006020303200019504c401d03840c6880040b443c295214a80052018001248007801100000c14260b1a110040c50b00c0e0001d480d01003c43da03051008031054481824031890200a040307040e1814000c02400305c050aa1005a680c141d03170080071290144510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 383267275 1250 383266025 383266027
    0xd0207090906230703360507090f0609050703090f030309020103090b160806060301080712110d050d03060b071a04030e03030a0314060f010203160c08060403030606080a05090c0609060c0102 83
    0x50300415019003070459100c0006881c00b54006c242d210301e2003e88180c010300c40c10741a4403070074200084910175030490301181c241c4034031040020340000e00e0040078890544254001820351a01041105840c4003d045008061605140d540014000c0101e000e6041e01840c00241d008803520060b0300800e0340f214040c0c100d07010402000312901c202003a64501d146c90783d50301e88198507940c0510403940000c1c0554805600000d01c01c0c45214076864000340028024081094007040c0400031a410002080c07040d6566041f9403650901d464143c054200200340c046480da1400c0215229401441300c0010002c100603101d50119043c540300308501a81090010140c1360749000010340074000b00b041c840c6200b4100381240000c5d6442c54884102da19404060f0041c5180c040c9064400b0314201480300d0403902c0440080000c101c0c610308004061041d8465200040d01d1401c03c0703405030440d80011b0501514904007410072414000c003050100f501641500c0081e143c11161001a0380c40c040c0070084000c9601c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 383268525 1250 383267275 383267321
    0x120902150d0c0207050307090f1d07050910060c020f210c19030803010b160f080d1103270a0807111002070b030f0406090f230d0207090906 61
    0x102600180105050081c0c00c1000d01900b1030240c1e16482c9910800754903401607101042981324907003050300f6100301c8200c00602160116041071492040080d1048240e2082d44141b12504000580c96005040002c4840b21545094002400b080c01f683c7d00034010752690202107103c1d180c01064805092440d4826214400020f00700f1703580d5000648401c1c82840f4040b1f400c0888a0f01d14540401c4d285c02c411140d1643e0f00705540d9509580c4286481031544401140b4517002c0340e200d0b00e040907014425031540d652003601c4107a0768142c81c0c01e03141060803000d003001408120b180d01206401c01128a441400c40000355642c464101945010050240038001480078100700c11202d201003551402c80d0200a8604c1d0802e0407a900c1c08140100d0000d802e0400c04940d20403050401d01354813511480380803550700039540e10005040c81d4803c044032104800c4102200c03409500590295026041e0010142ea21107400c00946d116020f11881e6240ba540703009040910200303070020003c41a20140c044507030700c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 383269775 1250 383268525 383268559
    0xb07020609071a07081809070c020105070b180a1a0c250206040f030b0604061d010e041502070506150f06040603050408090d0c090c02070f03142802040f020901050703120902 76
    0x71440d006c0507481056401c0c00901c03c03600814440305a0b07501a03640d6800c01040e96241d1140440250000208210488144074400401c201400030b5604c6803e41605204202d210380302466005496042c060009018040c80807107240268210001c91a06c0f4040406050022402c1361249401916111140010110500c4074400d10035003c0e420076101007119650715003170012104c1000d21001e030060034810041000941170a000c54009000c0c10140e40e48010039044001243e1100c0800c55013a0020300800001c1102e0744100009003800b62201c4c100546150000b8055110313a0050200b85650390b00030030103001c0b1400580300c400001400d04a541501c6041c810544071441c441c0c03000a41c10810443c2c0b10501c0403413001c0454003040c0c840c4101c80d08503980c100708102260307146070152041c90f4000c01d100400c004000d000854030042000740107014014401900d0b03000c0c01c1c0010440c01000b055040c0e0368404104da540310742500d002c07070400c4003802c043e00141008000284d400664074003104d9000d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 383271025 1250 383269775 383269807
    0x1804020c0f07090515060c0f0312090c12030d020d110c060105090a0207051905010b10031a0102030712030e070305030f031509100312050c1204030b07020609071a0708 73
    0x940a0700c0100d0300c14640d1801e010041c1c0e4001c842c0c0c1d01d8000301e014038110680c2070800c060100b400e0300100380c4d60b000100c1e400c204d1030f40d04502c8032a1049010326051280010040c00700c0003c2081c00e41c2d5040e0b1005035860180d940f48603500c03c40d0400c940c00620410210f801d40d100110080c540207800c2d650749000e645540d900c600a0040511681c3d403680891402d11882c42141d9001e544a0094040680c00b0707410740010142c000c03001e035015500c62012000c0340e9a550302840381048152000075450300101c8455440c0100f418446041d50700c10040d05000c0341003500d400740040000e01e07010503052003210700c80b07040440c1580014814030001c6001c0d45404050009540310303565001e4410200034202d410481403440c1985c0c1c141303915000c02c400740041110324004131410a01814458500050300340c1e00c03450982203101020301c1c000003260a0042241181e003460304480544010403407414543d00850700d8082a110300502c51001c0342e181c4030800c408600791a5038580000040ba08c40040c840c1654003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 383272275 1250 383271025 383271043
    0xa0b0f330f090f0906070912031206091e0609020f090f19080f06060d0201050d05070513170c0d030813060923011103070203071103010e070b210f0c1804020c 69
    0x113401740500042820384104100300841d030075264200442e03102924240d4103119411008540c05446020100352040c483c0901d6900719001c80308040c0c02c090329980b000844079581c02440080740100419945101c90b4800d6840c501002c44034007902840c0c2900048050800c40d6684c91140c04040c0b0009801a02180e014004400c10050355910fa80d80c0080100340708402d00d000b80840c20a2220300010410703a44a02d610901d0b506109150071040c2c00318210304605a0300c0340c441200514008162844c3c2440314900800050354038031001d010642c0c0142c14583c0085c56411201c4000843e441440300c2604100441038000308202c0ca1902e0410003940c04a146030030700201e40d0301b84440003200300c64030402c03a840350300180d01460070507280742e80e003100b9001040d440a07455034842c2e5550103185001c0c01503500800703c2e141541d5460640c83c6002844014401c1c502e09040d40060801191161b0b0902452b4800100140300d903450040308801440400c4945005030418808943c0c0c0c01311950000340805 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 383273381 1106 383272275 383272291
    0x20f0309060406030b0d02120c01170c0a05030415140906060a03050c152503080903070c09050a1401080601090f1509020c0f0a0b0f330f090f 62
    0x40421615010b0307022301e820103030590a95682280141109a94003c070b10015860059502800d40c0181080c42052220001c001410400000c14215140741d403900c0c10040c1c0a4030100b070a03407c000071994003800c0d110b1200030407114600550b0321400c4a40c00382c0204665060b01e404e200c0540460121590441018091a2005c00d45c4181c911860481614888642062401e0040c45a803020340b00070002d80040140b0380121f00c2000b4490180c94013144081203645a42d1429001448114190b0140400d00300021807880b0307010415904a0b03100c80c6051081040340c09484c07085408038001076844103441c000800c150040f5801409000704144141d078843c0141c2c500c1c00782052101001190400300810402010880d1000403940084080e0f10114200c456400446c10242a088400200d00101c020417041030740e0b0100b01c018038040141451559041c240140105c082040d92860 = true := by decide +kernel

theorem cover : BRFrame.Cov 383093525 383273381 := by
  have h0 := BRFrame.cov_init 383093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 383093525 ≤ n) (h2 : n < 383273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
