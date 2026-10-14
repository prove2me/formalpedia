-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3103
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:39:55.89071+00:00
-- url     : https://prove2.me/submissions/656e337e-8e58-4718-a5ff-ef15fd9a2be2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 557913669 ≤ n < 558093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 557914919 1250 557913669 557913679
    0x140f160c1b090b0f2b02090901020c15010b1c110c030405030c010c0f060c09030f0f02100503012304180f0b01051509091b040f0e0c070822080105010f170c 68
    0x180420150074080400f01c0d000b05011000308940703001587c2c03003801e540c1c81503140074009603840714040b04190400540045500065010a005100010001041e00c2d10100401845681c030303c0d03042012030160900e00410110000001a00740800780080002d00039201c098081300d1441e00c04500464100f039001c640071b480701c4042c02c20b07040040d4150b00680c5402c0380c01d103800409692261107404d0b24400d400d404449003000c42402030210705119071141803024041c20602d0941d8504031100c1007100114240301e1950803200509055a03a1790390015068011000c1000e01d0304d0503900c0c280c1000284490142d41c0e01500c10700001e09403824081280c109880f044555081025001c240190014040c04401240e002298402c940056002c0908024030401da2462000752500c0e614500c1c000000c2c1c80c0f001c291508101c100041003d000845100c0359498038003500d4a000e102a003020703000301e9040b0720069420103000040314912205a4829510034484801d2502804051709565150000e801c030740203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 557916169 1250 557914919 557914939
    0x302060f091c05040506040f030203010f06050310020912030c062202011d0f1e040606020109080412021c050607090b0910030f0207050303040510140f160c1b090b0f 72
    0x31410707038418001c40b00c11814202c1c1801d445500182d001c0c0c2142d08580c0c082a050f000800540c80d0900880404150100c4c04000c56410003021a0320780301e40c001040409a000100507c180e210414402107902c08001625201e1450340c1009417192400daa6150740d5001c02000072002c241580d10f64030072a81d0507140d46c0028260092004903c52801c06803940c4000a03000c80e5031942c4921404100d07078820360003890700d42c0303490b0700412003101c0140c1c02400440e0f01d04012040010030b604111001da134001c40c00c00c4c4080002d0310000f5180c0008100400415024491180400c03500140d0640140d105803112004c41d0b480c3e020b0200240210311403160f1019050500700d035001c0c040d62151840c00c400700700140c50091143c54039403071548140c0d012900d9502c540c2030010400c099200300c030045055460221110309249402e107142800c00b800315504280c000c00307001c1000b80502140850258004028059443d00d4800380208220701c1c441e41e0183c0d0300788036a0050301e26024241c12400ca8008081b2800307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 557917419 1250 557916169 557916193
    0x61c0b041a130b2503090c0605070309090207061d060f062d01110703050601080d03020705061506090d0f1208240d140a2d1103150c070302060f09 64
    0x14100600021105068680340368135a0041c001c01401c801c0240e14042420b0b041d9240c2001c6040160f0700031410400c003406640c002a40c01300a103001c4410010000d0303140c01d001c1c1010300003056400d84e002608514007025400000020560350300c1203031003040c0c80010ba0b43c0c2d041407045090150b40825001e1402d41c5503035103101b6062400c0d1441c188180341c070619000c0c1070301409140115540007580c20b68400d800401c035010b4200004004012246420360a03c201940c8696a03450054442660103610f400808002d466110503030740664001000b01c2000e91117030410141800b5585010703035040c800c0e10721005045005580c024001e85d40c045d0110002454041102179040c48100095400207003045030b2004074031400c0c6c03812131030400c001c0a8050341c3c200b4900f18851142b94007600c0c2010300c40d00240c05201c0b15030114501160b40005881e1219509100080d0074614642d00010f012520754081c025800320380c0003c1d01c416442a002c072007503602c0301c1c0c4522041b460102c8490341a44c0c0100c01d83c2e09 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 557918669 1250 557917419 557917433
    0x604020a02250e060d020319060b1804060f0507020304170f030f120901060510051602090405010e151303050705031c050a110a0215061c0b041a13 64
    0x9010003040c415941d00c400c0c1d41401d100d042c1d48001c0300c80003040980c01e0034400c04000c0c415850300010219622851040140e01080e02c444032409841803210489a0a034248001070f00f101d0f801880c001e282c0701609418941002c110130041d07400340c5000c0d261100003241e440b030380d2051900460060300214105803800d000b08e18160346d42154504640146c044604082c041003001d0180c0304500c1d58000e484a07143d485c80110320000810b48011a030514204000170f8840051001c40d240741381c43e24a0707544410b010103c046c0d80800720000d41022a040030003050090640c00f04220125030b43c260790307080c0c0c0007401c6007007007080c01c0d0303014201212007010100006e80503900901201c0d03c140306880c10007414407075180b800c03c220a9a001010744600c01c000b0445200d00c514a00c2c0c100c056000d41c2442040c50000b9030b100386001c0b023009014130340740220310555108042c0c24004080c0c03503401a40152580b400790250b150540d0120f540425000c2d03020100d15114110501c110b6283c4a9245180b00c0c07611215 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 557919919 1250 557918669 557918677
    0xa0b0d0b09010f021303260a0302090406080d02100b06120f0429010815070f0e0f060705010f0f020a021005041b081e01050606040501032003071107090203040803060402 74
    0x40000d43d03a4560556402e0360b540040c1901c807100803004e0040c05d1650801400003948180c542c0006a0468142440d082c8000e00752403404202c2e20300140c8030180303000803030000e0103580c1105620381320380710101142d654001443c4800707603159542440b100e401a000d1000d103000c3e4800300000c0c2501c0900080b2605190b00005901902a401c3c2c6922080210400c6003020f403c1e0f01803454007040000188070101040204000e1101b140404201c0c3d464005002861300c0c1e0707071009440c1000035954030081969500401c4900408000345030316a5079000707190190080245011540c0d28505180d182c400b002203c3c400c0e9130100a150b005020310024000889004240c020021a40c0040382c41e400107000e00829400c2018140b07402c0103000b09142c0c40f40030540425151194911681004100907143e2210015602150700c02c1c200414a65810640e0044410742074808007800b01000c020002034580c00b040ca01039510080e015552415202c01c000001d0b84411600038100b013800f0004070300b003428554010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 557921169 1250 557919919 557919931
    0x3050310090203180106050f060712020705060f0c010b0613030224040f0e06092a1b01020301180203040c062007030b07021917130f0b04030303050a0b0d0b 68
    0x980c8454860001d10103c2c1c0080d0b44003a02c0d01812440c407201c0706000d20070a80500701c00c075041440445840300254042c401e240c030040008004405a00640e4001c00840001e8500205260f8481040d401201c1c15900482c00800b0198248400c203102170a221049404100d05800303091034440c01c5409008508840c1d00d8001c02d01c4241410341c144a04092003c3c01c06040e9941f81000c840e403401c008500d0190024022520a40c1207105109910040d0a004020503031160b402c1d203240404482c03d14400d001d10f01f40b0720050384082590031501a419070096040e40c038100700800c80400c074140341d04100e0004940041c035103501d0346000d2001c98002d00c105400c1e45400301c0d84004160008104e10705204995100300d960400701d4081c00345858041c00105135240100340300b4000031032031f83c954000d0003010010540c3c1d40d650000300355030324820070f008400c043d0411420b1050155515200705070564480c0c4000e40c000303894500401d80c410024041d0610014005003010119246a00c2e400794141010b002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 557922419 1250 557921169 557921191
    0x50114030c1e04080307060f02190f0c0b09012a140d060305032a0d0c0f05070e040302070e0f01081c030204260f030f07030c020102010915090309060503060d030503 72
    0x246001d035034102c4004101a19030788001c1c503111652840c090055030319100c011003046006120001c00d565020203c1442d849031032810b0349420741040800d8503100e440d01c4000d0185030681d000c010100c001504442c42406e1620f1042c20725002055507840b680c0301d11008000012031070b07269480f05100010181031030700703687c1074001407a039500d5940901d1036115480750000b0201d84085007514140c6540d1501020a00030040c108100401100504100d80584000c0450200384c804000740f00080103180d0150124810b0110503090504000c0c0d40c0c0c0c5c1d942e12400341c00e000c174100020f2116a800c0113180c102c41c0f80400501c454102c87e0320108450b0114004641010350030302000030780c900c65541e14422203030b03074200d076000d07240c004004141000c042e07a0f803004a07640100005d040c08a40c4c5011586800e405183c9000020b01a10040340907181150340908500442c40058070321403070a600204540344607407210341d200c0340c1d0b6020645140c0811180f56a10400701d55011011030f0080f8025503101e51200704c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 557923669 1250 557922419 557922457
    0x3180705040504030f0801060302040506094e190305031306050a092102031c1b3c05130503030a1e0201181e1218050114030c 55
    0x20114045880441c0e0540000704808041e0785c9040d000070748107024104601c2c05502e801d00340408900c591140701021801184400c0444000c030404444120b08500407014a25280d101c40c03800300d1100e0020f0a45008c40042c03443d03d03070034072040064440c046091801c00c00301040003903107064800703800007400e900041c6009150310f000180301e4410103100d0060720704001888070311800c0c07142e851513100010036440c3c41f404a140c50030070707000000d80d040440b0000c884441e841008140e40050b0a90408080c6038108011005030540c2e0803226400420840d1094840d811003440d03244000398a1071070180300ca40c0c2c40c0c0c0007400c02d6284554004c00c0b0401c01150091700340355982000c2413469220440000006031082c24104035070710040c440e1102018030380f0083c4500c03054040c0009010580342e00040c01c801611350080505941d40601144035600050408114082c40c030020306003110122800c40001007044000c50707958014401032001204800440f421581c990040321150750210421f1251490005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 557924919 1250 557923669 557923679
    0x90301090f140c121b0604090c030f0b0613030308100509010b09540406150801020f161103030f071205040303300e06091011031807 58
    0x407200807018800d481c12032001045202281c2040f480b800400d104084112000c030304601d00140340300d070011401568035107400800380050a00c1c070443d40140140c03805c00c41e05a035000d8150b405454540e40154060200c1c01c441c0f010803046104491502c1c40c401183e810030310100e40304128450f84600315611200d4076544400c0000d0a20600340c0c021885900c1c0003c0558940c00d00d0001621042005070041540502c4200f032024070342104060301202c0f0401c160202e403040c4908a4060806800c40042890340c00c1ca41000805084420f8a194181c0c1c5d4040c4e00040d01c0c030051080780d001761200d00d18142000c000d001d6840010300f00e0501514804820b02e064034013903805000420303001c514000015030320141807604500c00f207087e8109205110301400f080020075000103102c0055500034441c45540508080c820303a081c8d190081142c41d203407070845000c0350140c000801c6406940d1075802c88110301109240d002c1502d000c0c440c172881b01d20301400071404c0c2c0035440c050380e84906a203c081d61a106e4582c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 557926169 1250 557924919 557924933
    0xa0c0b0403050d060308071202240a140f0a0e0304081506030a020315150a18020703120c0203040303020c090106051903060810141308030c0901051306020a03080a02090d0809030109 79
    0xe908146c52801001a0130010010b1a400c0b000518440f030000c0d144107111000851000580d4a11703038903905030010002025210b855004103410310168400c5411030030401e105560305903084540140003881c240000c800c43c00000b082e90200c405450003000c0047c000c40034640d82c13202c0070340442e400d4440c9500890041e0780a11800d40d008484c4040c001d120b1500024601403006032103503850040c0701d030440038070405601c204401d0040c0d0301d100002d60744204600d421944414201d04a4020a28008400340006d5022008000f142e0007607007203ca08a0b4000d0801c584000c00b8403c2401268041080d01061781d122003646207040c98a00380000d8881d65408501c0c02e080a0f2003d1010150752400050304c0fa0140c0e0318200d8210314900c8039020284060b1b07480010302e10000c1c103007100c10100880c1031078442c1c0c45a02241c40707400c0c4d00714004440941d9441d02079600e1800403011804184040300007403242403613100b0380b5404e0400418160082103a6101c1d4a500d60141241e6601552200380c0f51011900d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 557927419 1250 557926169 557926181
    0x9030a060c05031b0408150402030c04090507080d03020c0a032601030b040c0617060111010b0a09050f0c07050307030804060222060206330307030b040809010806060a0c0b0403050d 79
    0x140c2d445a603901c2c074010042c00c001c0e84410400c50fa0003c000c2c0000d1007034500008500c44801801c0780450099112400007903c1c1501c05546c040d845403e0580c900108030000c00c50a017100e04580464031f03a16680282542070b8040c40002030308135480700c0e56100c0481d101c0c0b003119003017509400d510101284580041c014400b0300340c00a5807070901d01000e000c01c1200380740983c1300070085860b20031485074054900a41200024011a04100d113000002c1085003003075001e4508003500406240407507035519040b01c081c2c07908803800311181165000058002c041036049a4001e03a202010314a807130015a01598400c00c094010743c1c0070b607400e0012405099002c40d40f8500d1071011074070040001c1c0740c401c0080c581343e401005000307400c12034608411003001c0412501c442c0002c00d0340030747d006044203010a1400509502c00760001d400758060000340440d820003007202807800e030b880996540e80c0d0400d00109103d8402140c1c0020039114071400403401704010359402034400d24045250007815041c681c10791b0700c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 557928669 1250 557927419 557927441
    0x5040c0f030f090f0b1008070603021801030e0618030f040303111506030a2006030a020c010b010f1b020f030607050a08090601060f1125060e0a0302090708180d03050610020a0b01060509030a06 84
    0x540001d91100e11003d1300780741c1680c6035003440c0512640710b181c0fc070b0f0b81e241c40b0040c160104240c2c5400c5811481c0340280155a4201c1c451210b8a0b155070b0303613081c004c250042c94003070005a4041c542040c0483c11142219520606000e40200f03540768190f641c0c0d110740345115646404250b004032100b600d950381c401c0294003600d00d01c00c0168590040d5000c02c3c0c01c54210588036410f000000501854140e000600c42c4a2140c2c041148005500c2500102c3d001001000035190300d07009180400424076000006802e40e1003071a51a081c040d41c4400b41c07255960400e01030480860440e100440c03100340700d0325080c900500100c096610115100078808040348220100400551801c4405e1200540c00710072035034500c03812941e0034030079403071900800d24008001e0300940c1048a0b170b03400140c003d00215200c900701c0001508503500b980d05070368000c00800d019220707248908100075024178428030000c0c18030046a0816040001a4078025041d02c95601c1600360940500507840f107000403607083d100d5260030354 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 557929919 1250 557928669 557928671
    0x114040b070206150d08040b04060915051e0d09050703080c1519051e040f0209061f0f0c1a0106090b07031205040c05040c0f030f090f0b1008070603 65
    0x104003803410828565005200004541c084010400180149000400c96150960740b0482803001401e11070564441c81e0480e001440f00010300207112a072000564003110b12640c0c82c203041c00040390088030341d803040c09901e603c041d0161901d40d4400211000400340109440d00c000b9001c0ca442d43c44c80c0c24038030140d0065070b10307010105034921a000c1c240560480300d0048940c284961514160f8400154000c43e0700c908100d64900020705a881000d900c2d005c0303090056550508e80c645490024210554a0012030041d004035022a8150a0580140d01c0c01500048044843c0c00403c00880340424562184001c0048041c2108042018180303503130700c0c1614144409010350b051050240c15508076910032a901e0508101950200f54088104600c110710400003007001c1e16141080152101960861036015140001d2907203425009041c05c00e045003640c40600c05044c170707100c0c0002115002ca20240008500034904000a1008900294400001e02814002c50f0702d51a1951500145030412404a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 557931169 1250 557929919 557929921
    0x10c030c03050709060824132007020d022b0c0906080c030307030311071406060306220f06090b07081b070804120c170c120102090a05090a0605030114 66
    0x100d5410b01996034080460305007480c58a140620081c25904014000000000c0444a00c00051004d044141c20307040010324011450460000000c0107100f0b103101c000e5129080c5c2202e0189407540c6094600c41d64004001d80440180d5400303009800180d04040c0c42e4400148102000c3d556a40701030426440c003804d16101c209003081c2402084542c0b039081507030158001c20a40807507690000880f410176600d45400308101c3d07110080da0907039020300c40c0003c10148a84030400348840001407070900c40d4600720203c0d82940ca0b010444802512280c07a140048107130700000c8408030b10070b0032070f43c840300307214a00006440d81c803900c03801c141401c161000c40c002802c410602c081082d40024528005001c440c80c145044020703510303407140d881070344207603428941d8422941c0d081c800754041810003000808418405100003008881c0c80f1444908014821400ca60110f01030305c4c414402e440e40481c01511484141c0c1c14135040110540d0000c00c03501c01d180d191500450951000c4c000c43c031200c01440c00080c0e607 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 557932419 1250 557931169 557931191
    0x618050411090a081c0f020c03070902190f02370c08071502100b01020c040f060503010c02031821010903030209011d0a05101202030f01050f0303040b03060120010c03 73
    0x220103da81c0000302c1540b0414450104038000868140d003010142001d00c40d2850200341a4140303081d440c48907500d40107460340010020740540040c5070001c80c203d480560a0341c003410640303000031090064001a03200c01a50b0b400060241e440c040381034114905c880000303041006400d1180c3c111401107d1191480104002c1c03440c2c10440396028041d9903042150300841000000d503a485803160f8070800c01d46a4100f036000da4020f0007410300403a0054000e00004d00501d83e41c0e40908a203215440c069860074000120041c4003000742c0e0401030032440403180f4924200d0801c40030902000441400841c0c00b00d600740000024843c1400d141d00c0b9860140e00e41e440700380094101100c03100400305102c0980d0754030740c09640340d0070701c5019540c0032114080c1c07584040c01c007211540259a009291544000184586411486585812030b030040324250b6018503c10b003410348034000d0344216050071000348040381e44c43d801659a41904480c03010701c64404d0340861059825541d400320390001281ea90035501c0340d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 557933669 1250 557932419 557932429
    0x31509150902030a0e1c0c02061c0f091106040806010b0a0e06070b04060b060405180405031b1f020c031207020307020d1101030f02091e040603060c170a05070504061805041109 77
    0x202d200100c004105098146086c05821100382c284024801e0034005182000b441c0038013001d10156040c288200b1400c160321417060010070440c40c0030b495600c106d070140202803502d070f07040b1025030310b0304405800c45920f0f180855602d5000307210b4000c28400d41d56a1001d0b60784510b000b5096460042d07100000d42d0406040010403155100304141c000d50003044280410b4440c1c00741c4444a00545d4020303800c5544600303056046024007040d0b071403184004a13070b80c88200c0001a41158411000041e07007071205115179148100c2c420004448215041845921401d003c051303604c0c1d50109485c01a02c1c40c1280c0c0d680081c0c052203001004413400d000c01d201c202000d507498804c060100c0c0e4554411403500f00c8010000d81c03040c55808a0300d0141c000066044802e481303681017000215408501802000914132014004009007544000e80321100000550060300034050356010f0710392522414038282c1000741c2200c824082214600411885500000b2940c8907071045880a51404c0082034480c03074140c0404c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 557934919 1250 557933669 557933683
    0x1032003040b07031b0c0f1b0b070b010512070509100e070801140a0501050d02131205010c020d020a0c1412330405030901200102030f040b0601031509150902030a0e 72
    0x85d001200810040000d030b400c0380c594014540c03c58030100c4901c4061408440c402028081014040c162120000302d484501c0007400c07549100d062805c400360b80740c0c01480b03848000c805040c1c0107070f8060350f820001030030540130440e0019100d10080200c00e8a440790301c0030b10b6500fa1058400501880010066040310a03070032020164121040c644140c83c1c03000080480c040d422404842c107600042d0039807021071000020005105000480054109a080c90b03030080201c2d542800c058010034580c840010702c0801e22000d00355014444160f06400c00c260640c6266150034669080008220103841005c010001000002800f107060b94550315840b01001000d0600600e0462905c418020b00001460200580f00e0010007882c0402039036549242c1d1001100f01c0404500c0b59506c00824840540e41e50111107201b24000e012658030f9071611401103045640c000440b4501c000c00321418000107000303401c405441e021081c81001e425481e102001c04a0f40140d9192001607070b100203640f10404144680 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 557936169 1250 557934919 557934941
    0x103020d1505070c3e0a030516060305010b2b0b060c1b010201060f1703071406100e04030804120e0a060c020907050412080906040e01090207020909071401032003040b0703 75
    0x28003400c080205c180210307003c415402e85e80404480b009264850300054802560094211012078000120744a0b499016002e6500024241070000c5582c0b103030802101d0800c942c40d03a5083c082c4085041c021000c4a41d902100318290304c0f040310201da540c81102030424590003c01812070b0903810400860b00c1c00826990130b043da41081410000e0003040102142200c0c404400010102c1c0b840844504500c65103100030030200c20040c45110a00d4002000e9114040c1010580c0b0b1044d21424050302144c01168000d0000b180c00c00000d00007105099250811911428120f03443d9654100040104c0b1580d0440c00c00101c100860714194504034800c01d81216490501503d00350405200d00c000181c903400190640c58002502d40c89915080300700d40c000c3c018820065040d58445205e50040d40c40b50b42c09920070308401c8085503003080081584401c4900c81104c00307003138814840040d0060801e00c10a03d103400f803510300400800e09000029032086e031003448e100d210752804800141c2140c8040d101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 557937419 1250 557936169 557936213
    0x30c01110309010c0f05120307030f0b0619030e0601060507060b04020403030206041b1805010501030b0102280f081204143d0912110a0206030103020d1505070c 70
    0x341048840801200c400c0d00c020b00e08020540a03138101881c10401900004015110300c01c080045044020040d50041c00c5c50341c0c050042c04442080c1c5825a00b01804860b4020400c02c414080c2e040d16040d06240c440303c0e800d0109481c00390041c1d0341d060181c00d91215021510003c0c0305010040c4910810035044001c440842c100f60450f100290385500091008021210000540891007810740c0d02100814203004e0011001c0401048070010300028132036180428102280001c50f503001081001c180f072042c0e035000400351040802c444010450702825142e249620300e644c170114010070001c1554003030781100424a0304086c030381200400c0501003031245030341113001141300a00d0041c1e034400a04902c00c035889030b140301d0840b0f001c0c504500d05a141c1c611500c1e04030a1010095071000d180d4488015031141100e034610240e00a803114261800250b12140c100b0060005107040d4000811407801182d0742191402c1c0c080b9950101c4405485003c046240041d01b0410084403140da210403d41d0300c42 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 557938669 1250 557937419 557937437
    0x80919030f030e01020a0501020c1609140705031911090a0b0a0203030411010e030f1f0c05040302040f02040506040314060604020c0604060b012105090d080402060708070303090b090309030c01 84
    0x20340941d5101681c00040401068800c2800341d84e20070060411026004002155100e01c3e0741ca0f400d507034414610004060280070b0030000b4600000d8800c1f00c00340030b40700c0000b070100c0c1d44481080b111940010200320034200e40010300082900180b00d8024000c0088800315a00c480001c00c22480c0703c6181d024150f410001c00040d200c150f400300949400960004802121060700e00058a00c1c01c1d2600b91943c061040042d07401c1000303070000358900925001504d848102c0b04501d42142620360380c04038038011880404c0100014142980321900f4a0b207500700040c01c207601d078000921203074400d61068032a4202a0140900800140304040e00318004680840c40c200c0301006503516000001d0001e815103a6401d040c00040c0d00410052510310040b2107080e0308008200c00b04401041d0a888594452040e10b6a05450a02550b00e55028039001010141480030b00da032802c10960203400d04400b01030300d41078400d00081daa40d10540c003500b020400741d5110103c02003414075000401c0308aa04002e5240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 557939919 1250 557938669 557938673
    0x40b06271e01050a0e0f0927030c0c121018060f0216031b0209180705100903082503031b0206040c05040c0e1c030915051c0b0d08091903 60
    0x441299581d142d9405c02c010030906207800034200090000b2100d4110150b10304200221003801128801d407070b0700307460143c00038505080e12640c0740980c100c6161160300030284501c040c81d000c0a50b5540150020480300f4450b90708406400b40c41c0302013640b0003d41e182c082402c0820049008880105007407203070440c14000812007131020703610503590180078414041c841000c04106c0d400c10040c00c0342c014101110b0307800c0c20303600c0504085c0388a031003800a014001c4d020034289031801e001c689501141c1c3c0e41076400340c1143c9407401030b54010710303d01e0075418041b604c0348101d11400d4080851580030f51000a03084502c0c160001d24103103003110341802c5402c040b040000050300c051203c0700f41c0310107540009581200040030350740c0f0b004000400c2e90080b11191048010b18054409540031072003039130780003145942d403c0d000c1325064421617800d000c038800303002050044141c003500b034010740d0100c4400315820000b01301240c111003400d102a40c0312803001032075120300d041c5103101e5411040c1118126003a10310355 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 557941169 1250 557939919 557939927
    0x60e0a02180f070302030402180403050301180501030203060a020306010207030606080312090c03120c070e0406090501110304170702010c020603090d0e19150302210f0a1802040b06271e01 82
    0x3d10760350038540c1c08008242552985101003510041c10040414030741400e003006072280d00244241d19004880303014500340108640901c41c100c079400f45c020310981d2218503844001e5040100090304501c0b4000001010442a00400006051080c0515030301c2521095074003d10000402c2010300d50f10103144003082d900c0c0010080004600a0b2a00744c450000400650900030958040015420800140310074011550b2000da2054410030080003030710a0489840500d003c12100034048810700d40000310100321f142d00401034148149424282803081d030340050783c603070000d5541030096400101c41c0340c0a20b801c0361581078020380494040d4141a0440303540701c40c0d00340d580030b860368040012481c40c0180e40207406039494900c40f540e40d110860500105900441d50403140040e18080e40008240403d00f144161005000c40c0b80c040c00e000c4c01c084d02400040c2c07031103400b52a0811400c0002450700c07688032000382c1249803440342600c282080c800401080d065401c100c290000904580d01c0d40c50303a08 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 557942419 1250 557941169 557941171
    0x31009050a0b06010201021c1d07060f141b0c030f06100618170a0611031003140c041d010e06010b030117012a030c140a110109060e0a02180f 62
    0x3104192150b150781d2600100d0290140d0f10b04030146400d603a411140911301c03138010301e850069031110500c890a90305009641e403c5a8031178030011849110000000c68407440700815004410319050789444000b500780f60011450b2a5800581d802541050449280900c01e80c3c044600303001c000c00d85420005010383d5040b645118140c01d2004280220500204415000d002007030401651500007004c60401500c0c2c000d110350441d151490062840c00b51901c01003960701485c218425000d01504641d90043c4826225010f45030621451030403e110740d03580d004500007050030084d450b4012080301c034118251241a01405200d4100c50014442c1031300b08401e803411a01070001c80d8950344240800580100300b00031110243c495000009800304800214500e84803400751f80810a003130b08100b0032103a04248001800c010707041042440c41d0a84660303000c01307840710b00d440000703008192662030100701d604c3c4810403c01600400c220383c00b90700d40b0300310080c8013070185540f079500c0303141038200040c030010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 557943669 1250 557942419 557942423
    0x40501110718090c120803040212030406090302100507170c0714060901082203180605070c090e010f050916050319030309080f0a080114060c07090914100506031009050a 74
    0x39464400030300f0b0010101c1d04c20002e204030780a411880c401c5082500c4c13664002c031810790145450500400242c000041102c088504990301e00c0c14a900b0365080240744000e040050040110900206001c9541c1c0405050365000000645076100c0c02140d6090509010354407170080c204025103000e0640d1500d0086600e110301c01d117401145a601c01500c40350102180d08940c0c007450240110104246e08100068640c0040c40c06d00715400703a40d0781e002c0300e6520403110000d142d0b1103024810406410b007074010524503403102001107840d0b9807844145080716000c966a0060351301140e08580c5258001e050b05024010581c05050f0002030840300c0071001090400c01401c140e40c3e8000c2e4800c4c40b420340c003030303400001d00000041da4501074240028003d420a025060300440c00403010612460001d0031641800289400380440c00e1034484c03030000515000f1000c0d240708001d40c4c1c402c1e903181d10a01c014000c9040c40440041d0606000040c94034200c5d001201c005014544400000404c200240c1442040d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 557944919 1250 557943669 557943671
    0x110a020708010c230f070f0503090109170a060903030b1e090f041e030507150b0414070c1b0909050d030b0904021e01110304330e0d050a05060c040501110718 69
    0x544180c41d5050500c1ba030304024190a840310215000c02c5400300c01040102426628504803030b4403101c4c03413004560b811140715816482180b82000054280d003206e07040718000d040000e150801d101c0815581c170700d02c03030718100c0100d1220700510343c0c2d01d03108401d581c02c00460458440e080c40d03d0350307520408648103214419844600745010b020984200e045840b5658042c100ca40308045c002d12500140120034084c0f44900d08003140511034403c1040d6192050300195a04110701c0c030130b525004070000c071050102c40107190210010414159034081d09051610070b000525101c82200c000600315011864001c1c480d80c1c0940071b010140c2c1c2c414110320003043c0307400c0a4a65010200c0f0050320072443d00581142140030215001680a1080001c49603400081404440619001c0c0340e80c06055074105110000c66490069030f000c1d41003400c03100803001c0c412004ca502c1c11140d500c0e9940307029000c584a10400d18005014025540c3c4500d00001044041c1c00420384ca41c11300900760989000d00400030501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 557946169 1250 557944919 557944927
    0x9130201032a180b0a0c0b060d0827031501030b160e04020d021303150605060306090f0c040f0e06041b0206070810030209040f0605060105031501050d110a020708010c23 74
    0x3d00c0a10f0a9800030071032810b20315902e1011100280429885000030b071100f680704000103401c0e00b0420601c03d4a9944034009a140245040010440140044114000b00d0b240d0301c41300c00c1518100054200c2d113908c2c030602d11142d8910300d02601039400003040e004100b000c00100f0103001d500001007041c00001190017503124513842007450000d01400b14010190124031200006201c0b00010460000e030890354244429078a80007403141511055402c550856002000207510200f000d07038041d0050a4030059903d0103907165050110b2781c0e62600880c03a0241c0141c240a29840c15101c1c001102180e41000304da0f0cca44200017a45800b0b0082440c4244030544002074031040f0141e1607003003d5940100081103d084c41d041500813603e0344a8100c40240c03801c00400c00c513601600540e441581a410103000004100d8011540b903000300000341d0700151242c9a142c079214800c4003500d05000254006c14426140500150075940507414203820f200000f100240170080c06055001c0c488030344001e255503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 557947419 1250 557946169 557946197
    0x240f09020a03291002150a09050f0a12030c08010305060414031b0304140604050a061409120a020f0109150e030a0501020a050a0e0405130f020f09130201032a 69
    0x43c028250b000b40c4015602403054014048078407580c40d01550690302d90040c0440640300f03995034a90341c0c1d001210b520103a80019070003121600080402442401079688914006d140c03645065041d040889000d400300e80c0302d074085076061141307500c0d800251070700240c00d514589440b0349410780600044d024002c42c15004510303020800844043c038028441145a07040c0c9035051503203d40044c021012918050400b034044da140c8441600c0c191403008102040d01854000c041d10010b480200b035000340003061010903006d81e2074604031211400c4a4018040c800c245104000c10036003118581c074140254190240b0061b01c00d1420001810071509000c06186101030000c0d1400480c028028095800041c001d9186d91348000a0040d1042c00d0325880c003044000d401b040182c8004456500c2104400c002c100041525155200032850010700311000c0707031600c0d402190910800f22183c00c10210080030240465900d4031a00c400d80c600103030080c100c10382c2d081f880c802e110381055101c41000030913022400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 557948669 1250 557947419 557947421
    0x31505090705130209153601050a2105040602040513091101030b010905060307090807061d0d02060d05040302030c1506030c060a182301171b04080a0501240f09020a03 73
    0x140a5004200a5460303a140110303d50112954092547c0d50042e020b040074540e034003154060a400070140c590b40e00f003080a4104481080032094a010154008404462218458410b45004500911000d0380d501d05160a00c541c4030209211100021300c1c100c0d1850200d5102d00c2110841c00c0240f03008100c0140140c0100c2c1d442c00700c0d03000304e0ba2160000050282d019000a41501100c00030303c151811940d640d20252480346400400d5a44020400c417030301224502186100d2900740300400c0c1905094507100114200c0302c0c1110300320090b0b031002640e04119a810041c0903180b00341d4071002130103407500201090f00c07811000e00380d9001e51008141c410126000c0c1001440001600100314452981c1c4c07500c03610b00072201c2c0708400c886480045000011f510414090030079124179082000d441d11080d003c0740442d9000e00c80c02100010611010500310300c14402001000e0042d800440c9086d00d00084c80c90848086800b981c07030006041041000071121400a0212412050b00684440300004150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 557949919 1250 557948669 557948689
    0x10905030d0903030e0d020d1404091503060501050d081c1e1506050c1c0e0310020d1103071e0207030f140d090602070b070813031505090705130209 65
    0x204540400714280c81c003056036601204050f4060750f02840301e41402c41000e621080c2d1042080d0050700314100310101e040c080c0710040c09420b4004c0c200c2c0c0c9011360300c00c410030840d602c4405509064000c0501041800120300440340981402c032106070030310038196294000742c803520b8000d100404203001242403480d06079100e01440800c00f1160040300390501d112070000c0c0800070134a0005c2004820114940c0d04c0742c01500c0000c0401c200a1100b100c8890300b1172203d42000c0c80c01c030108600601200c000c0e032400d115004011003168009078a51441c00310300d0068030840b8044181040050081200e01507001c00c010700c14601d102e500080c0b100070720800320305090064101911003002c45103000d00300940b641c550340d50700120106a8180314410707401154010700c0da204810051b442840140914940000240450307441500f0061070710301c000d1074441c040070759584240e441c0300100744c0c41c5500e1032035070049981c80301004021788403440c00e110018154000e05808000071a80c041060728072030701c0d640340b03103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 557951169 1250 557949919 557949923
    0x17100306050c0a03060b070803060409050a050106080d030513020904020915060f03010509071706060d060306050f07180806070c1505040b0709050d0c0e0705191805030c01120b030109 80
    0x1d01a602e040e1402c0c0380581c0c0144900742c002440c194002640e00041d42c16901a550312088144c036584070700d01084040c202a000548540c02000c2400300050000d11811780101102e0001e0710441c40c0000c00034040300d10040001c07202c40400d0714040016607403c0c529a03400759044400d2600c40d22030104901c12581000c0340300342c0201c0002074200760803c602c40a54100c443c115924085555101c100320f0301c0501511045900506c0782001c03510b5842c188000c0c080c2f42c21360f80b0f4001501c60750b070303191201982d03010f41b100c00b4850205403e00c8400c41c0e110411015441c441c140d1040b0442c5071503040c1c2d5480b10028030010410512030524010030004000c0000004c002200600c0641010b080180c601e400139030b0500041034511600064504206010419064004a07040d03c0d203850040603c4070840001d0482c420024100211189450091400b08114840e40e40c0c200d800591290750400384001c50300200c0c4680d0003a00101e0311607a01030b00c1b07440101410440842e40481c4400402e000d41121100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 557952419 1250 557951169 557951171
    0x81606140c10090204111207030b130204090e12070c09050c0c010e070e01080f030d0b0301020903060f0406062310111212070320030627070807030c17100306 69
    0x41c402c0c0d91111a000043e1040c0220f408100c0205000861a800d00c10307881080008800700c2c0000d5040c0d801380c0d10016000802405004403690b040e50114200c2c2e01c950840b94190f03564840101c80d40e170040150074007110003046c42d1860580da41d264140298164441e640002c3d403114002000300750a02d0903240445545002440050000340d0b050351600d6260140b000121416000020503040003c0d8801d20328030098043e5217440f12840500c0e024181403824076416640800c15880c1c1d42c2c801b0400365102d06c5a01e26509150308240ca44001601d4203940810420355662075046100d10084048001143c02203030310941c1041000010341c2e003414400c03002d60160040103803258000740c0c103000812a14150390f80c1c0d1141540c2d1120140d0840e10b21203822140c800440420701c0da0300e0180740043d600800010b00e001c8801d0416013070707940c1c0c500c80d000d01c4140481a01c014071040f02e0304020784503000a45403c044c4280c2010000082100300090100f11030810240e0101e804910a41c0c2403402031500028 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 557953669 1250 557952419 557952433
    0x170703020a090c020c061c09080c0303040c06270b031806070e15130b030405030f041202180105010e130f0e0c1320030408161209081606140c 62
    0x2840300810748044014054017560130240140d240035003c8422180711101d2001841d49140c0b402c0004007680c00301100c0941b010400d403900030000700041c510980c4a52600c00000341450b04c020708101c924041c4000300065400780e41d054500050b260001c2d60880e019154403552459606e00802501034448400c5005d180284500070703a005041001c000c40540e082c00c0120031030000328401d8030543e200c103044526030000c1803244010b038078000c60308540203900308c03410100d108050b07203841d0f4420350003241c900c1500c003400700440c2040003244580511151126901d989028000307080041485650340c4540d034290141418000c0c10341c030000890ba0a90003c00c103413448903c9240c0da036003035000b12611450494140c03010454150090b040000345401e0300c0e540c0c6002c03c40800c2440d801c05042111042c400b0302c4162881c00034a12001e442c0ea00801c840343d64014a62805403a50700705800802280d0401d01040b8162114110044c2c203c2d8054070708200c800030f040f00000f0141c000e40310b40490f20301a041d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 557954919 1250 557953669 557953679
    0x81207202e0e0306040c260303070f09050d0506060120060903030405011b0c2613050f120a02120a08040b04090b121c02030d152607170703020a 63
    0xc00071101d007040790300c40c1c118016910302095540c0c201254010b010340c0c404e800c18030088510046060034085601441c2c180d155068803a24111f0708102d42c4c3c80002010000c4801c84540d00540e400000c100139036120142000d1521401d0321020003e003401d0600001c0c0e40052024030308145d903400700c101500c090f54407a0901200c10b40d2654415901500c0c190f080034980640720350300b0040110308400070b448009e010038040d40c1d171214040e000410102285e07480070300c2004140080e0018029103119241d03100c801d82c1400c0421518103943d0640f18042c0c040b0510030002a2070000d03401000d1034040300c280c003a8000781c00c1460724010102c1c0e00105a43c2c000b090000e030704610741020744203a411100f0180f101030012070a0041210603840f8032406680030301c05042d6840841424081c50b0801881920b140c0792a0441200a940d086251010ba1141c405010010036002d501010342d00015180d8000810100200042d52886140642c0780f040e80c402071660b400d0a4100580750066a015280ca480d0343c0e910 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 557956169 1250 557954919 557954989
    0x1d1f1803030306050405090123060118060804050f060603031806070f150c0215060103020a030f0606020a11040b0906060c030d11270109140f13020408120720 69
    0x44c0f052a000e10700b40008550700e080113001d2440c400c04400c2d860311075292820008445424050020790500c03551030701e0307420310035603409944c0301400c01e0b900c400000d41030a1500c54500703a210b10034400325402c401c041c80744960300842200c508818201010082c030100c00300151540c403900c14020401c6005812041c1048440d076803641070400c103103030304011002c05488c090b03840780300111b108110b401184c00001c0f00c541c0242e0151008a19030314000500b0310240c102203040310203e4102501607400502601e0802080d20344009462500b40c3e02449150070b2100410074041000c0c014511455000ca800540c141041081c5d40000616601c2400f01c52002e020600061348441c192003400319414580c18040c0142d887c03006000139040e92105100d92402c0301008503c50706080281e40f1860043d0802c0705650380001d50031402c0c02032a401038bd01c1d440c04000518011054015180c6c0340010b00aa50101d0303081035090721800c40c4502c0c0024001b0101000405072204003240d4510321342e005250750010000c3d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 557957419 1250 557956169 557956181
    0xc17030c060424020405031002031911040801110903030a1b050a0c050f0102010c2c18010f05010f0e09040228150203120112110d121d1f18030303 64
    0x1c1040f020300c0e0260840e40400364030480c091203030503134000c4014802c01d5a55500860f8454198114069022052250202a1014004124a4140081018002c1d03034000c2c8503220000840c03281c000c0c03030300070100c3c042070300c0f801a0804030045c0901429004043c03a8a00d1070500301980c800c0603180e00004501c1c0000006c2120300a09014120112490105500503c02c01417180d000d80c590b003100d02d180d403141c100003248000c0051b1020b9021040310482d03446440042c0c01c0c0704400104035906604001c2d19001001c41684400e04101d0a40c07985c5078502d82225030220360300820b58140c6800d507147c1c00410800041d20018150801440301c000c0011409030121500b44d80300901d02c2510a9620310301284d9034054074050755801c40d05040104a440c59902c802041203203e0300710020302a00c66400503190b4010700c40e0a90301c00440058195816912149480d0800c404030000c4807202a40c0001c01d60280900300c49010140b500c01c1107510860244051104428940e54940b03500b40d1079150003009080c3c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 557958669 1250 557957419 557957453
    0xa0f0302031b0f010f140609040c0512030909090706051204080906030a0f0b03061506031506030910050708040f030e040905031801140702030a1203090b160f0c0c17030c0604 76
    0x1103419040390170340ca91409080100540c000c0710f08019100d52003086031010010700100e40b8400300d07450004d1303117441e19498a000320b1a280042c64036050038605000002034010700510361500700c01303010f0060582100c1540d103403122140c40f5032882e540d07515020b0303103500c119101c05074400c1c400301c00c1200404140d0030914400c01ba0307a005018243c440410305903603803001d131b444102c1e40340b82c10a0b008113410810b000d1903000d211840c9006030000100085415988160391100b0703140c01400381d42c410415103005140e0000410720f804000d5180a4890302c2d19070304054401401c0054840c206225a501c9030403140160360464142c903130358203200403100c5182d002d50486c0340c08a1001d200100c984500e80e07080e07400c0190060090030610500c2c2d641c0000c2c0b8552001c10509040d03464214402051005100910808001c14070080c1e00580c003001500e4015140c48100c10400c040c1c1446000403c498514021207651801700009800c156503000c2c00d5008000c04201a03100301810001845424078420008a17 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 557959919 1250 557958669 557958671
    0x3c0e1c0302010f05060105030604091106160221030f0304110306010b0a031107020a0509040f061401030308090d02101e05271c0c02150a090e0a0b01020a0f0302031b0f01 74
    0xc00340f0740e00700040e500101c1e40c2c207010880c01d100050b168103154001c5458036101d140c0c1c4480d11203d24000514540100101e901d136581c82507106011402d090f55101c800c142c0001c0c540107072060003543c880d624030071a4507604100da400b0000c9410080140c2d11103408075030080643e0303095038540501031420f8200b0042030000070f041507550f2400382a45000c0b21b580c03e8001c3c1800308aa82824140150748030080c00484524035403451341030100341c1d203205410851543c010111880c0d4036604000f44034650240043c071040e00020000c0b20415000501c0e50480300206d18041250741481c0c5564030001d11300004200b0301400c040c104030b1407000e0b20200c241001c0c1b03c15035888904a0400000ea074403040c41c5a0070b04c40701110110212020701916412045510050071042a021160000c40d10743e04a200d908022840d02241440030b1701d15003040f1a0b000200542c00c2000c1121500000e50f17410348140c014011410000b0244185803090084407001a103410000610103105c01c8a0b0b951b401654451001035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 557961169 1250 557959919 557959931
    0x60a050106030606172a090109050a1d06011e030e060c1918030f12120b0303070303020f2206020705101e02070e1003033c0e1c030201 59
    0x2d019110320400d45610b0303500c541000005603529500c4682c00b030044104860203800c061856035800b6208842040b840f1300c0680c071566000000340c1038006982001e4401c1800320f81c240f052000d8244800c80520322080c071040c0d5030f2102c20041e203d94913140b800710411100343c0b464140790303600f54001e59959620101210f4042d030303076064103029a00a5940121f003e1041b07401d0b2401003403242c50403505180306000f0f40d965960b035030354070119010a401d400702c85d0113501116113a55260481402000300200302e109115842e6807800017500c0c1c0c441c02000806166020440c110132103030005c01d42e01c911056401118a070040440c000280c101c042c03050368010b2083c050041080d08100b0b4101d401803c0300d880e106006101840c00c1000030342c2c042480011032082c030200082000441c1c5299009914a04c0a56545825402e004007100484072541c400303029403806000756031a0440484107030004460219a004d0504082180c204000030801c03075001c1c0c824034000700125221200705074a14447d0b0000c00407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 557962419 1250 557961169 557961179
    0x5060f1803191b0b160c0b04030b01080118030e01051602090103110a14010518010e030706110d0504181e020a0f030c0c0b180109051f06051c020103230702060a0501 72
    0xa03503500c0c1c09004518542480301d020b20105140004100e60f1041c2410741406d41ca030035600d0319517045680152500b0030441c0041040303010a10512100c9400721117844200c01310b80d10701400740d003411542c05040000000b10001d00404e03141d0283d40d0300707600402c00360340d550f5241000d00030013410003992803003409a0391001648120001c0001400302c010327102c00b030405540702d0408c00302828103070b002d41c18408200301c201c0180c0d500b88480d9015000a4a1340e00090700c0e40790626260094841200d030074050f041000b48130084c049485240071400b45607000c5071040061402c0d07109489540003102c2e00c1c500101e070303545c2c51a800c01d030310b035443c40c2d01c0365010400e119000710f003150200c007915000b41441d0881c6010800e80000300208034079141c3c0715030002c601031280380d0301c891410080c480c0c078411541405812213080b91440c0a48802000c00300e401c0e0304215881c1109801d41500e01c04c009050583d90a49940c1c2c02c8444504084000c0c544910000186085c1c0c5d03010352581c20459401001d50300e03100c00412 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 557963669 1250 557962419 557962463
    0x603093f122404050403120e0304060c060f0905030d1a09040b070c05031b07031205030f012702030106032016060e010603140715020705060f180319 65
    0x8890141c5100046240c86029014242d108020030001c040108a1904140c607152406100e010703d03c43d07030f140003006070f1032040300b4211106900d000076190003c01c010403142d07500502040c0110703007060002901801c11442e00300204410300000301980400b16242640d00c1c140e81c4070310080140f80d43c8007112080d0b10010024050b604950003821100b00f6800f00340341754402c681500196110300102c0e4540300c0610003401c02d008150240780215449660140208a814600817102003081d04106086081001d0400c0c501b4605001c0c0c10302045a1740c149003110701d001c04118841a00700c040441d92542c4400d0300801030200ca01481207092400740c001d03114190700b20b080b501c21803400c12190400c40c2c03003669208094440d84403120b6040d034994401002040a1802c03200801101000a259103480e00310840948400d0402c08000d54100035010889501e483c0c0c00c4542c0f2800c2041c401d40e540c0098540d50f004095400301c802d425101d003205000010300c1041c000c1c4c00e4a400751404412508620150322 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 557964919 1250 557963669 557963677
    0x30506030d0c1202070b0408010c09050d030e0d05030f030a0203150102210f0f0d0902132a021e010506040b030f070b130305060f0402010f03050907050603093f 70
    0xc8005091a07031140b000c1003203421080450080c82c41520559660790800907900e40040d00541903907507640a001c141c245d009080200184000c2d560028074101030b4030060044004880c889000b20b40601022040110074000c984410401c85600d0361203013003644910009420071a003901807040500007800c004e40c000540b10080c141051000c0c072490803410041201900146825442034134248443c40312800304c00080d00050714105400642c091682c01040000c00e18009400c030308615043c5c902d10710809064042c03000b40240c1c40081d00109000c0002c900c0d01c101c4113a07100488802800125a40606420250103203a04490070310840b0502e07001c1588400102c0d0704c42e40325510032142005502d0900340606084000101c07540350303003692500c0386410040122071940e01e1910f044100411507800c500702104030700d641d10f001c01c664541911116583c01c0d0500030b43d8071404001c00011f601000412600700004500c0741c020003076503012907501001c1d404585540345102c0302222050501c03400c0340280d07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 557966169 1250 557964919 557964943
    0xc0109020a081c051309060306050609070c0c03020f01050f07110907030e030301170a0507030f030306170c0f060d0c050c010609111c09061a0f01030b0105070b1f0f030303050603 78
    0x403480070f0185201079889600020714041c0ca1011140002400c13000d910544005500885000c11203141510802010f1000204050140950b1440b40c202040d4800c20390000d5941c107603810002002600700613100707806600c012884032640000d0341000c0199040050041040a40305c0030340644403680140d0a5610815011003e43e0040c4010003034100ca41d2124001058a0004e82e415050b0f0360312140d042c14050340042d202003c1d40c002c403000305a450711405008252000c00c0d0400520760495040e120002150b00c07510a80002001543c41c0d901c1004640d4440c0c400b1904000c2584611800fa02c1900600704504555207000400030f6110101d00840d002e074070604480d02e28190302800f0301000324061400070840075a44a076003400103811445101c1c012004a404206034540c00e2007041400b021703460981d81003500b00320070b03041c01d660014256240785038482d900b40c0c042c0e52108003405801034158050301d40e002807103100080e550f440180750021780303000340d8090049584102c03c0c5641c5450813405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 557967419 1250 557966169 557966203
    0x2070609120e0306130b06130903080106080903040f0e0402120f0a02120102040e0f0705071b1e0e180c1e0310051009020c031c0606021011030f0c0f0c0109020a08 71
    0x1500c000182001300326a84120000d19001001002c28100c8c3c08542c1980403c5020555280042c4629034200d41070b03942c0644840021031403d41441c0000e0345998591007007020038103505010800710350320343c903000f07100e00545011203110307404d43c8034055518030782600181c0c05a140c0c440001500c040c18000c071400e03500420749140d01612452800801c08000a18150801034240010000541c10001e541d040e40d2802901141842c10026002c51000c4030340c1d002110b0050004041048000450205610141c4400214440c20741d00d001c10b4142a84180440d0b8800d040420a116006480341c83c0800044250221001d0b4041c03054103004540080d40da42100003400ca00800406c10300d900107000c1d03032500b5000d40f81009100203003491081c0b1101002c0701c2c03007900c4030307024408150704010707020035400d4004080c04400c2ca00c860307444c403511026010a001d480241b0000d12034451078012104500d0f81010005e0b510034500c1500f1740200540501280b180344004000950500700294021a100079402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 557968669 1250 557967419 557967451
    0x3111204020909030c010501120c06050c10110c0f060708100b09040902121f11090a090903030b1507060c050415031d19060c0c050d0c0602070609120e0306 68
    0x20042c0600000b403004825200401c00360754110303020b0283c00d008200c05c14810079401544e14002c008000250416801c1200c144075030040c40d0300010300c0700e41030500502c0001300d2410000d03484055214a0748454418400d460751010801e00000700d6a10482c09541ca03480151100c140d07001108080380b00e8004104400c0c4a40c2d120b62900f0b921030500c0510040c0100d8003036490b0308100e810000041c1c0c002480000c56441d4004140540c000d406148030f0002c49503190980703010005895102c43d0046c40300711680d845000c01054060b03071081d044500300800c0003c140c02104100c107a10f038040d07001251010305200701c44150700d02610a88043d10307921010346c0f1801d01805000c60003000769500c481c15601c80714183c111403403418411011014860345c400c00158059040c51000d8442070342140007080412000d903804030700082440001911142341201c0c1d140c406007000e2010703000da103030301900b51450076070501c00f0000c9045060200074050703201d058100c0307144e4041503280e0408440480f10300c29024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 557969919 1250 557968669 557968673
    0xb090109030303050a140f0609070305060a03030e0406031b030507060c02090403050c07051002010f1a030a030807030b13022107120902060c060702060103031403010b0409020307051e03060103111204 87
    0x80c04c0150f001c01401400241c0c1004d06402020500050305c041d265500c13414280010740c200600f602c0d51069180c00d05112509001d07010032241465440042d0030818031528249443d51103400850042da0400394901000d4826440c00c900402d10b0701c0308491520a002c000590035004545a03080039800424118942c0d8442d1019200c0ba80044010700c401d001d081c60104055445601848841e00c1503030001420650101e14442140d9010800c500110b00054864000e07540004080e140c0c170f6410329040e841c41d00c1d11031007034015103044882164000041448254a07103080d60140283c0e440c800400c150300b06401780300455038241503c2d00e000140307040c8a10340402540703400000d811440a0070003407805c0ca50780c1c941030030301038162502e074010b0b0028001041031581c491040010819400c00b03d034a554501a51100300b4420352145000050300030001621090140d816110000b4000100c0400c2c0d41c0608050b24195000f110024082450142c10f000000b05a000740c2c0e00301011500c028480fa110b40e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 557971169 1250 557969919 557969921
    0x30c020309010c08093a0f02040b030313031209060e0901050402160c0b030105120318010309020d082101061103252405070503040f2006041706010b090109030303 71
    0x31100f644c030040c0c01c00007011151905030720080c0144900030342c1d81102e0b2440f40c40d10450901c0d100c01515689100030800086105994420040b9504a800103004600d5001003411401044148051040700000c000240640c01c841d55109070b060342da0350302c56240c441c8010768100128603041600424060300501c0316042c41e600504600030707081018451520b466941190880564010045014021004001600304101d8071280e1a200300051400d0031004408014080784120210b41015281c4402030305648494880c00c81c126002104142c5d00c20300c2c0c1040c6010030114846e4007881d50f81060000449510a48001918140301009180382000b14685144080c1003034045480c0c0d102c0c4824400005007007103403071440c9196610940f01c00340442905820840b03038010701c0542484020020080010380080c1d02d0301c1c6440d0b00ca03003030740c1d070960703140c219a20741041d023042c0c80c0c0c0c00110010b00410581d41c00c0c1e400c100e180c9019400c03500141c1e2510305604c181c2c000c543c2e01c00e01154840105200003030007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 557972419 1250 557971169 557971187
    0x10b18070c0503041a07020f03010b0d0312020405120309090a0c0207090f0609020c0d030f06050d0f05010f0f060906050d0507060503071206060f1d060301170a2001020607030c02030901 81
    0x60411242130503154603031988820340640c10360340d1031000029010308606281c0304280320180f086000300a1280030f24042000303023240321001010001164418950b40d0500d6058401a01010f44110806051081040d580303070f014a100900c01c035081c90020301042c200f07001d0030403070b00708541c05000c0310fa26104092001d050004ac00100031900d861000c942d294441c0701a0640d040c140d80107043c960700550000c0d0444491683d540c8506003003c0303003440709032140c000000c00ca9a110f0400c640411082c2803160040a0070040710140c241400220382c180007050b00454161512060104080781e030303503020000e0709840740340010300540100703004100e628001d602070b40d480314503410302c10030b04201039000d80200c80190f00400c001c118040001c031303a03042e8004414000161610854640030001d18009049808140b01e1003040390480c0700310200458007030101400156122816086d0010808034100403071034202015030040c0300d000c0005124038800d009070059000d46402441ca032036004030044900b090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 557973669 1250 557972419 557972423
    0xa081009081603092c04121803110a080c030a120c0b0a050f0105090601140a020a1b08060f0f01260327030312150409050a060b03010b18070c 62
    0x1000740420120b003400e20071202e600521982d50040c0d0079040400c03800c1c1402e1010702c170620701c0c0060084000c45039040112990002e070401c4c10101142c40b40942120003083c8520a16042035600000108010010907952144c960481d80c440f05140c079428107541d9030080a242d15450341c0f0544000c8045071520388414544200c0b8584440c0721744440d110b4501350201500c17042440c0d9540d000700000b1000c0340c08100e0140c5012100d220325400e05000003007408a02e0003484022060000f50f003100035000704207421545607c441c1aa800d400c042c03076048800c0d642c03489041d4082c09040c1c00610300f040f00a00d15841440851904c590716403e203400c6c8200d01e041c800300711491484400c1000319000c01000038040145001c200c48000c914201102c007281032075050b81c68020360040c810129141c004912050380034843c0300101d06160401400a0007500303075044080c1c40c5014000d0182c0a11845810540840509400a0220325800c609110760a81d40301036a002640100021400e514880d102240d03a5074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 557974919 1250 557973669 557973683
    0xe040f060e0d270311400e031e0c070b0c0105100b0f03040809060f0a032a03180f03020304080106050a030b040206030405010f0606030b1f140c07080d1d0a081009 71
    0x11007000a481001112002c1c0000100c6c00901d401d81c442d400c17855186401031261400d0205652100c6a990b40c1d0240051418201c08118054036041051109561090004c4002c9581e4103a407403e41c5003080c0c0c820a4845169400c00780001c1c003003007244401317204944040c0b0103546002820101854941c0020b00202d503885070802c0b5460070341c1d0300d60700034014142000c1210366a0b030003908009011102c0118808043d00401c2d10304221851104c03600500c00d02c801d0a021075608270501c0c040300300549540b80105204d51014254091583c004007400542d0401402004640e44038020001c200d812840010480c00380d4100207401818604082e68200e4443c80003c6680740c80d004840c01a16880c0d006040002d66800320f0300041c1c500380d4514000384004010000c0c03d40720708038000f428802004030f0041c4d82c0c513001840e025800e1080220a000b41024015110952000300c0e0090044403028510451292802030705003151902089401c00c948500000f030003138000d920f441701d025003030000064440c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 557976169 1250 557974919 557974939
    0xf0405100516031d040903020c010c0303060e1812070203030904020c0a06060905270706030e0a05121c0b09040b06060c010203101d09070e040f060e0d270311 69
    0x1030040c4441e441d8070034480d84030b012201380010041c0d00700f401045000e5104604158446011a8010550110500c1e0030702c0c6c000702d1452030781425030241640b50703c40002d400c90b58007080228040240f204c48400d49090503102c450b030b10000c00500303501840c88040d5040d0401c21040310189010780c024940e0500c0c1ea0252003039414142c4420040f54a203511800b4815110700410005031000c58048a400c2d01d44518034000b00d540030b80380e6644808038000d01051603a541c0342c0c103600c000e0810440e1001035001089650a4450460801541e008810000850b1181002c0c0e40c404035100d000303021448001600304462030360b4680347d2141980000d0103d86d0401703020040303e42c250100f030004611410601c1c0181c0b00803460100003204008112382d114580c2d4080005001d0300c403402098200c100c60360790b0401082074070b807410101200e402000c1c0c0180a589803241a000003500441e91404188158031244422520f82d814801d154080d54a2200b41e01200c80341400024101e60f03142c9041c40000c0e103080c0c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 557977419 1250 557976169 557976187
    0x80d0612050705190e090d02160e130203190501020406030b010e1f031506020a020a09060b0f0708130617061002100203100302030105011e08030a050a0507030e0a0b070212030f04051005 81
    0x11504056501b9112600b0940c441040a41c0400c01c0c04c03901103809100c0c21700a85060a00c8000e880090919814001e544605030290760b401c122081900c0041d201c180b54140345860300e03500070f500506c1400701080c1031035a944040e600030783c0aa42c01c2100501044002c140b1520030040481300c0c1d2500310103140c4d84441174040d0740c2c0b50600040103440650000c200300f0342e43c0d004000d020303da030781c0c0015640350501d1828441c0010140c280c0b0390160103901103584400d42494401c070f0710b002d15240382d401c00c80040d40014006e50300c05519404100d10001d080401c1e02e0f00400c2c4000144c9030201c80000d030307100d04102d600303820312a0700a40d4403c08080001051680300c0d40040d003503400a92002a80f050301032820708011004203982001000c0d004015071804442d040040d009016040c0d40070244100803407005c06040c0a41b20110424078020031811282d62120b0015415400c5000306034058a07002c21130b042d000e4000021940c2920034109003e0030180b60104000003086900941c3c81004421700601030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 557978669 1250 557977419 557977439
    0x6090604020c070b03071d041104150c0b0a0c08340c0611031906030c05060a030f1e0e071212140c100f02090d080306060903030403080d061205070519 66
    0x80a20309030754501509640d0f00c2d41c0030707a80e542c1c1d45028501c08e0340f0f4819142d00503800740f0101c604a07040c1c460001a811880760007a1180210108081c181891481c00c10000705030a41c4450440e0000d5111207000340c442d04a00e02c001000700e08601002c80610340b56054820b0503840142c40c00d40319241075007403000030303a840c4003d81c0c40100002d6107201e004818403011007105100038000007540402005102c1c03854850b200085105d100c3c0303900428000880c4041284643c104002d1014854400e1004400460015100a02e52003d14034820701c2d00e1500450107101003450700455040341c106c00c60b00d000c141c4070001e1040840030100e0038000068175080c61605140054042d0141040c050500316078070752480c0003030701ca28410b0081d03240c1c0304101050b140d5403400c91031094142c0014049032680c0d10400426100d01c100c4020942c140700c0420000708203ca510000d10360080065018405199035600c080c0785120441c00080250b00310359810b100500341007100d09107810015013564a56070b80d410b1324070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 557979919 1250 557978669 557978671
    0xc14040f1b0f110a11010318050a0204110c1018050f0a150507050d09020f04090b060a05120d1d0a1503050c0a02071404020c01020a080114040506090604020c070b03 72
    0x2103032100781a00340c855481d0000540e4424010a080c03140c0544200c100d03160300d45180b1900200032603200030808400f64400d80c002d007602104004000580c1441e81001070342e58100041c228425802d0202001d603010408082c0c440302c0444200801049017920241c2d00030749180455401242000c41c2c0e60004160100032400c10746404030081c0c0749090301d0382003401c08080d8511140e00c0700b508110502144075401800c40700c0e503460685000070146c80c84d2001400640010700c91540c0b00b41012102d90034043c41c10103241c0100412108032080316034038000c1c0102d04100c2c0d4411200d90300010180c10600340103680100d0541e6150001d80c100c0200d10340010842c08031600312500303a03040c007525203002e41c4e0980f00c2c40b6040f07000c14211600700a000400250b44080501691404180f00030095070542c4942e019283c00088890081d52545070360400101140001d1040ca280c0039503d00e105141400c003803140038010754025020090795540c1400f800040d42c0000c0322a45184503d0300001600400a030280d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 557981169 1250 557979919 557979941
    0x605032a2e020d17010e04050708061608090a0c12080418050105010e042d0207050124060804050613020d050d0305060a0e0108060601031e060602280c14040f 69
    0x203508900701c424402440c000b03000d1401020b00080394200364229208501182c115500c040c007003801980d40d85062403d0001d0b96000c102c0d02d01c101014840c041810560b400d20344281c03a0750708101d43c3d50341100259580e1154401900000305160300703201e00e43c0355070b0000c102c0c0c60040d010545090340c0c8500045090703500100c281c503d107543d500107002940e03200008016501e403c85051014400078078103040c81402610303603003003500c3c0c080303480500401103601070b540c00c0c03074200f0000c1181c2c1007078010388006441c0c0b04600f218400d1401d600820307014011592540101d03000300043c41c607550781d0350030030618400c003403801c1e07031700c41d401e581000d00241041000e100008034035175003c43d040c02c043c1e05029a0f41d94681104500c0d036100001801820800038440da130083c02481c1c04105181c4400c18691401a8410800455428104c001c2801c2c4e400049211f610055181e9200344184040b01e20b600c5110344000040c2100d81b060030810009000804280c02c8440042000071198071480604048500d46a03039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 557982419 1250 557981169 557981239
    0x80a0305060f0d0512181e030705090106021906060503030c070f140310020f04050d030903050d14090f060c0d08160207060804030305040303180807060605032a 70
    0x700911070600101c503041c2c2c0c41d8140d8800e0600b01481d41d81d44d0301c0d07499a10150a20301004914100480c582c0c00c054a618200030f80b1507040901300c100900d4206c130080040030f010f03224540000a003810702150340d904075000c90b4050804003001c0b1604105001303c4000507241d464580201140b10303038050000788480072800001301803c9284c04d0008030a5607180d0b02c0003404210094515000e41c43c00b1a00c0800780c025840c0c0181e9640c58100318204d903018a4100b02d401800310591075041640044000042d43d0040045a10f07510b40140100c0700e11000040880380c2820a000d1b201d01810406600d9001c8600107000f01e060040e44500f0030310301480a260301000412400078003c0d85108031000c01050700300d47c80a00b840d1824043c3c007802414000c0c20003010035a4600004050601c80e40c0410454031000d856880c8808450400400780e0300013000c2610201c4c03500c403001034186000108000c1d400074840440c10080003414100c3c618040404070990441c8212018901142040701084035040403042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 557983669 1250 557982419 557982421
    0xc080420010e04050f0a240e060a0f0e0a050f22020a1a0711040902060909090106120821060906130209060c031b0a0209060d0602090306090f010e1507030c0c080a0305 73
    0x3550800347d80e5204124440c00180001c03031111088988480c20503200c0f60011004207454040100d00ca04081c1e50120000318010b40e00400c812590560b4030340980785028041c0510344403000c044000354029203401c088010404c02510000800280140222340000c3c03140c1c00322550741c0f54548400101c001d128584100020b02541002031040750001d54030340c1a5010031281c42581c2c04641c00e8410541c180d441a2041c400243c440502500301e140544011080c0440702882c40c58040d80d650801559106e03e524040051402c41c041c0341c82d8607200d03000c0107101042513240c400a000207003480e61004003140d6003c10003039080d5103400c0014601341d94076200031a80d4440d6002d50b24010003c241e002c0000c1c0e00144043c1c0007503540c01c0c4416800c0601107444044042c60751074120300034801d1160281e05401400708202060502017585404d1040100090107400000f12015407254945c403002c0d1030410045002c80c024038447d90104100e19071608090500780d10755200c2500d40d8000f40800e00001c0e1702c0394 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 557984919 1250 557983669 557983681
    0x1e040f1406010210060b030105040e070f08013e09010e0406030c1a040806011e150804060f020412080a03141f050f031b060412050c040c080420010e04050f 68
    0x1304076080c00000000f00005810300d841c1ca41c061106114452241d9205c00120310850420b0010b84000c0c0802000c50b4007040e81d50301c18501816006000d00c800250300b4a854960440705940c481d4180444407142030f60403040c5508420300d803c040e10b5035040101d6103816030665185c500c10030380914040c1c1243e505c503900e403008410006000d0b06081044030b2082c48100008103000038a5815180489195124210640040e800b40151a8071100c1401e81c40d02540a00d542c1041d5080c1c0580e0240ba402d00002440c02c5503207059215900c02e0760103222101941c000030900d0035000d0084040f20346400300e1070f0000c6c00e81101002205031010700c0f0101c0000c1382040010880d00e024001058251040a0741fa481e481c0003940700e102108001590a40c103028003201507403a0002c4030007401100042d03441403000c0c5c0c14055502d2049162403801140740085007060203014004c914840c907408403044c00703a890380d900710341280803110742d0460501c01c120400c0c8805640b1ba0050903c00d00d04049840c003586000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 557986169 1250 557984919 557984923
    0xa0302030a0c0f0801121718030705040605150912010528060b030a02070c0e090a0302060c07080702101407080d0b10020d030e0f01020703020106050a0e061e040f14060102 75
    0x29042d20400d001c00044902e81e065006030380d5504403136802009a0b44802d45060400200c0c0040c068844284030000c1e165014041c001961988410217404592001e9211414002100c03014007034141d0018079000b62181c9c04003144010440f064000e03000c4007103004007140d12400c0d18000c1e642c103013000b003d85078801c1700d0401c2103044c402c000000c80300c00c1c01b40b6447d040c44400e05101c0501140c60703041d00000c03103d051000700055480180310300b01c55482c0310302d4880301041c1c43d400d00345011401070156002280d1512044016a540300b0b420030003d42c0380c552981c1c01c07c0f04a594080301503050001c000c240134081c0320040d0140c42128080e45030b0581d903400c0c003105142210b00c503180d070a00c10702c801d01510403180c0c0e0000d0881203101007420000303a1049090001ca1a00c1c0c0c544101074080d42c0002200e01c1050390640018046803c20f4540c15549515408807017086842120307555005900701f6280402a0309007000190450805040001c0c140003001040c410b0710780009000040382d071405c003402125641 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 557987419 1250 557986169 557986181
    0x9130203060603040303050606090907051306021507050c070e04061d01021204022b0501020a030b270703021b0c01110307020612040302070e011419081c140a0302030a 73
    0x410110300d1440e1840024407540030280c40a002c050740c5600041c0c0c182c6514088900d2100d00902e16a500d2801034402012030b4020700d1801c414143d4140005806800050204040319192140e090113690341c5030100c0d1366412131521a44103102e040c070300088000050b01d80900990140c40301084001212148481024058800c1c0000341e00c10409002c0e1104000003640e01719a0403113240700d400050240842070131004041c80104140c2c0c581b0307004100501580108490740e030300c0e2400d0020840c0c000801454814401640122401d14805000003401049040781c0c01003c40c1801400c001e07004030b12210ba84030314403140c3c0440e484611141115038100a03c50800400707540254609a600d5011a00d180242d103580d40e44c511601c80071604043c024802d1102030702e1450b0403088190b83d05c4014840100072980d51034000d1b41b8103002120402034100c4010280c40985004124a8005035079074032201c50281c03103080401c1080610844c1d8849254010641c141c0199005030b01c0341800c11300e900031110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 557988669 1250 557987419 557987449
    0x30c0a0501020615040f11130509060a12050304090908121609050d020a0801050c031605030c12060a090e03070b0c13051311040e090f1218010201020403150209 70
    0x20610004011076a4000307400c0d64444100044d001c03040300c3c8000414080d08000100c400e0850610b0301c025841e982e404c0151508000d40c4210720200b50f034070000d1045011050b00c809030042d108060034008100b09422890f8041c0c030620031240781035a18080b61003180d1300d020040352400c4002940000c1c54040092107034003c2103200140044615600020300464a1449018081c807580d08036101503641d00e58412005121000007448a49000409500c10790b00c1120000090544000f07030b410310a01c1481076911404444a889107800014031042d41e041d0001050303991300810400c5c0c0402e540b92030b805040c900380700002c015a107030581450030300c4c5039000042c9400c518100c18000f80b030310b080080031800101c6505a4401100c48540803450700a00000c0141c1020310b440040c0024000e609241d4142c802e1000354107a1301c0404107815140c2e21184407121010411206124070101e00e001a030032185107603014000140340580e00e03600c541104100101d0214210380c082000701d400c0c20320700c081c40d162603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 557989919 1250 557988669 557988679
    0x606073318050a0b0c13181407091e0b040e041502040806040b04140a03020d0e01020f0a06020f13080a03030e0609100b181e13050604030c020409050613120306080c060306150c010209030c 82
    0x200d48407a00500076540b81c480c02d0104940700782f4001b600c000d001d010360082c0000208442d9190b49030345010001c400d06a8084421000704440d51070f505103d4425201540c40304009030a0503203641d152006641d501400c1621416400503a40c0c0070a0300c10008501e00a2081c3c0261010b2300291038040e001c0c80b000b4001d1030564012008204906502150342658550302c80001a180c40b07200c1c5540c031040c012080206a15803080c0c1000c500010001101d04200707100340e030107205c14516529182e40340e5005941c08178856100022580d065005500042c4191202030716029140c144254207011800055501d8600582c514640f262514070040009500c0400500c50b2914409550b80c0c681d51281c00400150030868032030090421551148c000d40c2d00d681d0840300703d52850404041d0201d4104012004890010107541546070b403d000c1c0c010389084a160001900840c41e6034424000c40303501c001e00041c0d2055244100b401c0600da150040e140c3c4031201e0f4001078036100b500f030505141c401840d100c0ca00c58 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 557991169 1250 557989919 557989921
    0x190206060f0a0501050d020d06121103010f18140309130f0c050405150a02010b13020c070e010b0d0f0f020301060801060207120b0606073318050a0b0c131814 69
    0x1591700b00040f20000c0201210060355144001d100c88028641600b050300b031981010610014885c1c507001c01c4402e40400c50003007022010351401c05044502c3c2038110118010300744008404541d21070100500741a0b44c406070fa281115901c0010102e000303031004008095a24425500d02c00031610600150200c14100180307402c3c1000006940716644050602d1000800203100b900304c1d1007900454403009000d0000420014044009400b07074100e180884000d104600001030041800000d02e030480f001d1078111490405000c0c4440080c1400c0062188420744403240c0d41c0040f08a803000758001c3c00c550752240300c1c1e5418600002d041c0691980138940401003002c03040041a81c40c0452a0002d4040f00c106a0700d20304c5203012150f00700c50b100700c2c155510468100e105243e82c09044031001c14800c1d801000001c2c90701e40350f1201c0601900002d130262307100c1c9980000145241c600c0c2da8120240407012424034685050440a44e032054000c071403224503002907080d5900b50f81c080c2d02140c141e030a100c4205 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 557992419 1250 557991169 557991179
    0x11b17010b07021507030e0d15050f040c05040b150313020102060c0a08070c140a050102091212030703050709030b04060b0108060139061b090503150f0a02190206060f0a 74
    0x2211130259000805003600190400c1014002c080303101104c00c020700003034980c1c2580e04043e40104220740300d00940c0c40c10800002d0304410500750701c1c2c1c0305580c4404110350443c10081032000929002d541e4641080d034800e400d10708403c8443c095427141c101110401103e144500c00282401d038040e01040c200181488a2500300d90041311060744150302d441d001c0c4403416141004840700600c000890114055907450380b0034400c041d0014811798005442e905e5000e9014a1440c0c1d0702c4014080c003c103001d4007440400d0805100707030040c41e04001249050700000d91607440f00f1005910a5508072041c0e41c0d1000e02d00c545580042c4016030005090800540c0a01d010801e00d074610200010300c604a0101040484540c68403400002c1d140d410400030001d001a030004442686000c450310804140c42140018103803030005501c0700000b904192004084e12448004041c1e070101414020300241c090203100b4054240b00201ea4410515500400d1a41481c90a0245844c6030010144c001c2d401d5030f4081c09 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 557993669 1250 557992419 557992429
    0x2120613060b060409050a2403151a06040b04080d090b0a0c051009050708070b1c0b010201020d090302160806011a0c0c030d0206090706020d0e12011b17010b0702 71
    0x21495040702000c24224018400600f0510494006a0b08540b900c024040324400c40d50110012141404461810540100da01000440c01c1d2000030564401d2064024100303140d40c104041c5801540000703400110002c0c00150184c00c141c00054902c00701180801000000700028003500034181010800281071400c074415911401c8100b0041c408070b605600100541044500b1240215810400100070f1a1800d2a01c0b401c1c14400d100040c860481c002c07503400703c05000c8540c18000b810f00d00450400020b40400a0954410581c1c1555802d01640e15040500d00640704028420b6025205803420310700704041c00744030364008640303503030200c4014003009100c1e004040030490400e07071150b2940f00d800d51451903e90084146601401404100e001d65500011114090000c1c8000e455840d0784a19040346c3d41c055190316200010105034600e903580c105160039424200341100045502800617680b20180c0840110007000035903013143c1d50214010050141c2e01516504012a02d811450b4001503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 557994919 1250 557993669 557993701
    0xf06070311100609060608160e10020c0307030b0609070c0206040b090604030c08150703050403021209042901020c0a23061b1e0a0c060f090b16021206 66
    0x101030041c1c561480412034030401090503a03280480d0180140b949a049500140c4040c2c410507001c0750031207022810411181d109104174100e031750b5030720b8000404501040341c800c060012040560050071900300d90b9440502400e005140036940329501d50405900b1310030341e090020060002c00032234400500c0140d4819082b241118464131115445424141c0000d0031445142c3c0000e00c0000c001e800094a02c5000c1845075001c011250405441e583e0804190162a0121001001070300008554450703444410b000e04400074002c0c00c0010001c189030240f8030300d800050007445034211244540000e03503a0400a100705920305641040c02c031460f0454030a0082d03001100300481c0301c2e20070700405c2c803900c40c5420364120f00d66848040401070f442d0080b0075213130144407024034454030707580c00e000c48032960003c1c1c0ea0350b00035070201c4011b8207180b51510498402d9801400c0750100000c0c90400100500b00d44003815030303a420a110004c40d41041d10400022054403030000d40160403060400c00d044000446c42 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 557996169 1250 557994919 557994923
    0xa0b0411062a0f10050601031113030f1106070b06030d09030308060607032606190e0f04021309030206090d0f0504090b030309150c100e030a0c0c0b03090d0e0f0607 72
    0x85803802030b14280c0ba052400b184502c00240c480d41d80300d421240390300c0e00054060402a2000c0100423003448408200d84204444242c84100140301000040c80d68070030751041c00d000d9021854244020070004625a11960064a0342c80039001807201d140350501c4050700d000e019040070202c2da46140c2e0080c10b00400101280d100c0c0201003084001c1c540034400705400380c03107130005a031143c544246a0070390110042d544140244230221800941240c00007080040d911104001582c035a645802941c4c1e0140080080740c112110605103859400d0501030b4000d540e2083d0040d20440c6407111002d45070007030340140441002520007403883c4054000d0100c0e402d581143c05d000c0350203500701d404645180b007000c0125400c0a179072250b04094014030009032041440040684c0e1545a0100c2d841d01070b154407800c003002d260000c04c411520280502ca94008039031241030710403c915610f40c1c441250340c0040b11000250b4111051b42d25071154020000060b404049800d5080d80c00f480c00030134818085c800340 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 557997419 1250 557996169 557996227
    0x40513030e030d0f1b02090103050f070501030c0e0405060d020303030c040501170412140408161518050d020f10031e060e010b1c0f1d010522020a080a0b041106 70
    0x729440346003654009521160087d00c24003c81d607503880c040c0e0340c2d1112011030b84540d00940001042562190141d0301e18600103968806640041c9020000107040c041c1000354411191101c03040140c07014406075100750341c121405900e43d40f80c400007504480003c060002441a501c6c2008001180d030740b0040c000e0f22082c030348076034060443e40c0f0103a11881160405030251117a8030440c5c030f03441030b89802101540d610144007007100f47c0700c00d0241ca480d07600a618513600d040d190000d0110b4101841800902400113000c003040840100c04210802080d0041e080040e4071001410301c00c0c8852903552031280c0440008115807480d0194a01e14141c06000d2007400f85c1002405a4051280210707085c80d52138403020810045a40c4840c81c4001c3c0081d06d50980485020310541c000b10380c0622419210b4000e2450501c06c41842a007040321002d02c1380c00c04c90707100030341410218070803030108040601a8071402000080e420242400203100f060080645c1c8540410015080111124040310802843d0000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 557998669 1250 557997419 557997437
    0x150705031605150103060615110705091e0a02030114030604030512071e020a051c08011a070b010303051e0a0c020f2214070809030708030a020702040513030e030d0f 72
    0x24002c1c2c10000b040b9280c0d6a5014610000720610880382c0c0f040b03003280d40455040381d0703241d040032082c3c0e03411030340f9146a0443e401102e0104858200407105550044807165810903241c0ea80002d41c4816400f40c0301869600d502000501003007401d0105210290411402131503586001d650051580c816010f00301d1003006860003150201d8016042c21001c9600408443c442c8802c2042c000d40e10300705041c0076119840780b2804002014100000c1480809096039039600d0341c3e003070024504803030409064680a24404001a9005c90a124004c0780a0741c480c1d52460f603034400d800b4116403200400d224011030300340100003e5040e03d0304519030b101e0143e4103461807000030f0900c00000750040c0c0160300e8000309804141d94a400e43c42168030200c10300102d007900f264143c66059080f0344ac89421a60701041d5482080b40c0001305551602669104642d00409454040c071503002c1821760b84156041440c46460304100001c15401c10000841400300b60000d02001c0b8014000034240252901180140706440d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 557999919 1250 557998669 557998673
    0x13091b03020906091f02060705180105030405030f03010e04142d01060e010932271905060f0c030a02070c051207061106010e04110f0a090501051507050316 68
    0x103040d12004d060007410502e0b641c1d40e40c50344458000a40d0601401806074100041005000c0d1081c0c0b00102c03460b951580800d0150001503a40c0e0b80042e10139600c5200600560543d004100001d5020308580d404600180c01c0914140c1899082c00720400031f141c108540c40d00b10040701e2400341e03100d46c9090f4040a044030401c0c0300c0500409050b0811b038900c400c08800810000416041310801001521145008000c05902ca58480401662001030710001c0000700d0001000110340d0817105562075100b1080d4110104083d18007843c03140b004581c2c6800190020520400b4010140d0203e440000f444242c40c0c0400d19240600c4028600c10903564003044140602c02e214035aa8090a0080c043c5101080d00d4076042d40d0364011442010006211440c106031f0309000424003604a8031a100f91264035103580c3c2c0c1c0c0e01000442200d00c1c40c0c1007840306488030107a0380c400b43c1503c02403510881c0015254104000d201c820102c1c3c08a00e84008020030101c1c00150f80001107a03403c0030002d62110240d5454 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 558001169 1250 557999919 557999929
    0x21203060d120801060e1f0c0515041b090209150c0c300a0f110d05060a0507030e0c21070b13060306090e06040f021504060513091b030209 61
    0x840d00281c90b1a40d1004056092500b00c0b241c00d0588007140c0310760341080000e204000f500d107035403280303908040b124401e800741ca54060403858041e1440390080e074044080066041910040444084c1e030050364480c41200c181c0c031f055a248018040d102c3d01940b0701101c030004580001c0b080f004400b010100010300b1058100103102c4150f005100520581c240b284c070486446401d000c4252041c2c40450045c40b40da0b007540006141d0030555440326002c1c0703480000351a020b114298101c0050b400c9000c0c444080001501445058480c04c0c0c507000024030350800610080865070301c0810045c01d0f0b8000902c1e03080710b944014030044180c2c2d40b85507544408070151407039801d2040381c3e40036008541c004550f00c0d100501d81c8500b00c0583e80c0c42d68007001420365503400041a10810492030b01d2030703002040424003041c92940703508441c41c00a07105d195116141d90300c0d0f100c01c1e8010f5100000141d0081400d03516045000e80300c0b001421009000d01468462401d0308014044184140c0103155000540303c440da00c0e1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 558002419 1250 558001169 558001189
    0x81504030909290315070302070606050d03030203040b0105032121280c0905060a110f0c150c0d0522030305040603051311060d0f05130c06020d02120306 67
    0x501c0d40184400e403200d100c81c1c0ca080b000b01c81c4030030152000c1e03104003141303080c000f940c1c51010440458400c815203400b0380c10340c025401080b042c1c0c0c1080d25402c000c40c0a48a07000e4000d80c440c804d5500507501d10302420071455441040c0c101511030b0300700c4012061181c007100206a00c1c943c50900641e40c030443e14100820f00146010400442c031401d00c02c100868640591803000749440103842280c60030309400c031a0444201d5002c0001140c034454040c041810404040c015104caa070909034100004001070350319045481810440c250b100d100602d030981070800c60351a00f20132040e620790903d034180b80d43c9912450902d1050040200c01311703102100312207000079424681082103000a8664807400c0c014000e9200b0301031400442c0c2800089441d043c40c820040610380d810a80010040080c2c01c1005016840030003100e24488d11800550080c111900ca00341c042c584012140c02981034500e0261000d007425031064043d034000710781083d806500414010805452201c11b140c1d681d649000040d941e200c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 558003669 1250 558002419 558002429
    0x18100b040e0a0c0501080a060e0a0209010c05070e061e18070c080304120e030d090b0f041806030606170d230d0501060305130c030605040c0b0a02010b090c03010815040309 75
    0x1107a00e80c400b003841440164070b01503d800781e9407854150740e0351305500c080c0c62140c818101c008164000140102d20707241e01500c2070302e00516205050007503030307101e00e0701d01005c5421408042242c4d070140081c42c544102c213580b5802582500804060603c0f001a000152010810451034540e1001405031031060504c01d40b82544460025207905007410f00500200481326001d000c076240540e0500d29141c0020005820f0b03403d59580c0d8492030902c90300ca08036801c80301c4858850103081c00040b9407101103181c0100320081c800c0380050800d245d41026030070b0301c804e03034080448003115103010901c54001061074650710540e421b102c41f25100c2d5030308800385130203103401040800001103544946190160480e9048a100b907905100f542c43d114240485079100c040000c0c6486203070142040000d03455000558054024501d03024082c0d6241100e000550003482c2c00c00041c0d540d0b105080480c40c18584094024a01c54140c5081d5030408480581c2c510b445100d5001842103a4006003c06129450903c060a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 558004919 1250 558003669 558003673
    0x180712030e0f2d0301420b040303020c0418170c03070f0b06030601080319030b03032101030b010905010b040605071b170606040207080910050c06070507030818100b040e 74
    0x505101010f00b401001403040521a500342054010540d1100094085c0a2400440d0940c030042424070021b400520880412109980d003000040901c0800d0140000b180241c0141c54100f0b104410402215000419008081c0e42c147d20a000300b294004d00c54100101c0020459460707100814140c60360142d40d000800d081d100340280380400c1030064000c1d0084c00180c04980007640c980706059260300401c504c12041078150788451a005201790000303483c2283c05015685171000d248040150452441c004c490700015013001082005444a103003801010600070802c09541003103644041d80c8114030403c0c08000d00410201c0600c60714405207210300c80705c507280c010402c0c0e44e84d07044e589404041300d04818030302516000076080c0c1424002c0300c0354a0390042d20a03161000740001c0140522008120504020003402240b801c51b0041020300d02424540d118151150250f1030018080840140074010114a54108010707080000581c400001042c10000c20440013401c0490010700e091903da89481c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 558006169 1250 558004919 558004969
    0xe0c03071209021c0b160f0f170907031b03050c01032c06010501020c0f060304021504151e1e050d020d0504080408120a02060609060a0905180712030e0f 67
    0x50044c6942035803a152107090200100e94132000e0020b4000310720041d40300400c0c04411880036071881050399286002190410340e0010245c408541112581220003000340d42c8281800c0c01482191031003440d120078100340320309070681140e803003d45600740b0149840c1411303187c8035100c1110b01403513000604046061202600b4072100d00885a07155405e20038940580680740f020032082c01c00f808102c268082c0075025030b00d180c9403903080c0700e0542d4008040c0f400181051102045000c820181503103240d541c0d44e240c88a42040544006840400c80c1e110014003801480607001c0062294048942000508204e17031125040d10b110340103440b44078010740b4541c0c0f40034200b00030808c0990190050b110400e00310303203450503400359180b2a4440c0c8c00064015a00620004095203000e004c070320b61014010b0081103500340c2c2e944d090004c0c0c0e038082c0c0361b00007400003c00500e105034404012400040c200c1000d002d414100366100503000c4e03100020003e004d64610314441440744c550041c44003010400c030405c8426 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 558007419 1250 558006169 558006199
    0x30509090415050601090506070b18030c010b0109140904030809031308150f27190605041406072106080d0c1406040b0a0c030b03010e0a0c0e0c0307120902 68
    0x1081c0d0581940b20300c50346400d020440c15442281350b1410303202c02604180c50040c0c16103a4076080300d0001d01819500103260014911883c050000d454030303065020000c605c3c041c140c0c0c0054401d08003500041c0848100c02120f440580e5840070454001e901424100031548400020508510070b24661401c2c0c260035038070000e1a03503000a030402803002c0d030154440d02c940b18900f1715008528142c0b903800c01c1b54402d411210300c809503030820303c0c0604164401c0320300702c854070100d806503800c40341001d85c0e59541d40e008000078484800c1044030350844200c00f4200500c0e2011010301459003c103000320000041e401c00110000781640044050a00c3c40200c406440c030000c0001c01d820024030041355240100c204440c001d50000a0b070344e01803030703002c0060394180e038414480100505c0715521840815403030f03481082c001d4400384600061211000094034000043e401d150f1208c00030341e80005441c1c180101004690017116050300c0d00180a842d0003520b000c0300034002c034050204c0080c0654072030049038034250 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 558008669 1250 558007419 558007433
    0x4030e030d02150c0901090303051303060f050f090c0a12140a0809031e07050103240f06020c090421050d1b030614010f26190b190509040305090904 65
    0x10700f02586444400d01c0e0b541c4110405080c0650381109021500380c0c0320600010380507401401e41d0100e003408555240e90b903600c42e042500c008108107460555100c003801004482220100c0d845644e9800420040100002042c00202180300c0d005101d45280c1140c07041001110b007031028641d503c0c0032100402e6082c01e205c00c00d41c3c03049215034428420000c0140c00e40c0c010841e0720700301c0410b140240032500c0c600070056001e0b24681005219014010b1882c0c201c80c030a060303480000d032039500203070324609042550180c940702015900f24070803040b003010080040d201800c21040b40341e80700000788000da8108400e0b01d4134000c0300550030400b42414901840c01c0c07078408407240c2c01d030415030b8184007003542d0340c4406500c145d80c00640782c001f500c08202e150910f4041c0c00032002c010019000210b98040d01881c0703e0341c1c100c0503205011a9a41000340e064080100d00890090080440d980c041c1e07202201114a85580039204e45c9018095603070004080c5401141070b62075004024002400310f20782443e04030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 558009919 1250 558008669 558008683
    0x10e0411040905221e1406012105070909111008071407030f08040507150806120c0102030301030b09070e040317010611070314070914011406120f04030e030d02 70
    0x140000e24000001c0c401d881e102030480c14a98102d42c2108030032845172903803c001171568551101304151210340303100240c43d580c0d07840702c06401c05000e80600d5041102e08007030403501c0c0c0c2d4505008651104081c01040303011480b041240c1ea84a00010b000700740f0b1030710541c2125810849a40070b086000e0344031881e030b0448551440350f0b41c00d681c2c10005041c01285405107008402000d40000c0c40c0e400c44480d5140034403866500140901d0031030304855554065a483c41102c080060005070a00050000504212044c8088010200003815110880e03c000039524001440302400701c582050100740c14800c244001000740410110f4904d1600c2d1030f0030042c1c01310350188010a40148036900024415102364410b00b007601503840503180007451900c42082c0c0320490124445903008182c40007070b0b4500c40d0300c6265481443c20707844241c1585028089041c0703900894059020703500c20480e1404103200d90140b00e83c010700d2110180580e03119030500b10b449810b02014990148100c40d0720036030082d0001104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 558011169 1250 558009919 558009929
    0x406120b0702010513020f0a03060f0e120f16030c0c0303170609090706050d11031f0b030c04030f1b17070602010b1804051005010b040e01120b04080306010e041104 72
    0x905068507481001c0b0300f00e032400c507035180040e94860054801403174070044101e0302c0c4030010000880303d41c582d04c8100440f00d100341000c880c01e0f510352207142c044205100e02840c50411402481c00e141043c0102c02041c0305511400858501d200001c40030540101c1a081c80d8641122100e04010384915000e0402c0c0081554040007940d4400002c1541c41d01103c070354403a54040700580345051824105468581280c80724002040c0ca480d280c18980c070400d00598400c5400013074048001120f84600854802e440e005500990001c00801184105043c1240c0c1180c0d0712911000d604001400d00244082045403a082c041c1c0480000155800601e210f805045040c4000e0320a423a641d03107009c3e4202c54040d0140c982014500f10304078030703020400380030039401801385068a05c0b505040b01414200c840c00d8101c0d482100d0041404e10604051a4000707001d040d10303008000d214041d50303c0d1505503a4004100824103640000080c0d6a0303413240d0b0b90f40741c80f14805030061180c1550344d05c9401c1143c10a001d8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 558012419 1250 558011169 558011183
    0x702071a07020f06031311010c0807050105100b0a0504050609010917060703051e06040b0103060f030804030606091122050411030405100c080c03040201031d151506090d02040605040612 81
    0x3c0c0464515180c0200c0e070180c1d11a021072a48019642c1e282c0e000d028111820342c0c140640c81c811344022070000301c000d200003441100006118500460041c4540c12290025021f6140600901c1241908601281e090311000c40d04540c80d1000d02c40100d4145080c0d400610b4a070f8a00079001040c500c0010300c41e400754130292814805581c4e00607484a02e07041903d02c03544050052008240c06091950144242d44410306d00804c400e91100c0f40ca52003010107a104a503039560001d410818081c1ea8424200548a140303014004503400036401d800f507000340c8247c0802c40f5800c1e640c489103000100c0c21140140800350060144034410851700030541c0007210107880c64018040d0301d85012143d403080b140303041010703140d404c0292195908400d09800041089043c15620342c0402c200049842c00d0151503000700004250883c0c0804000e080c01d5005080c1c8048040003c0c0c08600e255102415140040015121011a940d1a00004014103210303440550000e14180002c600c581b001d506070400c0c02e0090704 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 558013669 1250 558012419 558012439
    0x717092b030e1c030b1c0c0e0609010302010f0e030f0f071418012c0f1501030606051b12070503130b0a080613090611300406050702071a0702 62
    0x10b00652180380a0120f0b10346203500700a0f110200780039900c1480307000d401030200e800761309220b046080a4020f504c4243e071106031001c0204a8805003500b2140d010506440e11039a03945160f0020748801134080d1241c003401039003a0540c025031010482203800209041c101ca64505d841d04c0c400780c40d030721140140c404119898003031008070300b41001c80b440c6c0c400c083d04045003943c0c80c0840b034a060385422085014580400780011102403803100856005400d03142a1240c14200144401c1d400c01540003114141400c10000b08401078101d8150340c00c800c8030360341d03002880d41298034140c10062402e0034a80c8a05c00401c20390305001001002c0e00d4031348001c0d903044c03502c03589170f6141d007942d801000c1e42400050814030008030141403003840c0c13001c61a1380c20400302c0c200c8116660f9034103031507007450000340700040480d60250400c000389054005061a003100203031043c5106c060060082c0060014003035235242c40220300442e03c03c0041100410f070b800c0c0000c118610035a01c241c4240e1180c0000d03407140740c00e11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 558014919 1250 558013669 558013691
    0xd0f0c11011109010c050a0501050106030c0e0d0c061409030a122003040b07020a0305010515041a0d06150509010f080105010603051e041707140d0302030717092b03 72
    0x4802d03020b0340c00c41c4039102800c01205400440e030504054108460a0268008100009009025281c0038160548010400e0140d01d02c0041098260000042c415851405d1000120f4a102124004c4d10b200d1314220060480944900c103552040400d955014480c04002c20140024070308204901481951260000000341d0501d144040540d0950645a00304200400c001c1c092900203050451024141c10320156581c0c40b003908443c0e0454650b0582000140302110602e400e2180788841132417100310401a540f2000450400c00c0c81c42c2c00140700c1d81c0e4502d030401c4c140700c00422b0407008000080c164841e560711960040c0c800c2e9114811603c040d07090100124100d80280901485044105100240020060005d0003020b0003e07009550401c0340a040d00c820240800c01012001c1c09541445c0300d1034280d400b00e40c9440319994060023094070502c01d04c11a1070f4032180044003c0c0389823291200503143c2180a5040c00e895803c0045442000b100006640c0c103c440c4005000c000358404114003800c00d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 558016169 1250 558014919 558014921
    0x70e09010c0801121506060c02030106170304050405190c05220b0f031f080c01080903070c0e070504081c2601260d0908060c040305060601140d0f0c1101 67
    0x10780700c000041802c5800601c40a040c0761000c1100502030703521150507519003a1140111101030f00b04100042d00c95401d0800c3d401c090082000400c1240e285003c21243d50280c0c0382c880c01580039085c455074030380012800c810031140e0300030520424540e003003205d140381c2540a07016074441e4000c02140c1100460241d0b80d001d458812404403141100d02525229001844980313079880188042840300600b05580c0c1031030004c0c07814601038145407004200c07504c0e074500054013aa10007081c1c0031980e401003051800169001040004480c0402440703502903e9031403068900b400303541c010302014801c48100d607040c19001e004061014a85888020034000b0f012030149000000304080c07000032076030703600400040c003190704203880401c0052680b0080e0000c020303c0d607061040743d06900f00003c012240c1440501810300586410241c01c0640d41c0c0340915580d200e50302c80200074a042d0500c0100c1c02c0d40301190110800b240d5140c12040010046040280e00040c010138503445901c001902d416804003904c0c0301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 558017419 1250 558016169 558016181
    0x14010303141c02030606120f0108070b0414010c1425120b0f091207051e06010303021504021c200102030703171f06080105010810030206070b06190305070e0901 70
    0x2c507505904550480c011008043d50000d408250000b00400c000c680e030100c0d080ca41805a940c51042c85100e500d0724440520700380098215000340d11003000200002908000500701e131100c2800c000126811a0610200c010660a49000c8078061002081400c0403401c00881d46980c8255284041c0d82d04c612009481c0310001c20b00a00750340c6900c0210f181315041c2a05c50f60300410520072070f8010113000030814411b4201002c12103250340f10900710303a80c03440340140b102485580080144025072442c0c400a540304820854108411003040114081d0348465402c010b50724000480b0301e8102805180500c3c540b584012030460340200b104130441d00f0341c40030084414081e0182c2d901c07901641004c02c0e00480f02005090442440c290081c0403460101001c444801010303903031580d602172f40c03506002411025009120240c5c1402884c01440140d4409060320440c0d504449402069510300c808180042c0d07082e40d002d074081030210000400c00c01c00140b6502034418051900b00551201200d80c0e0aa40d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 558018669 1250 558017419 558017437
    0x103030c0201351e060d0f05100c02100b0108070e0f03031b060702060c0f0a0e0a180b030111040506121b07030e10021b040f0209041401030314 63
    0x140c800c04035009580f184450203543c2641ca2078400c40000c000700b02c41500080c01d1450140d0f44481020854040071303040c06240008261410240c1d00c0c508000060948100800002c0102500c2c0074060f06102d010050310350400300c078080810941c280041c001e0360712548017412812450601c070a4045652041c0385150064100d51180a03442411504004081440a00c165050300c82482200d9100590100142d00517210401500c02424070503402030401400510301c0102c00000c11000e1041c202010487c0c2d01c1060520f422401300c1e02c0307040080c1141d44d1a03482080100d60645104c1507042e11580b0544c0303130100440013041100c1d010341e04035401d80035520030164081018440042900c0b4440303209907005c03000c280306203a03100506a20b4034007a088054250001156881400081e0074402000e000d0010b083c0010208079a080a080c0d90519510111600680d12288000d0010f405034059036604240240240300d91714450300c4450381000240310a50001e80e9111002110b02e41c040100c2c7d0140c6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 558019919 1250 558018669 558018677
    0x23060306071425080f030414060712020a02011404050f01150b0a03150e0c030a0c08060f1909020f0c1c090b03150d0c03050c060901023f030a0c08010303 67
    0xb900c002d40c15100709000c50f6858065800320003600015000400610242c42c8030007045440e810075040800e2000843c0110a005038494020b0096054100c85001100d81c028600075a075548080700407400745c2440200303e41d55040040501c002c0000225080840c0e580704030081180c012110707604c0c1d00090b1540308291780300c0d80422080301e406100b03400560380d045d110107000286a9613903c4006101d1b804641c3d51408079400f006119807841240500e140010080c40c100f003580c10000001411950402100c0344542c9030a981c40d400342d00090000c60080c4205003045444808803400b0300c181d9400340120007024010301070302045400345810018888074040d0307100b401d618241211074074160b002510751202920b01024985203981c8201030680510710a2050716146407852401c030b80ba195501ca0081d11640d81800704910a9a0001d2803485281d8552940d41c101d0005407650511801c0c5281d1502420b00d0746c640b0f9046400d60701c0c0045014610011042001210350901103550010a0000030001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 558021169 1250 558019919 558019927
    0xd0320040512011e020408012009040e0f01020703080103020a080304061d030a0f1104050c041206020306040b0301021204050f0106061b03120516111603080c01230603060714 76
    0x103007840001c00c030b180b15180c000041c8036480400503080c915403c0700c0714000c29400050500050b0001e001d840901070402415894007041581c0c0d600c0503000d940349042c000d50307860340420f03804c0320100180080b070010140219595500b80c14002d02c1075009000690003810400000204030400000b120100c4005560b03000b85242d000d0b00d05400400181c00700c5515104011010000c55481445041d1891080b40c800580c5540041444141c500040150006420501c004c00c001e03588121131540c01540007000517a01e40c1c442002600804030ba04d8059055840850799024003c28442803038020350140040740d601d101c004900314285d0b0503170301500b40050141c00c3e080c007410b190401074100d458800d0402c0c0d04042c1c0c680030480201c8004850501c5611181030a0703050894000c00601009c0a0302d8000c0c212848001000010916880c0702c010828903000419844500007036200343c480c00c40c0e1a0040401c00c00e00070300711103131000c00c1e541c01c1d2003801880d0120704418050340e04c806240d00701110441c18 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 558022419 1250 558021169 558021179
    0x105030d050c0a0206160302060f04050d050d062301080c0a0504061d030f031b01021306181806061101020304050a15110d020d0c02030c031608040b030403020d032004 73
    0x3060b0840012100c29202d03c0c511240140e8854029001c4240c005001085450703040c140249410005450050010031840030b00c00450f002050506a692060401c00c0e40d41d4010140c0900030300041e442120700c90480500344440701d9550f03881000001d000d03641d881d03217902c811596010600c00c031410640860130400c81000300b2030044400125803100c13408038210014020780824100000c40818a0744c1d40c00009000c44280010500900e100ca1058021800e201070000500d001c001e090049900f400602080c0b1000c401030642c0d011f02400040c2c403209002140b030440d120107800c1c280a050042111100c00c1003003004144281d80c0b1a60700000285103080d65501e45000341405000b0041d4941d84505405084030105030081c0907603020b0a000590381c03130901c1800d908031000f10100c0c0c001c540040111070b85e030350710000644074100d00f502d400401c800310501d0205003d1217641d01003e10b0050100c20041070640125054103052883e44052264410070720a00300b08041c604070240d1240c50502042c48 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 558023669 1250 558022419 558022427
    0xb120d0c15090b1305010606020c1e1903050a051005061807050d0903020a020a09020403080d0f0b130b041103010f030f061503081c020f07150b09190e060105030d 71
    0x861104107000555010603110a50048400c8600071142e28055100703004100f401d2040100404251000e00000a890340008001580b54150201c0c0280c1e03082440000d80d84030307641b0180b40c11440303280311103456491070f2070f6460380824201542c190040e6884030104030801d0090902c036407001005204540e200540b200c0a0400240c14581001414842600e640519210358030b1414042e40080268103c2c40c410440360400390341054038014014082000011400d206a500310f21180e0b4011499000340a280c02c01800040030041c3d203c540d0030460740d51541164444004048113550034085400302d004110080c0c40284a1403001f80948041000070031200c06019411034481c2c040465000026050041c1c02148c980050b0745c90b02d00001c40549001c48580f641c014400b00210a508080040088140c10b015080d40500544014100e14101c3c0315264010405480d00401808003800c011000600c003205010074481c2c0d81c0d1400344175a2103410b00280711412520018014402c03000d0a10b070441d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 558024919 1250 558023669 558023693
    0x12050715030b06041503150f080601093c06060f02011503050c061b0106090516090608011424040f090513020402091f03141e0718080a060b120d0c 64
    0x5c080507a501c0c00c24000a074107400c1c401c0104400c001404500703003046404c6040c210306910666003585044000c407910080610f12603c1484406485d041c500b039000803c00b4290000c0100240880c03901c100840d801d5005407412600300fa0503402004124103580785c50003101c5507800013900c580d01100039190103140c40401045940c0401e03058494070302a1010590941e50305401c8039150507114020003240f07180a403c0303540b00b00d60510382544039910341400900f58980602424035003507001112038000b61511034104c180756002c2d00046258168501040c15a504a80130b6901404041400010348204600500b40660390344100b90304048840e03405c03c4002d5014000460f00910038a029885110550001c0141c0301102d4030040f0701d03060311881c3d440340180c004088440f11030a0150b2411b0058402e91143e41c41034060900c080f14a80da8108001d08550a134800a0144144520710040000b2034002855101c0165050025594040495900e60000c0c0d0305d034000042d448062a03002c0b8849455403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 558026169 1250 558024919 558024959
    0x100c06020307050d063809010c0809030f0601030b0705040803090609010c020a09060501031b020604020d05030415170114010807030f0b090a02130e09032212050715030b0604 76
    0x3052030044c0c2d61880b0015582c441d03200c03406e1074040d51040301c402800d10070401b1640781164072250304500c90700c0d9150340034050480c9180c1001803c1146d41c00b00802c8208541e00544014111480c2020054a00755100403d02080314a034880c81c02081046000d01c06441c240c51100e405142492a41b00501240d034100c1d99007a410441188100c3c005600da2000d540090055031f280400d07064102000175013500c68030b0185111444540582203141caa02042d12174201c0e904440c3d0300604419400d00900c0d41c0141e80002665001a012010406404c031400c14510081070785000000da980b21248040c1c1c03240002c110380820031180000340400c2c4664000c3c3c0300046041d0700010103d002c2e801207881c00c1002c952601d544c80d4000b500c903101c01c0306e900c8003800805211100d00154640410b0407038880c0038407104100901404094440004910030504016202c541411341000c102400d100b0f80d903000720301c0380e407a810a40000c0c0300e00c2a40709026800d031203040505401d00d0240b1b800540c082c01c1c10b00c1084c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 558027419 1250 558026169 558026177
    0x30324090b030c0423090c0603060607060f050a0c110a02030a021210020423040506030d0309080708032809050d050d0213062003031003020913210e100c06020307 71
    0x2180c11640d946105494603400003841c11380d611840011038101221010f08240c1c44ca0b80305487d010290365070341d02101e50041040d9925525540c0d58a08a00900131780101d00d455141004100310011540b580450001407003582c0b10307e030107541519040d0f00da400c01c2c80041d41541006510f0009810b25049180d801c40c1000e0443c2c0100f041100d1040407038109402801d59007911000c2d0303a04480e04114141802c0104032070400180c140800020354500c02c0c1c080007014942c0b9146601c050103525015180c8054100345c0e0540e407480c160984207400c180c0110440c4080c8000c0e203420110070540d101305440c0d1a0710400030f18044170307100c50030b0700c0f590010084050426020015080840c8095241c1c000a10468a400d4405010040c0708c0100080c001455941d9134014820099003100c440f02c02001c4a8040e152000300b6259410403511320980140701034000d8000c40124082c0ca14035650b030a041090710758451035130303121108c00c012000104a891a00282201540074040ba135182d0040d90020706c6820 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 558028669 1250 558027419 558027433
    0x2030103051e031c14010501110706110f030301090f060b0a27030f110103050a0c09030602090a0e010b180f090423070305070801050f061c020105071509030324090b03 73
    0x2207075051100f038001035512130035107038098148001012a1003d01402c424200780006006402034a42d40d002107225070f50410260314080c8410510610014030840800000d0742d5a035a10340c29524003520421050f8005249480b00c0010398040c1e080903140403000c9681c4a034251103d4032840d8921300e01c05481005011510741c030000c0003c0b08000611000d61103082480d8030041d001c4005411917000811241410341054103150302990712906074001d407540003000680321301c2000c010400e103121076000314502c1070b520000031405482c040302510040e110a0306d4003990052000a00003a00d180b108426006522134010074002042161006007140070098a182c800100600e001c0c40c05410707a06c10344141c1c0001030240103403042070084a5106e9000400d00b0001d050a002143c40d00002c490b503c10805002c5d42c0c29800c5a200c3c00450307040c550007200c02400c0d60705e140020801807000c0502200443c0c0782040d6510070648685400f9089100c85580c001e901d450854401d002e064248003480e41401216 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 558029919 1250 558028669 558028687
    0x1203071218120b060f010302090f1c0503130312030603020603010501122c060f0f16030204050a0f05040e210a020a05030d060602150603060103110607050109200402030103051e03 78
    0x42200e034141801501504181d00385103060004401171003c0c2c503410540100510f8141b030329002000307401100180d5400c00c1203a0b405820210b140d0501800070700d940400120300b0241c590307030442c0e2003d90303000311030a03c0c461900d040309030210740081c48020342280d401d1004000c00c3d8050610801e01541864011410170003a0f817849001404001d5a01c184104c2107100b0889000c0c00c0000c4c5034841d40094240c1440d0401081d8415015001090060061100100d0002030380c400d406540081001429050029488820014400c03550b8010280103d14102480000900001d584080420000a170000321046000d612030581d009011620540c440c000400380082e40401c018284030261120005030107040c10b43c003e0918400320044440c4142c10001e0000e0790b60003190241c1160b40c0065078241c601c042d003010a07024003444001808951030840b803a424426080c402c031480c3c2180200ea00744403800d403003c2100701d000c2804040d19507408030591400c0200f100101ca481003461341c08581c03c0610300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 558031169 1250 558029919 558029939
    0x31201230a0305030a1412040f080d0c02030a030507031506110c090c04240203030c0d0603050a06050910060f1824030209150105031506040b040e061203071218 70
    0xb50300444059100240305140f0075441040300205054016a4038a00030f05d60a51644c80d120140028013644928485041000f0303100c070032500e607541240002d2185102c03840001c0d40b2031f0450703c0341901007810a00021079182c801c0c0f08054500340e0340c001000d003560500c0d00856503824850f5111040740f10b0050380d1a036950340c2c029280d06c42d19400d202165640d0520b803200684261140021510481e090f035143c601039004416130303a0111880000c541c841da00c02c4155000b40002d50f2000d030503030082c00041c009000c00d642015100e410307030900725260b50309106c0c1c046d0300f00c0e041c0d80301e08406520702c4901881407015212014032107081520010545202d0000c03040020801e038400068150107209003041141802000346504c00c0c1d44041500c05030f450075002900d40d00c8020540c500b629001151101144d4505060720003074412044026151070303c4054141d81228180d0b1214400d8002c10700084da807000020465812580c0500c00c0c800e5061800c4d030603110a0f9007504100c0c1c0c0341403424004220f003400303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 558032419 1250 558031169 558031189
    0x1609090f020304050708010506090a0504230a1b060c080c0c0907020a0b07020c1305060117070f09080c03030a11030423091e071d041d06010803120123 66
    0xc03032600603a00d040030714040d0300c0c2807201c0c3d1216035a83d0400007004030079600e10791800d0340314943c000082031981c0c5510700340e040c3e40031044440b4401e004010b082082000c00003190380c10b1901c41c28101001c8100e4040700c0d052500140728002c0061788408442000032a030f64060301690114034100d40d80050b401d0000781040c0d03811114000140e1190303045100740320308656081c2d0401c0c8980050b010183d41b04011880c0800c000000e40c10542d2540c0108165910900d021002c4a40c0d0f40c950292900307040c407004007100030814062000407202c010204030080d0110f001c1345142c1c0001c00035803802e20040015a03010b22800c08081c458001408001001e414405c08068018070f50800d046c00240303a84200140c20360054200c100c0004101c02d51000c10f00c03003480381c0d6000b010380d05120030040c2c1c1000340c000c0105440555543c0203410480d424007a180440c0107041c6070080340c02518100e03030301c17078000541e00e000300391907074041c60cc0c0c8000401503000d920a000b41d03001c580d1040407882c03a000d140030480c5c9600c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 558033669 1250 558032419 558032441
    0x90705130e0a032606030309060c0c090109051e060319170a02061902211009020c0604020319081206010c0b150901090905030702041d0d050415090e160909 68
    0x100c24142d11405000c010b00e1389848030100103126045081540200e07a0783e02500c88540c0c0241000960b401d80c0315002c220380b485184004203d00c4007582c4801a4801602040c0c0726090410700078559035001b100d942e0070081c8910350150040401816203070280321500c00441050755603050090034020020001802054000203980050886003002480821340310140c0c85034012141c03061181c148004a0b41030f111482100c2d840529050b503c0f00303409440203540e1a849071b94007901c00a84444001804100d0078071441c021804c0d10010910304071069035210781040014108401002060110740001350441d421420625040b0440161569603161612042d505d4a81e1040c140c503503103445183c2070202d80e01401c8804801d01403d07500e17035585a900c0c020b903440244030350f40301d14000c40c2d18000000c02d40d01d030a681100b11960b8150b80350740034045602074020400444d0141c0b280048503409441900c003284c01e0980080c05c150ba800702e050840c0c0480d040050100581c15600250301d001a01070b8800040e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 558034919 1250 558033669 558033677
    0x8070209060411070201030c30050106020312040609050a020d200a080304090203131b23100e0409290a0e1906020c01050a05010914090705130e0a03 65
    0x454600410035012802800c0c0c911460800000c03202080a0406495a1a6080c240810349003201d00c01074900c044d0644040420941c0188a01c3e055865444407007289107400000b040241d032500412600ca100300d645011009070340f1000b240015071075501c824810b80c040d8050307810b61000c0c0d40c00100702a4a048040d031361500d5040320301094502c1c410966082c6242190300700d281c81d207070180f1280c41c1d010f188210301103160b0110010341c546005998842800d0f51000c3c1007030007001020069020640c9a000310346802980c965082d00c1c0050340249028481c6c0c0090811140110301d071011030307803e0340b82e40741c1d140c1141c0c998211600180701c02e0400a0070b240c003110140aa50b031182510441e184000380040d403001d0030410100f140040210b9415070f00c140218504010304e5942c00c1400191085d1083c0d1106980703024104a24454940e00c00da045c3c8801c030300144150b1401e60700c00f024151040da01081e203600510010852884d00e245002d140108240000c507001400e80f1a0505110311044190082 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 558036169 1250 558034919 558034927
    0x305092d2e0506120c01031a060a032003130809061209011b210c020f0a0605100504090c06050a032901020c0d0f02010f140c0705100504080a0803040807050a08 70
    0x4401d5004465101ca41901d1040115010884041c0d403108a00c1d12141811b036180c500da80b50240d9804610700c40840076013a80d54411000c900100240b219212040c81e107410b500006108107108000c4a0240b0403845c6100c0c001c0000d51150046c95100e004041e40c002c40810285001c501141442446890341900024031003403d01045080c0f5202804240108604500c60b01e80c1c0140c8a040549124024180000c00d9040490140d00c0c1c540c0180107803500d80b050a15030000c00569412140c40740040ca440f900000b507880c1d007032000381c40e98044004c100c0e841030442403003401d20540240402080503d000b084c1580003c410114001501d5101e010143c07a0150381000755804210b20211000c0c03d507004010a0081d4603040c00e03441003a08001d0401101244000c07103148502c0702c9040c80c14002d984e403940c0e0744481c070380a42da030000342c0b00d024010b00c000030002d0300c2e860085007981c084501c21000f45c44003200c42d594032030107a4401401101c2c1c6c3c050900440001c10700c10040ca4003001d204101d01c541d9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 558037419 1250 558036169 558036253
    0x615030c130e0a150f0308040e0703020f07080c070b0f031503010b040905030909060d0203120307030906020c0f2a0607080c03070812010f240c05011b0305092d 70
    0x4c50301c1c0341d00031405100c1031180420005000c9011501110341c18410030805484001c000c4019104020b001d44908201051080500c0075a030002c1905138074800448c0d0810796249034052090140c5000113069003018000500707041c0102d80c0900742c40000400024ac7ca039500000182150078136141a100c2b540b01048554090403e210000e4014000b00d501c07035010011030340000d9640f800400c5200c00c040006c40460f0500703000340c1000568661084003551940280c02c0340c1c0d96270b0502810518058415084104881810245a903450050368000130302d10410032001d004095114036405c40d0301c10f13010000b841c8210014000f41140d0303481620a240d8618011042c0d4900303110680041c41c0f168203c081c00c00807030a07030312400a449500400e000b00e0500070800c060380c0030001240d0143c01c41d42030010311941d41c00c9250084440c04d5054608000b5522514002a56840b03214620501c0d06910407448085040c40d60107151500460000c9840c030a4410a13403000d082c04403c401c4002001030401048 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 558038669 1250 558037419 558037451
    0x3011206050f132a03060207110415150c06020d14091c0309080913050106021002211b0a09241709030c03040e06090615030c130e0a 58
    0x140090040500d4011418100300e002e49072060b03d20300800083d4244000c2914251078180307100c610000701c80c07604195690307007000f00281d03200400c110f50a80c000c18800401c1d280c64031860300c084007020b5092841030b0800500c00c0c5500d45070901c0c0400d0140c100c6140000502c1030004103035124461102148029186020070210540901079818603044100710a6041c50078101d9043c14050303c1c540072030f038010745081c21010f91144a0319070350421241208a21100c000380c0090381200c005908031000000002801d03001c90042c4520b00c1120340c14583c3d080e0300308005070720840d0020f1070a091044513000704207102c4102e030f011303920320070200e04515070400504010030b0045445070350030300e90342d070f00c84042e410014a102d00101100c60242172400c0402c1d100d080420640c0d00340044803040b0384d966600c44804a48000e01224075500c01d01c04540091601d0030610b00600c3d14040d030309052070458a44007056001c6411081c0d408034511240d420000340840310802c0980100c0c2c9124000030210201e0014031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 558039919 1250 558038669 558038671
    0x3090405070f081b071b032d0b060105120a05040308061527040609090c1424190c03090905060f1201020c0303010b0c01051b0910140301120605 63
    0xc0a00040c00c038181c00d402e4112080c242e0180c0c2804070007802c0d009010943c0040c1c00381460140454050032481c4045408806c03001c1c00760b80c0239952a040004101072900e030100c0f0321a443c80c0c014441d03020070743d0004459543e8140c010005060450408050300d0001d211444210b4100c10800d031120300340f100303054005c901c00790408404c0d070b0002e5040c80c040303890341003e100f002b0314032003440b4030500c443c81c08034441700c0d04d101030030002401807140340d50321100030003d8038a03003809a6440455810000741003250090f200403014014241380e00056600da508c3c4200c000e00300780307461413a00401c054810200e501e22806800b201c03a464a580400c0b003414000c15401c116041640a81e01e01001c0c0001e41d922151407400d0000d0032244510404100c090b118003901070311165091601c00880041544006000a0058402c1040c02000a40c1d200c240038115000c102c1c40c042102d1600300120011410b01201d82c54042d2520708010304e240c020700d034040d81140d009a00c000c03880c0d80c02c402c50400b0007400740101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 558041169 1250 558039919 558039931
    0xa0c05010f08040b040f060509281a0709150503160c032001150602010c020d05040f030b0612060115021b0303191101050403050406080919140f010e03090405 69
    0x5084468400c8010700070003030150021342640f0307081d80050304006a0344081103c0c2a80008244040c2c10504080fa0340c030205020904420480703c0d1240d55810424100d40182640054441f8112680c4c42d824815524000e4660410080d1045002c0382c551000400001d14000c0d130317980c0581c0d03803901c01d0080c030811240951303040c1000036001e5a0004654000300034128001c090b04040311031010b902c14a401400012045520720b003002000041954040d030140030f8848a0785c003510000240d06800300c07034520139800340e00990030350514203101003500308511660260018105001d41280303007040343c2c074046090340301e413241c484040500150142e060082c0c5a0340040154204160796503c4002038590187c0d40b0b480582a0864200c603954500c03405211704000c442c007008111908043c100242980e10071f0048501145080700440d903408000030f01011403100b00708840b03c1050007079030f5a80308a14200b001c080a84201c260440c07102c1020311031900d08144050055580b26454070034001511030081c60 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 558042419 1250 558041169 558041177
    0x8010509181f0b0910050f0d0b07030f0b131d2103040303090c0f0302091b090f0307090c091a040503120309120c0a03020f030a021203100e04050a0c0501 67
    0x4601c0410000810090003040c0200b0705081d403040c10140001007a200c0040c95004004000b880301031740d9848200410740b00190780e1102c07041400e0060000c040500700700101040905030000e1090751083d4030416000f0412140403920701c10309800544101c030b031100c12075000c65944c0072040c0d038040501c11802c64541c603000646140d8100c1c1c411011008a02c9500d01070407100040000d00701803090b441540a55400220855010b0319411190107801607404128098860310012418880064001c031222040e8202c0d164039140d5107100340449601e0321500903800d4030466501045110389801075014030303400c0d907468030303565494058002d58080350500c01d03101c0d1b00b900b08020300080d24007154003a0385640c621040c81d92511030440f42441c010600d44100c00c0e0801c04210320405003030200c0c10700b042074000c4d803c4034140e55012103402d81300c0c81441451000341e4000e031180b4908200c5d207800746510941c01c0301c41503500d07641c03403401d481c0c240c070121422101c50300a010320310100071000340c0b00406450280b030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 558043669 1250 558042419 558042451
    0xd05010611190c0801020c0304030b06010512060d02010c0c090213090c05161401050403050306010806120606010c1515030b152407021026040206030f180d08010509 72
    0x4001900c2d4000080c601c03502400490128003800420394000e0018981d11008640d21071004003a99165005800211410b00c00d0201241c05584204199654655418502c55030b80d00c900e0304001801c440d583c0104c1c14014400c03030102c04154241c00c100001c00da4041d0241c0c0d40c840d00d041c80340d19241340d40c01504801c0d00e040046620154404141c4480d1016410035035501c403094142011224250aa0600c20390f08000c10002019480350103035001d0781081c0c0b602201a2500007c1207500c1c180e000b22003849a00c0440059002e62141c0c400c0c0202c9400340800d2095000c80500081c151801d10350084440207400e201041000100b400050b4883c018451110039640c81d000040c4036090030680d02e200304c14181c24201c600d003003900c0469078940c0c0d00800c0b1400c0150585000f80030309040101e1142c1c03855482c2d007035048400c80c000307401d441a5402040680342d0381e509004a412088c01a0142e61400c0440c4201c0c00c4a00d810414400b204481d030b1070f0014590300d03040c1044403880006080b402050143e00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 558044919 1250 558043669 558043697
    0x402040b28290901090b0304030203090f0d0203061506091e101713080c060f09010f0c081f05090a0e120705030726040902030604060e10060f05091002030d050106 71
    0x4048442e107101c51015940c2e40c1e0b039141d001202c24075000c2d08101003001001080c0402c1680000007085224070554403070400a4281c0100408100c3d61340d0003a4041e04a00c0006901c2d04c0007a880c242d11410041c003203810214004041422030721448403105aa24807440e440520b4078000440e03164034485417801040c02d5242c942100072401d0003500003010f42c40c030f2900e03d1080280395400c1c2c94141c00914100c030082d1801e071449001c181820303900d40c2099440d1211260407010700d030080074200c0da181d840c0d0701082c0d220340700700c403d00701407043c0c1e44a8181c2e0030130340114550741c402152500400400b0404590101d0154030542000b0486846a030040b00070425100003410100035a0745094104001c8445030010748100c2014030455600d41c680f2250004011402c2038956000d1801220f080c2d07000c20030aa11a016050b02e881c1c00e5524104036000a50308001c2c142c8607450720300220000745070260500040c000480d44180820300c814000d40c0001ca0841d414410434840c05004104600d41910801401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 558046169 1250 558044919 558044969
    0x408131206050a1b110a0b07031b02030a0c2010081e13020103020c1005070c1103030a170a0b04021308061b03010614041206090203120301080709050402040b28 70
    0x9094080900000c624a2100c015051040640c1d1b16048403a1000d03a1a105900030002c100c10181001d40c1d40d001082002c40501c004141c0348505682d459011402e041d0791580e01c008121520240024109a11491000d803100d50400c0101c0450740c07a030743c0650400318501e911142c0701c00d24100d441c102e048100010054461400c01c1d10340d0b020f0078010303640c0907101c039001e0921180807078400e4041c1c00e007418001340e10ba00a00002505001e00a1303180c3c0055450300705512803181c07108500c009440410101e07620f50b0101400c85e085007900200003692040d52001c5010b0740c014006044400412072010010741e54181711243c1d02440c1402084090f0604412450582c04180181d008129211030541c0b004850002110302a02a4a42c2243c0303031459490001c0c05446070460880c0030780900310b40f07144818044400d9138140c3c0d080300007030402c850900c6801002844000e00c1641e12a80322180d5609035251091522054209481011034480006d482c0d1654100e690f480050b03880360750120655a4a41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 558047419 1250 558046169 558046211
    0x212180a110418050a03020d093213061d01060512041509020a0b0a02010e12040302040b040b1903020423010302100c020a15020c0114120408131206050a 67
    0x720b50000d18400090f070304002c0d1540b440c2d07000381079200e0788041ca0180740c2c0000c0c0130303d0610030580c3c4042d90b03292a560300003214040c43c41c00605103407960781031041a81c905003440540e0803024107225814000914010181d400a07480040c0f0300c15082d070708400c49880508614090b245d00e0822a00d01a000030b40c5030002c9130020b102911445c1c44030702d459403103411504118030341a0010102e2801c26107940109120f42d001e0740303607130000d5840c121001403200004556030788041600111142042d00e503400b400040c0160301d60b02a8070954485243d02999580321107250f40395131a074001c40d802c50451040c0000c8075008520444140584c030f01e140340d0200d01c448080e06596064801000d07030141c5100070b464a000079580258030083c000c0700400c00700e141c01c00c06541f0f0440b030f0b400c03600c0401c5d040d00103490341200c3c0e42d80356414000070032003d9200740051820381c0d0054864a0510710300760301d0b03d41119440c496504002c17194595490b90000340038071030007030a4120b448000200400d0711000200011012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 558048669 1250 558047419 558047453
    0x1005070b060307050a14030d1b1412070303240b04030609020d05030c03211b0a121a1e060901200a03031b0216050409080c010212180a 59
    0xd90300d000a03610741c0301806607400074400074201e4a00107441c0c102e842c41c4032842c0301445000c2e01c11071011900192081c00c1c0c8002400d070590003030740d2294240d294522541403918103c51280b00e076103c0700080b011140028880240a640c00040c113541041c40220761490705000d01004141000040c03001d5480c9004036404c03603900c003400103220b44551003c180a0f06040d1006000790101190082c04010044000e0903101007404880304458803504082c5000507058402c0e140040c040c06015a0344081c02000305800350b00780c1051140050b000e0005000d481c0d4000c078102c0781014020303c3e20300038104001116110302460712511030035200000880c0c1c041c011303000710714104140501c01c249442c0c001d000cbe000301001c5c02804c0e40c0f0303496050708015024058400c0554800081200c06c409828404500e1700d240000d400c2c00030420600c1c02d010031000e041c12540949000908000c0303401c80b000240f00070262000216241000c80c501804030100c80c21001525903250b4105210b00300c0060650205000d001e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 558049919 1250 558048669 558048683
    0x80303070513030803011d0702210d090c0611161503050c1b0d0905010507050d030e10090b0a230105101b110301050a0e06040803130c0b0304060b100507 67
    0x120102c050403442c40c0590700c050004000040003040c50801442c080010000e103030070b02c0000d601c1d1010100d0380da0300b405100c0201001340d04401e42c0f4000b0250700410321070203683c5011030140c0f9543c6810115283c40e51001001ca5103500d100c104800090000302440040c0c1c608004c40c40b450080804210700c8070042180c101540d40000490032040c2100742d4040c80300c11a078445081c40040f000c40da0310004151b41c0310118401c00800103140d841a0b0407540190f50220140c4440c80d0610030a9014180d91541d20070b15014501c6550715020661080782d513114050060007001e4244034000300704031480100b014000c5201c0b00c401601a100261850f41142c806841d81880c048862404544404c1c003010301b006120240c69262080c0030340c8228100b03000d04102c00812507074880d8014a01150000136071001c1d250485000074000c0b1f803841c00510740c03040c02803858103c50380055441c138007211015045900080004005c4c4020300010b845810310041e42030f00e03005a010f0720314602514901440c2030060040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 558051169 1250 558049919 558049927
    0x402070804080604062004060509040905010e030f04030c06080112031b0204180b01051e131b020714032e060510020706031413080a0504030b0114090a05010803030705 73
    0x54450480340240b901e4801e40b080c1d81002e207801700103010700c44410344072080140203001c400e0307141000711800c42c1c0090701c4291800740603509200141500044c2a2019541ea00328030756904c105000610141d000c640f1500d0f074490640c5045100407016400c40410480c101c40144007500d030460043c07225940500740003000b40782440c19250000081c1d50000c2d04a81400015002d2003040c0c00303a07111151060190041c582c0c2c03154103101c0f030800002c611400c088210084022581083c002030046502d02520214085074446051030110107680e944800503070181408215100700c0aa04400c41c1108030050980702e01d020150000c0e00e1040420b45200341440e0020481002966001c4401004c0250140d2500300d245407019440340f20620984001c64145004d40f2541e03002c00e041e441c411100000d0701c0d500408a51a0812180c000480300d0051020400020006c01c660080c024000c0075443c0d51501568640e009200f50844094400d18070305081000620a4002c0441643d46c0b0a40c907141031925 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 558052419 1250 558051169 558051173
    0x6090e0714091f15080603010903090611030403080f0c0709021801110316080417010b15071a010f030614100303141209062e0b030a1d0f2406040207 65
    0x851800016110901000b02c400216100040c160b511181307090740360700001d5070b2900181800c1c1d03080074400034001200e020041c0b0001d806a000e00102010b0101101e007001e85954840146034400c50401c80c0740c08020402c030402308801c114000150003d1007081d4105031500e108882001446500c5c00e05000d401003a02000c02410015200c610b0003400203004000c10310304148506a0050080310800c1c01c220144840c0c0001c1405400c41c88403001d01810391010550907a804a0780100408070341c840a182e411045a00543d080301d406032440c1281c00c00030f10b2851900000b00c550b885101401046980c04000383c1740050500c840407682c040c1081d5154410601446883e0f22030b2082004903000445c0500102180010300c26110303160798051160000103e4052800c507068040c501e030b5030034500a80c07e000c146003107409075400036844c1c2000b0841d260403d20f0361202c40c554181c14034041c0d0001c1c01c440000c3c2e804010051046241c003140703864407044e1410182c08000d00403d554051500040c021742 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 558053669 1250 558052419 558052441
    0x2220f050a0f050f010c021908010c0203041a03070207030c030606060207060c0b07030914070306151a0d09170c030702040506120c01260c04090f0204050d0f020102100f06090e071409 80
    0x10840c2e40c000e201323400c0702c450400541140003071400b50b000c456117410b0301103ca480c000003c42d415984130307480485c0c2c0e084007026405c003581c3c00100220f0450007081c00010002ea0b040e0750080185115131004030f480b0f402c040c0d0003450040039920500403c00f05440c1e01300030840e110000d94100102c1d140100300300c0d0340343c140761958101207541c451480c8210440001032000c00d500012044032420601002640c1e200280c581f0000c070180f9110500400b0061540d080c0b0300c0c2d9100c0416988241542c0d010301a241c4c580c602c89400005560340c0c4e90b00f00244e80c8046143c14882c02e0f6006a007116007040c1d400c41e0f8411144d43e10b0940844505200800785c071180101c02e50b556a10f0002c040c0e030000821131901102005040d0001c0c490284900d0800440d1141c070400d600980701a94005066004030a019440f030120074800c65205030f0541c0100c00c02d400d00d0514902490340f580a400c900400c01d90b1501c44490211038011a130011140c100d08000d00c1414040081d085101d001210240c08a40324480910 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 558054919 1250 558053669 558053687
    0x1902040303170a060512030a17060102060f13080409020301061e02060a0c03090803090f06150f0120070801020316020105010e0c090a0914041e0c030201110102220f050a0f050f01 78
    0x17a510480100c00d00642e0700000004040822003a541c6100d11142100003841c01501590703500d000da0451000210700e07603c0c90a0b07440d8042c03543c0154143c41c0c0803503181c01d0003039840741e0000c1c034000b50000014000c040d04120442c40d80c85c6000301034030803100c903424020f499102c06800507405549465941c0c000c0e030b210303801c4402607517041110aa80c1c0d0808414040e9200700740000e44100c0d01881000a2a42d500d142001040c401c01410922400288200441f80724500d00c4801400100c0c0324a1320024080800000b07010300100000143d0341c2c28485070700d0020344840304400e030440e81880010320005182144280c0c004060360f14068540da0004c0004827900b881da000140d10707928203035000e2404001e002c11140200e010350324441320605508505071007000c900300f001d0300c4055400070400042d4414401e11003a02d810900060808080031803100304107030010440030300052812802d01407000320055460003488200c800000e441d191407100000501c0318403030b291140715520300c0682564001c000301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 558056169 1250 558054919 558054929
    0x1003020a08060f0f010803031303050c0a0c0302090a0903020309090604020f03090a0204050a020702010503071404120507050916091202130501060302031506090f040209190602061902040303170a06 86
    0x10801030310341c103080307944180880350341c00c030a080800420f030311010320803850f410703920040701640c510781e50060392628045032108124100301003000741c002d0000c02880303c440e100c0d1217855004401460341c0100b142088002c0e204450052038070703410b100041d400004403aa40340d4203032403e00c0c0942c1c0b0305000a00a00030251009401c0c00f0001c2003009909002c2565034000c0c0c402c60b82003259840d8407441c00100c0c06400e030000d02086041000c265118040c0030b01040e070200c45520356192580307031003105400c1e9022400440d1554884c0d0740c103004d145010380e50a50f01000790981c00c968145000750040031030342144101501d0741c8401c2d031200c040d92683c0310111140901000280440d5951301c40003402544100c98010341d40c0d1040c50348074003d24140e411951314040081c03910a10025440400000794015880340b50b0054070865094000758072200403800418164004c0c24052400f2960f56850030603007207103051440d20401050001941210301d48007200c1000108100035900c0c0300c00326000700019007117 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 558057419 1250 558056169 558056179
    0x20d0804080d081f210204090204020a0c051c0c030f11160302030d030b15090a030624060206040201210e01060906050406050102030315040e030d02070b06120a020a0e100302 76
    0x94920440c1c00050007406400311144c840300902540204021004050060b0b16035600c2d80703084403030001c204031651110a40014800500740f00190f000034120390003411580040307803c155501c800e000d0140301340c18000b490783e1248107910640550003450980052001810300c001c000300500018030800101c081d07015010200c8a80c09002407140c0c54001762480104c2c840d1084103020041c0c45d100703004085407914042c01001c188075102003880c0c5650400311175183c00980c840c4c1c0001c04a0400d0184231900000c000d80c0325103100d901540420b00d0791180d003001c81507600070340c18040140da0000021421000c00710103a054900b0821803030026140c1d060701185690f003040301c04101a4147d0f80b054044034000c0b1070800200740d039600160b880e800116641d0403142c90200308203e490420380c103c402a1000042500d1524145038540307012078110f40c1c0b0503114100207000300f00890400740c154140c01442100107104959450340069a006054001d80160000c40400b00710054680d1071a20055540201 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 558058669 1250 558057419 558057433
    0x4031205041b0b1e0a0c0c030f03080f010b0301180603050d020d09140108130c0b07110307050109030f020d050106080f01091106040602031920010e100513020d080408 73
    0xe1041512102c250040b40380000c0410008407011884100d031110081c00c40c943c0d040100c004120b0400d6000070350b0366014024000080d03400544106224006540705216030301540c40e0301d04000300300000003010794102e4207a810041c00301da5044d0b07064a0440d0302a02201110245d210222005003101c4d500080c020b2261904003900550041422003c0d100c280d5904d050181e9a0504000384028044405002c240c00d00041490b803040c849000400c9400750200882055540b502c00c1c1c903950005e403041d60000b0502c00025020320b014802c601c02000246081c0c0101400d43d110807611a01c0640002c0c07050a40310b2120702088000c2d0840e03001007003c002a500003d148241c040d010300081e41c802c403000f02c401d000390205868840c0645040c0e410382e50080d41425116951032511720450280780c0d080c00345860a16100440c000401c1e00f142103014008244003e010380340342e00d07100840145500c040d0030a020000046c0002500581e083c0d01103a038901c502d001400c0103107443c4a507421260007400303216 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 558059919 1250 558058669 558058673
    0x8210106030e060c0315011220041505120c1602030601090b030c030a03020c0915040f020d0e0a0b150a0b1204050609150403031d0f1b010314010e0403120504 69
    0x40d00c0b24545016000c29503030280c1d550380341004a84000c540200005100141e140b8055201d04100c000550f0020320000318003080a40c0b152000b00c849910f404c071188002400d1010000b24410740ca5080058100a81014035003542c0c0b000f4418018012a4000808034003484c81c0ca413182030304940700390050291f80c01c035616480b25401600c074044019010f4420024500302070304002844400c0141c0681c090074a144100307040011085002d024a0b4250a80390741003111556a40726110607a810342500680d1591401111007d0320310740300580b2010b400c02c82501c40072170508045a540180d03003400701c564210701c10b03000030075031000d94020703840c0c0d4480402c24140e03800541c0c50080c0100d0041d81200e4a5590744014155642d400165240355440d4000100340020b004e504140c8400c10508148448000000f101502d0000718040381081a4424806620240320800b0150410a001e10302404450310142c03001d00121818445c0b19542c4040c28006014140f260400350071140b04c6001c20300042c1418 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 558061169 1250 558059919 558059921
    0x616020f07050d2105040f0f05030303070f1112040609090219050c07031e060509032503031e0501090501050d050705090a0902090a0c09060f1b02030c030f030c010608190821010603 79
    0x40c0c020300c1c4001521b031401156008d103a49811041383c00060003907240d0754400c007080f2050455880d00071306100c0000096003000304117201e869850140c11100135241c41c50400000c040144d164825111248100281c45441c80d4403201c280c9041e481c1d00b001a501c61420901c9450101c40e0343c80580346114940820030101c407100e540c000214002d61042c01251601d00106450b485030380240c540c0c401720401c6540040b441500c143c85d074240603060000d14400c0d02c09032601c1c111191010303898810b035502c2c018000f2040c984101d602520041d1884200e010103690340998031815070042071300c070f101d2400000e44c1242c4281c20038003030280d01400c9000303d030400f00c5400000e0180080a00301003824243c0c08240f09200f15003880d02140e0307690301e1481c0c508041081e43c440b40303a580c2003a82c1600403600002240e8404000c135101c9244036400451f81c807d00050520300311005034010800c0c03a0880c07400b800c0c403405845a07450301d0783c0d0003c5101d9a030385c80303100c4607100c90740aa521410342d1107188800001c0140d05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 558062419 1250 558061169 558061177
    0x60306270d0806030c040e100e16141e0312032203050d060b0a090e13060e0309040b030625090306090b0f0601080903030a02070201020c120616020f07050d2105 70
    0x205900b2900d03441c1e102c05c00c11050317600c1940300203943d40c043c0c1d0111044940c2d9070444041c81c03082000391801c544200d8041c0000001a801c0303018040000300da80c0e1947e051100c403145e440e050307040300500403020100c0000d80b42c00d503203aa0300429180220101d040745107181040c04000043d80103c9518071558500980941c11001c920200706140000c0001e14040d401c08943c0000c00e030b607417171405aa04005512019410152000e0100340c8200345010000d4001d02c111241002040001d41c2c40d59000410402500da038031329068000d41041d0706002050603c0360051003400c10344407a0018104a00034100c5028525520140800b4100400042800008031181d17010320850444007a950b81c2d01c6005603240c28003925000002c1d4410400200311100550181020920520503100c0c410035440020310003402e11038503101903400031801d02a101800160b42c405001a5001600d0302c134400b401c2e0f403a1201c1103481810b01440200366510304008400360020b840c03c0404200000c411400c0030000c000d908 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 558063669 1250 558062419 558062431
    0x5070c1e06080f090a150905070b090a09090816051c051b0a1104111c0204051c080403060513060f0b030c010201090b0406110f0a020a1a060306270d08 66
    0xa2001c000c03c1140c503201c0750191080100301c004140d40c040d035030350302c8003418070142c0100c404079542e2940c00d002403820b2041c503009110000d4a10307114400c540c200046480c2980c059031700710380341c84400000250840e096a11b40c0100c154001c1051819051040c2461484641c1d00d03500551040748100c40c94101c03002c4c01241680d485440340b0051791001440d6944804035000d010201003150b1030025280079044405c00f440d10001440c200008541c000340b907280480c4440c0c003103a030045400e00c01800c0041449240c08210303600b00b41c503d01c0a0f180c08505101d2404050401c07526032000030700340701803d1041190346600072410060700030708a00314001403524480b1b4a00c0f074056007400050b03540c0f050280040c0150442820b40094507582c2d00e50b40100624050b044000c002440401c902e980098050146c422180e0090039680c0000d15200c01c25011010b04880055206000d01110ba00d0009656a1102e142451040440c130b5400c1244135020380e0340e440d110944039007040486015445440380d40146 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 558064919 1250 558063669 558063677
    0x4230d020d061410080613080d0e10150e0103120504050d0803100b0301050a170c100504090b04050f04080a0c14010603020312070b2701020a03060501170705040605070c1e06 76
    0x70b200c130350345104805550300c1500ca841c1d0125000c10141d0b02218110500c09101e4030015241c251102035940659541c4071501110703070481059884800e005000d01c4e503440325031704e400c1d240391420b00d4450400c1107018003008c1c010400d08881003801c98011021030f00601801003407445109411310301013005600031a805090303080d01840002d8588a540d0a40e410f0312002454075008a041500200001a1440c1c41c0c0c24548100400611251a030007941c071800082c03560303420744d1981445100c0045c1c401c201c0b0402d004a25110801032003680d9103408503042a44183c00d5561821481000c480c43c228810000c2e107509094800080c4400d4158400300440c2e20036015207501c0b42c0307131151140703380c0540c83c40a0044400c0c0c0000a0018050011000f807011381c5003804449111140003040c04c81c2c000e601d806000c81e90343c80c001d103d20340c1c0003c0855403141c450140b64000b8504244014498042d5200c1e04050000100d207036010880c002d0044005040d10042038030110075041203012402c41540b068034081 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 558066169 1250 558064919 558064921
    0xd0f02040503100b0310150b030103030c050613030507021201090218010918081912050a0b0f030a0c050411040302040e0304091d0705100309050313180204230d020d0614 74
    0x20351090103607101c02c4e00024050842500b02c19840030291410101000d490300000a020801c90b42c0c45010318040d41c040c1d131301d5403441180c924100b8682400988003184a54603d03c0001c0000c1e48041100e00c03059050350012107032a1540405405803040e450300070b510034a40307104603034403003a64586181210b202c80c0090281c5800f81643c038114101d81480506000400c2240c1c00258941c182d1201c0c9401e00d51600c026111840c40071001114020340790514219200c440c04a02494242c00300b440e208022006421030382c1c0d40da0780719040c0340b01c1c0b0b2143c1c0d1301903a182d10f59900d014980c20141c3d0000d40d0080c00030320030300b81d40a400a4407580203029420107585450b984054041062841c0c00303160101c007004040ca18144000c0250f00100c2c0e40b0640105620b0386011000550180701400089520304101071100703041030344c0b03800d40150140411008030310612042044211200c0215900c4010343c0c2016008220b004c08103418078000f8030080c0d0403040c28141e5801b000400c2d803110110850105480d501 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 558067419 1250 558066169 558066193
    0x1902070b04061b020f0d11030d091d15060a02031c021c0e030904061e171005060619080a050a0908090111070e070e03070803130b0a050d0f02040503 65
    0x540140e0082d4000103102c1500c800c02c1030181c420a81896000400140300c2040820002c0d4162840400482c6e40c410285e002c0c054a084c00c12900f0150000d038207251600d00c1c1004211500c0b00c0e0b540035024004500708011440510303594011405030301c0050a80c642e100203080d030280d41c035400030041c3e100d122014010903107148120f109071840f002400d00441030395103008900c00c000e015040c141000c540403c000b501c02c01d81e140d1103440020070f4000c0040300e482e118030003a0f001c0720035154004020345850050b103241600c00420460a01514071800040540b43c0c000410f1440c040c0200c40c103003426401076008a02e980115032180306808541c4103111668441447d1401d503110380d200140255030510490b10998000c3c0b401180001c1884100c807580d030b948901c0f21106002c16500c44011941d070b0710b000346403403c0038080c507000307008050019032601060401303e484907000352094031040030020900d9030260b48104200c0d1b0000c1d926240601140f0004409580254818030819201e0b00c07a40f0000304c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 558068669 1250 558067419 558067439
    0x1a16080105040c140c120711040c020105042a03060507080f0108070b072306152d0d02060d060b090f040b01020d121805010c02010507110a0303020f040902190207 71
    0x404500c2c540d2101d03203400b0002070312444c1d40c201401c030550a006944210001c00f46840c0641a15809132070241c0100b640300b014807040b03d03041104041164100020030022130510002d040b00c04030349600c0b000b000c030044081d909440a05400040186060074141300210b6400408680200340e15800584143da0382c3c0c000543c4c468407845800d441030300a00030000403034120309100c0100c81588403414201c2c40314100b6541041d10031a1003074218400c00005442500f041880d021070110140b950b070f200e40d004690f0303010061202c02d80d258400da40c1c141c4024215200e40040e01c2524004800c01e02015850700e2140300c1d6030300700000003401020309841405051509004030750030a04103030050403410311071441c100c58014518034686000b40d00c030304064141050303030419154028090400082c5000c40c41c50000d0035240090075520420194070f4040340c007002d02044000c2090f902d4140141c0d07882940848040764015a40300300e03003180c8003250801d40b800d4061904140600d070350382900c4220342c0302c1e40024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 558069919 1250 558068669 558068681
    0x100501030e03040609060e1f020109050615030304051e0d05010615080412030e120c030310080c011706040b09040803040c0801020f04091a040207080711010503061503041a1608010504 80
    0x25001404008080218601403030704407d9500029000205404018800c80b003408492a01440180e6442c8c4c0352a043c414203000c0b1f541c12071140080d101d1404442400280d89010360301a6034070070050342d24100d0183e82da0a46010101d20081c2c0254215809814464001c141c280b050703c075000c403114403e9003000c0c41040c60b9031080e58810311400c0b0342034070074804500812604c89140040e1241d0b001d861419000700c3e002e402c1418807140159030b42d10b000c00780503561803074580c010107860b84603c449010030ba8103d4480c091510343c0c5141981c003617541b100028050480c10034450303000f17450802440140308c014001036200324054036455100580d00c20415080f486a81910b04403c50140000c0c014080c1a40200d640291082000820b2844810001741240e000c40001c035403d0b1800504103040011842210000030001d003803440c01e610300070740450b031412542160401e44d040000009410031a145607441985680d40c46c003400c1c246498501c000440d049481c20801241d100800001d1510340742c0924 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 558071169 1250 558069919 558069929
    0x3020c01020729011d040f02150d06060e0303090607032105040c0302090f060a050d02040e061303090803120a021b0d02161205070501031104080d020705011b0b060f0315100501030e0304 81
    0x16485ca0759035444043c54280d0b0f0300e8040b6841031091203040441c0c80c02d200039100b0310b1405500016007600e0b0180c05003c0038200d040e07107070007a04103100703c0800e9906e40c070540744d80d00d0301418500406581b118800441081240c0b80421b41c500c1c3c0420320045c002c45036100c0041e00c1c826644800151036221108028100440b01030380d101c00030000a008a0600c00408070f8450f2010300003003142c0c160102c0090416404484410701d107000000c1e040309165200d50354200900982c405146000700040485403010b03402840096031079000280080d000e03428501281600c0500c0e000d030b811982c3e000308025105e1400440e4000c45210b002d20108880b200341c8880034150b90710100602f02240b0740380040d4040c105515492082040500000441c240144090034524010b0340c0544180f508040000d880c580000d0074102c6040e8a5480705000a100e42e242181c00c2101100d894400003483c0001078174001c40401c00b200a50400401e100010000c221400141c43c402d882c148610000058081d40d0f0780110722a07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 558072419 1250 558071169 558071219
    0xb100305060a0b0f09270106051e0f0c0105160315050d0f0203070510020307030306060e010203090409110d0303020d1a1507020f0604080f0d03061503020c0102072901 73
    0x401141103034400800e90f004c500c80005081451760b00000e080d69500d9685003503501d60000381e403041e02942e8030406014003043e007031a904200c640303988030301e902e80c3d4400c403400d400340001125003150040205840103094104001d0105282a103860ba107040b17003220080001c40d003071480005003e0101d8030301d10705031000600f8011015640c3d46940340c08207855102603805020325000030895499100ca590007217200c0da0000c50ba030700743c141307001070844030707694404000c10410b4014106540e80c080304958020400301d401141c0c092041c10101000c1c1e0008548981c4020026003400816030181c01a208a0039080030412aa115140c03000c040034400d18051a80003000c034094101c141c11002c00313061f203c1c3c0042c1c4003c46508210340802c1f819402600b154410382d0125180041e000c0b410031010000040718503090241c18a0b1601d800b003140706895120702450380102e468134410000b5815144c08507040100046c9250794010041c4164020383c861841c640740d40d200100301d80d07048400c41d401c0b1012480d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 558073669 1250 558072419 558072439
    0x180b13020c0c01031e090302070e1501080c0c15240a14130207120305090d0e090a020c010e0a060605090f040f0f05190803090c0a0b0706050c0c01060602010b10030506 73
    0x40110024100d0b440043c10a42017600040c8099681d44131301002d0341d1203500286440343c02d0010143c032441004094245c0c0361811524407102d640d0103d42960403864005155461348841d100250515003200c01c000316401d6410200114500c0102c410032240c0c85c2c00148080209094040c044030400300e014040c041400d498481e001801e0440300c41110301c03090900182824400c2d81d89032809084584504006a01c0300c09001f40404288002914100d070b80c1401004558904003043d550100100040e44d40342e0301142000800354290410f011984920040c5d5a2205403850801d0060103980200d0f0301440c405400564001d00b4004014041c5421003800e141d808030f1036a0301120b18440ca102100c10b03014020703403500851007440306541804d2103a080a500d0307142c01d41346039151a41d010b0500d0310803421081c0421041c20b0102c101e50f0419000280441c0c03c0d0b0b1061b55909061150325640c8038158a0b241c000a80c1903819800b00401845c100c07032100340030401c0d5501320161001550803d41c0030728118 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 558074919 1250 558073669 558073693
    0x11b180f0e09070f0602010f0b030606030c010806130603210206010605090d03050415090e091516020a080c070906090b06160501060512010b09060d050304120309180b13020c 76
    0x11800c0d0b20803001030480380f210b52114445512000365900072405030391075042c200e50100b020f0250304005482900200310900e030a000117513035410a1340c03a007814040281c000c501c16032282c20303001c00710a104074010b011030703643c0340761180d592281034603005500c030032209400921a10104070310341211655030360a800c0948010030440c000c1141d070021002d0020401000400e1000c40180d41c1e80c036112520740a80e003500e0900981c9907000010101303109500600f000c1080f0b101043d18858110600204a440202904505031720748946a03102074215000800c205208000025026040d034803000c9045c0803507940c6040c00001c0d94446d041d4240d05c030b502401100c0a27202030082c24a841c2d4080c0001044031507984003c6101c00d00400300c8288140d4541c18000320500307095601a4002c074040d50a08034620f884d8540580701d020b14010000231103024042541418407038181d40307000d00005007542044003141c001c40c00c02825501d91680c0141c04c0080ca080d07082c001d80c401d80e0183e9400101410010b80c40e5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 558076169 1250 558074919 558074939
    0x1020a0e0f2409130c2f071a040b0301031b091407080a0f06260a1e06020f030a14153d02010b1309020d03050f0c011b180f 54
    0x40f00a401c45814003d031020b1925030700890245c04842e40300d404509000f4103c101280b68001400070707800321203002e00007000000003140b2040782c228110301510910012980281481181d0200030003090100000c800d2110103603d4245c000c107030941001d2101d0b903032518072050ba41da016042a0321001c00780001d24540c0210940c07a4040505900042c80320076005444040380c0103904030f014507400f1a01c0104402818001845108482a00401250b12542d8804240c01c2203003084200c1000c2404203901005001d40641c1c000081d5131480940324500340c062280200b00240e194004500c8040206518031804a124595400e020300094030075500b004501b5403808038400c406e80d42c5410101c9280014660f20100c51801c50a80c1c00803801040013130400031b5000001d0f5080c09818504141c0b180165a54076164003500e5041c100704c1c0d1140d00c2100c04842ca03010313894070010603500380000d14078244141380010b1502c4216442d04021070038924403004148a40b4080c0311030351512410140800614 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 558077419 1250 558076169 558076177
    0x130606020d0f111e0f030405060409110d0c051314030606010509180c1911030a081e09070306061a180a0f030303020408070b0901020616090801020a0e0f24 68
    0x10b2418090f90200c0e1103180b40d850120100e05684204502404280a07114240103408001510b800294101070a010000b000c80c4101e11030001e0191391008001000a48507098540400b480d41d404c010a2081c1c00000e003450b4004c401101180d86581e0380403d2040081100f00e000e6000540107142c40c0c0d565070019a21035001c40c2c0714a502c8031680b07200d07204810b403140c2528881c40c4a00000750700c0d400f0840032005192041041d102c240101c9107040c41800740004144c610071501e41c03400035040e840300c80e8104585420506150480b1084600b00540a1800039a41040381d00c01c141c1041b03200e9036aa0b0020800c1000002030140d000c0c108071084e1a940c1c40c0c0340b44503018a00404150321141c0d1070340354604a0010340c0c002c5011980100d001c004003902071054000230403a0030b40040ca031440c0c0400003502c541d00142124200602c1c80321540d0b10030300c208224005045e00d0402150394401d4901e0103012208031500b8540b003106200911000d5051504181c0d884030b0742290107400800119083d01d100e500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 558078669 1250 558077419 558077447
    0x5010b0307140d06081c210203100b030103060b090a110403061d030a0903030314010b0a030e1e161d0f09010e0303042907050405010e0d150b130606020d 67
    0x21003448400fa800e9070620410b4010110301004050649650240003c0820780c80b9034102030021400d60b201c501d2495980b0000b17072100e43d900060b5295940c9800b501426032607005880e4941d004000402013007042d900003180e84030216003c00c0c1a594020900042d1008894a8100040b0911040001a01c00c0c1c01c0000f0b44203500101c161001016903050b450740d08803095400014084004c00c2084c5a00740c03140e00065404200008000c2d81403603910006c910908038002c0805590f030703091765040a4188603245540d400701c000001910000304d0501d65611b030550a80c0142c407015640041c0d0742100102001d8001664a20055242ea5000c511580d0002c010011080d80d520350f80c801c050a14180011446140300d1010105000c84900044108810700070f035202c824000703101488030b40c903003010a44040312001d2824000800d03a480105440b000d80440051000903c503143e9801c1c075005400c0008420001e940b0070280c00201e02c00c003c142e07541441214090303003242007000c10382407185100752070f01c83d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 558079919 1250 558078669 558078707
    0xb03090715053c1803100b090c0f090f0f030f01020a0f030504110603090a060612030906050711090606090a0e0a050709060f120905060901090b09010b090609090708031b010f05010b0307 81
    0x20486004a804d020040c0228106c855594a4459141c604410001e400c030405041003810520808081c9600784141c004062080c0c100c08040318007580c82800c01c002e9940042d098500075110003190074007030b400c864061000700340325110341412a4807a1043d280301d02e810898134900c590124040c82890703440039000358a00d01510780d040c4003003000d5010701d00003000a200d2018402034281001000c050b8aa001501002001c00510021034203002ca04410101c00705c480601c030741c5a183c001b0310a84102135002c0d401031f4130b08000040c60780d080141c442c4203c500c0d100c00d022550394120f0403500031001340200030200e042d202120014500c10045000d243c007588500141d00406603c03034030319040040b5411206a034480312120304000250140942103610322000f401110f900200180299038002c0c240b40c0035007101000500e141a04000b414018401402078a90b1102d20318011810044602c402418a41c20010541c0c0200954801d49040f0340b00c1c03108003400d40c1c886240803106511464151000c070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 558081169 1250 558079919 558079957
    0x901030f0c081b150f030402040509100906021e03070203070602090a03060905060603011514040e1e070806100311010305090a021905040506060c06010b03090715053c 73
    0x403804000032495002c110407001d1442030903000304407813500004801070100b01c042c0310b080c45001e00342c42a00c2c0c1290f0f0443c0e02040c0c1c1d590340f004031442c0c000d10788890403250703043c40f640d00e050014a600514030703c0e810180c007001d90300d100c0354a655148800d03140b01f0016441040580e0105141c1d0340502490310004280725809552070700d4045c26101c00721404e5034590001c03401c3c85010314091040070240c0c261075580c840130924219042c030129080180c2240201c1d101c40399103007060810f10481d000c01e00c00042010391908000320141d42c6004600402e00d480c80f40001003109410000006011207500001c0895100ca90500450141c5000382102c55984518400300b230041e030b01c03107800c1070009070b010b00d200c01801e26100c208000e0799405042140242001c122022444c0c101141a90560b8001030300c0503500d40364810514a4035145600842210b1411520451030503803202c0206440100c0d0500913449910034070144a180a107112403100d00d50008000c10703a8440701d403010f030110745440c84582c00c0c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 558082419 1250 558081169 558081179
    0x40308091903030204080c030708031e0f0414090f0c070f021c030206062d062209020304060e010203070c030f02010e060f04050f031204110f030d030f05060f0901030f0c 74
    0x49594001c01100843d8000c41c0c10302290f1020031150300150411801800290316104803180c8a1007081f0f00b0080080014101c0350311803c1c054200c038080c0d88010100b41e62195240310700400400c4400d1007074810841d140100d040013401d00c8a25000707241d50540a46403254541d1041c820700c0c00700030101d8105440004042c03d0541040005082600a80240ca040e141800801c00407451010600c6200000a0310400240701c200031054001902035912969424161108591503003900c0d0600505840070a00403c01e2541500514001c9200360420b11a01c0041044282030780422201b1800003a03400d01d4120100388107502c10102d0030907a000015564215002003801c00030112a001a5402d2170428001080000c004401303507418500e023303504001c1581c0f546900f001d0b001d003018101054a04404c00942d640001d119030508000301103a594001412002d030189c2680c800300b04109251000041807070408441500d01100003e000300d6050f030075130b550301907104c0c00c1c98000d031000d6600c0c1c400455 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 558083669 1250 558082419 558082453
    0x2f07030e09040302010609200f09210115060327021903031e0903120c030509040e060708010b0a12020f04170a0c082802040f020a201504030809 63
    0x7008030701a41c00494181d050011f800203079191254a0303039291286440e2805030b84155030545d907070407500d030441c41d40c1c80021600084000310350844100395803528510304a00c4c4d28056000c8440c4520081c0c4500610381d550109504441d840c00b04c081c2c2c05910040520180c2d54404021440c4610081ca003008000c51445503040d081e20741d800c210086034403240d10081d01d40e0744e850304403c50211441d02c0c4916504541d0f4595148580403844802d01841c0c07440d0380b00701805032080c0c400c0300c48054000c20800c944d044080b1b80e90071040d282d00002c43c0c8200000300d41e00d0100000c41e00607000315150b00708012005102d402c0254019034240f00300803c00c1c031000c9181c01c1801000300480509500902c7c42c1e11150402c0c003158041a440200594440c080c0003001029002080300649003e9402c8181902c05001080160591a01030015248002201e109043c1c00a400301c102904006004000c100031002c81540c401c040707800f151218070751200180010b4401e015043d0312035200c6040c1c8007209140700301c80d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 558084919 1250 558083669 558083671
    0x60301060f08040512030a062d031202071a0418380a03050d02060708072114010b04062a11031204030807110904020d06020d060f1205012f07030e09 65
    0x42c0006442d1202040003004a80d100c4044034040750820011109027052040260004d101c000c120412105061140d00d0081c483d140041560b290711481d4808084417915580c0d21a018003d40b0030031006a07504174070035a00c05c038141c0b4003c5886813a504003200c850300118500b055940000e07600610020b28698a440c02035000440c4607000030600e0904401c0080d0400030004e11030803c000002c000c2040c9c6942c0030504903401003d208940000c01c0c016400c80b0060031845403003030690368031038000103018420380c002082282c18030780d208001c0a030186030141c240c0d0303801030411550541411000c1c002c500115030240d100070b8020216210402e1141c007502c2070350413590080c0c895003c045000d400380412041c2004009804075944840b91030f2540c0018003001c0c04502c0500480d1303011800d8822046264813600240026406d24008195a00e8a28440d1841048206c50035403c1c00180148a102070514003c0c55800ea03079102080342c0340d9629401c075034101070b10540400c120710491030b48a480c4c1c1c3c0c51079 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 558086169 1250 558084919 558084931
    0x70c090f020903100207290f0c07080a0f0e120318040617010609110306010f0f0e0d32060a1a0406090207050601080304050102120c1203070c11060301060f0804051203 73
    0x5a00c406190500c84c5609444845030030348560440e400030147c079400904141d0083e045403103000f003622111400c140500030450010300003100010b1605165400c01344110b00808541e442c0016020302405021419400180340c41c402e610500c5101c0e2400307041d01015440b02c8001d840001c0e01980c600040f043d0010b4031241a4641c4d649000c1400b00d02964045c03070309120001031a6510f1800c1050009280200d1116030108104602e4000d0460a104145020403404001e0068950200d58145a442d4094491110811441005446d0040964040304154030400312003e00941e603a88202840a00140f10440c05202030350408200c4a41d141c0c455080a000c0c000401a180c4889240480c90b040040c0c0081d00e00c2c1c0d105102c104544daa00013141044061821004d41e190980d1440d02494941b106482d07000b05800030042280c5503610005407a40140144841c090210031442071000d60701c401c0c0515800110054000d000e002e0144014a411621403811109800c3c41d141261956400903100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 558087419 1250 558086169 558086171
    0x61006030e0a020d020d061509150605030c091201050a0c122007050a05060c0705100506060f0904060b030112030f0e010e0d1a0103080405040b1e150f070b04020114070c090f02090310 80
    0x85c027031f50b2013a00c6005d20240d074000038155401d060240140560000408151401d00005180700c1d45840e00a101c003030100160000b8411070501d003030345501a00810076a4400284d4520609801c3c02660207641184411080030211407905181901150340c01490240c4e02c511400b04064000b407010402203101d00c0007014156101c2d90340c1d180050030180c03003041c540c1c80e450505043c0241d65607450102c40d0010092082d51f80c2e502e01a03400b00d0302600789680620300008022000081c2c106d4088101e80c01c1c80d1003940c5503480928072040a4820303141d1444107070300103400c0158403021390803d950200a90f44c000e503035945081c020701000c0400c01c00260021a001100440c04004608150040c0950030741e08881c3c1d685151030410102c0b4480098221152050450301203007107030a00c1c2c03a0304440441804aa030190b40d00d0309400c1120011000b0789040b800514040f01100d80e0031880d1060361649030380959040c00b13280c9405400e0029000d02c614001945600300283c19a5075402c10044c4480851214 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 558088669 1250 558087419 558087461
    0x31b04060206070e1e040b0409080c1b030a030905040c0c0501090c0303030c02011416093b0f0402120c0a1e0512030a03020f1605061006030e0a020d020d06 68
    0x2000a11403004c01c1121801030b0b20f25118415281d801207080712450401761400240c80721010005409000f559801622080e0001006403d181020444c220038903a01498140c01507805404e060761802154130180010720180350074440f52170140c20400c5400c00c1c1d071038070054100c0b40351a801d086401d0308100711200c2d0b8034280c1c102304041d054003900d2103020440c0001c006080240d1000741c0c2d4041c0c0280360100522013511460741d03c0c1d00400320384010b1328500b01d182d06003001d600a0209000c240b041c007070090001c0d0300f51911090a40c41d404030310802815003044040e0711241d0034499003168020500a0a00620350b418072180c40f0540160f008000300403d94400100b80c00c655003421401c0e402c00d60240e8008242d18070914400000c8035178100d0240703401695140c100c00040564041c0000d03103803d000c0303802407280c00d20000207242400f07181e00600e1042c039180e40301e00c19812a030700707c0c2c08030301e19400151509000d40740c00081081000d0010302042c22820054ac0c541e4201c800b544110250102544 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 558089919 1250 558088669 558088681
    0x120601140301080a14030c0d1b050d0819020a0c2003030d09020906040e1903020c060714010506010234030203101506020d080a051909030e1302130308031b04060206 72
    0x801813400100304c0c010f9807409200c515000d82340c00f02402c4010510400c4882c21400c8071040903d5030010350014242c1309110200c80000b002114195011a484107140c1590302d81c4000c18802c0740e20041440d141c82c0c0710010240e50350506200b83c00541d4103041409010030704c181c4c60174402801110014200011044243d1040001350200a040240294503002c00f520b16103400080301e0455000340194140c1400320717413404a25105090580300d03000749002c1480f504100010354840e6812030388400038441e650301d4000480c0e550030011001c046164100452052404a000003503103000088807031410b64a449401180ca45110071a295007100e64824807030708510002e500e090042c00d15032019005d0380c071600070020880c01002d0700c03881d800c41e601c001098020b02402d081d1000c40400d50018002d00b101414003805054024440c54003c100c004c0403080100803078400c030b581c40640c84448803085411134480305031503040202500c2d40d0040c00c0103046048074000d4040d10040116600800e02458a8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 558091169 1250 558089919 558089933
    0xc010606030b012606010e0307170c0907030b0109050f0f030304176007090603060605070821191406030c040903121109030c0a0b120601140301080a 65
    0x285402c54410110710241054941300c46645034000200b4a4060260001d0000007802c12180d0784c4000c0143c6c0c1c465803d45800c00d004225901e204c00c8c200c0e040c0d074056480510a1301600c01c800d0905000510180c1c040c0f0051070018803005000d40c0182081e40c4103010880030034590761054000e808041e03014068400203141c2040036400c0100c6c10343c01c058890f0b0040303594003108102c500c060354583d19041c640c00d412070310545c2c96480341c00c07079201d41c10140022865074421001c1c0030b540480c0010f0040c440441d00c10700034000d290440b01c0c5a9141d62030000a41c0703441c4803540040b1506901d91440300d41c0000d0343c0308241e14076070046883c1e00522491100c80c03c020701c00c60f40e901c00a4181c0e8501101009004e6901260040c4141002c0d1804182c022241c40d0407a66522648281c503011403800c140c069a141021028006410b01030f000c070f440080c041801c001d034031049481801c03040c00f8100003800350f00440243c5550041c0c410f0402020041050482c50304030740090304048407692000b4071250620401c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 558092419 1250 558091169 558091187
    0x1b0e06040e210304061b0c03030b010f090b0c1903110c030a0c090209130c030c09080a0f030f0c06060b0a020625110a0807050601080f010e031206060c010606030b01 72
    0x10700c028510004a4a11140034901081881da062a4080009010301c182c0b50040940c943d44085942410420714170003410150250720150000307480c01c1101d8800b540500e428080c84200c6840301c1066504e08800408164484580b5101d5405400816040c42e40c442e00700103001403203070312a060351804142d240d624004407140c1c0c940c400e40c40075881001081c1c55400c0302c4140c0c0d500c824050780d2030401c5804035110003290103100c1041c901c0d02c400d8180c180c0c0d00d80c0c0017461440b890340d101000c0c03507581c01c0100d50b200c00c4220080c00c4079001510300d10001b1b000c0d03070441e40004040c2c1001c1c403481c1025141c01c03080300e5113a0f0101000400025121a50303660501c0074544c0268410002d03000c64a01c0380c5901900038501d40201d090005840314540d0000c010041040710590190306940e0740c6a1a140c2241ca030a02031203804400d101d000b51442034000d042c040c10202d0320f0510015414914500c0117083e25040c06400e194114008001110751a0303403e0147d4005040952008103400a140c0001040e07004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 558093525 1106 558092419 558092441
    0xc0204181506090c170a020912030f030703060e07020a060c170c07050f0f0c041808030403030b15040b2a07081f05130f1b0e0604 57
    0x1107400a0095961007030f03013440b55801c0d400c0c0c190340224001d0900c29070380340014005188180385c1d0340644000ca000802c0c0030999070750324800904680c0030412100d04004000104500141c00d4042d01c001000c028440c03641ca460400b8009440c0c5480140052049441d1011070224030300c52039002c030044440b00ca0000c194240252840402e600c1001c0c119524020904078a9031503a002c5000310030030424074040c00c6441001010480141450b8401c004401106074032440030441c0c46018500c01c501c03035100000c01801090030880c45030007035400d231000c0280801040c4044490141035840c1c00391480b500f40040d1003200060418041481c01ea2a03240c46085000104024001140700b4280c0c450201c1401c15000c00b8130a406903041107a080c07141c1c44100c01c4402c0061715803e4107001b001d004002a080f445403062515080388084d900c0600c1c2010080e060003910b103050b02c01e26030010 = true := by decide +kernel

theorem cover : BRFrame.Cov 557913669 558093525 := by
  have h0 := BRFrame.cov_init 557913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 557913669 ≤ n) (h2 : n < 558093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
