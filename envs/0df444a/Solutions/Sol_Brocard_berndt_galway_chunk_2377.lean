-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2377
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:32:02.008994+00:00
-- url     : https://prove2.me/submissions/fcebba51-7952-4e99-bf29-1b1ae1c8b766

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 427338129 ≤ n < 427517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 427339379 1250 427338129 427338133
    0x10e040f0c06050c060a051b0304020a0b1b07080c0603010905090c1203090a0f03080304081c020d0c0e1e040e070b0a03020c0d0203090a06080601110f0c04140c030103060e 75
    0x19001803162245507015080984505845000220500780b07050b100400d41044249010140441c91246d080a00340d0a003030314010039525a41c6101080303054029a201c6014000e000c540c0d4010b1001c0a03440c50040f622040449070300980d560f02e016038600c0010b0109070810002c00042c0101c410a400466002a80d081114640317140300011810b83e5486181d03008036504081a9604d0a183c000c01660090414000780e5071590300355102c000c0340e440007500c014001c601c000b0303850f010200b4107441c50f02081010841152156901441603025100c0c8445880020b03108420701e0b95140350100d0b5a2909901d0255442042050070041c00010113116400d000c0c2e0340318101e0000713406441000201030419090380c0151310791256804181c41c000c0d424180c0000c0d1340041c48241016281d0756420401c40e200c41c900b181164846c0d200503540710303036000c0d0513240c0307130107080c414255104001408242ca040240c404115001c0c074510054a803090544102c0d8884c001000100007142030b5401980f40d034041c1c101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 427340629 1250 427339379 427339403
    0xa050306030109020d030203090118030c1203020703050708070528090f02134223030a0603031107050334030b0f1602030a03090309080304030515090d0206010e04 71
    0x745d0345040d1038000b100180e10001e204104c0c1d59004408100c0d8441040d403042d1103c0c1940e5880701151501d000306c54450240000c0c080c141442000800e0081d0380000c2940c00c0291140d101d82e171900203501801d806504914455542c0c41c408154054500601000800314581041d03a241d010f4140c140c889034045400344220070607503044040c840d0040c6544525070356003400700c40450241050211565000655541c0031a400c4194101c94401c0000d0034504a69510790505041e108501c40e80a11480400044104034006030141d0105081d02c1c020303100c0882c080c200030b0340c03a643d60005009442e01508115006c1c0f5543d01c040103201213000d100c0c07404200c4401540b045a5003480c00b41e105941200c0e4000902c02440c007101881360704440d214110b4010b05021180c040d60701d114503040350040554600d0b08500f414822080000540300c144140d940d215030f6420010356032030305000a001e06096000c080342c1031040005807540e00081540107468540c0c40c18018954151008000365640741d0303001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 427341879 1250 427340629 427340633
    0x150806030d230a0504170118030813080d0218030601080a0f0503090306040f0b01080111070b0a09080d29032a0a0909060c0903110f030f0a350a050306030109 69
    0x103000d4081c0418540c1c0d1343d52120700c2d107900043e41c000741d14a5001164500385807100440d00d04040c151000da0541403c10301600c0b811805000070f802c0200240a01c1804070340d10845e00e010307400800056519158a20000b0301460030151a05400e101e010a240d1111050000044510420300c1c0c445004000f92810310000001190800004481c100c0307894039884880c00c10000e03104a480c0c00b50891800030000c0840289107401d20340b1580c030025040083c40070000c1d0f04002c1c10b810040c1c00c954401c0c0040c0d02c0d0b059840e40240504034600c0c80c0000d000c900c11410310528650701d5000e400c1d15008005090605691020044203003c0c2c8007900c0340300064601d1b44000751202240f1070010070b40684009083e03456818000220360001243c0c804100ca04282000407503c540c3d181d0162070401c07140da0144007100f500192412034602d2441d00c0301c0c040d440030601840401a07028903080c551748080c5100300c2d1845030302d80004d8215901c4020100091182c45002481207003e154025005070000480d40e80303076 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 427343129 1250 427341879 427341947
    0xb0f0409420b130506061630080903040b04050d05010906140a2003060907090b070503130509090718090b01030503090301050105060304080d2315040606090e19021201060801150806030d 81
    0x45c0107600d030152340102c0c0c0f50441d80c2c00f40500364401c10ac80091410b007401d0000d40c40440c42a8071685215050000100050080c02c0d0300402c3c8696100300c04000504060820b00c0012004407680d2800701d15200468180c1000e115170103c410881c2140345140daa5a041001260720001e0b001c01c003000381903000820500580d0740141007080c0907400445c0c5074690000840c4030700085030411401a40c09406004910f500011200e0603540817840c0003052040b04008030000740b206c8000a042c4180000c000002d00202000900003058154000d115a07070326101807101d10f20013510010810f40040040c4405000590301c00c0003048141d407000e40c0804448065100d4840003555070308101d0344211a032591514052140d000108000c0c102034207030074641007001d010003400600c42e81c2c5512070140c1c1040111401c2d412601c103c818404580220350316000001c2c950034003401a501008098030051142c00d0086441030320695004008046440d00000100d41c5826400b4400000c0e03880d00042c11481e02003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 427344379 1250 427343129 427343183
    0x12140303040b060310060315110f072a0e0c0a0509041407030e1606030b0a0b0c0303010806011202090103230d030b0f0409420b1305060616 61
    0x401c995200b9040c00400c0505001603d100000c001e881d1035400c200290603039081d030542403a40c160005000c911441440054816045000d40348480025040700b0050400000b21403a42d41e01f1868005443c40d00a20b611079101d03009015540c00f40d0000203060712001801441000c1e810300c1c0c003d081c5001100480d041d2028210903600c0e01c0041030801840903032610a0030002c5503514010094101110204403403425207015503020181c554030303200a60b0b2184001c07640100f001d42c24090b40c41e040d914035287c0300c0c2c00c2801008114002c1c400000350180d802950115080d800404001c00c076440e40da03406030600d00080600142c8003404246919069040c0030a464a0080f500c0100e698140d020812040c0600800f0b400d100d1840e141748400880d2402d90800f0141556035000c41c1c07800b001c160328090034405607000f1404c061030310340940181c03482a000810304c0001a40c14441c4a2512003502c01994000c41e2000d81107141400a1616080d4601c044507506019030307050412242c65000110303503286 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 427345629 1250 427344379 427344383
    0x703031103010b07060b1822120507051002090619022d010c110618030c03030106030f0c050702010804030806040b36011203081008030c070303020c0f0a1214030304 72
    0x4404111401405901e029044d00124100c8680d2542c13a00d01c1e5140083c10000350100350344102181048c0c0301445008140c4800e10b8010104100b01101c1c0c03c001803903580500c03c200c0702c902801c88000400e044600980b0304604008080504040f241d034081c4800968900c199411441110501000f826a00c1c2501c84407482d010407440289021405140c01c0d120f0004207030080214600140d40a100080752440d0450752800c401c0100e1403105800604d14020301c00c5010507804008000508150076a00401d2103050440051041c43c00c101d1b416900c0f4080c1d040c010b03021075000000a40040e200707026190307011000500000d10511590302141d008450201c034146a1020b80c0b00c45944c074403201e40c4009010b44041c089107100c3d070600c016040050f90b5104001d05201145011850303508800300c140000d02840000c41c3e40f40c441c444029680c8445500c41a00903004440a400182c100310005e000385141c09042069480c2c0340c103548800c880313011041526202c15030140900c410310300380000e500a81c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 427346879 1250 427345629 427345649
    0x306040c120e0c03011b0c0f0623270307150612080903061f150507020603070c1103012d180305040e010902180105030405010605030601080d0908061b070303110301 72
    0x101d079030381c107050850b04c4403106d03988034a28081030048a507910000712401c0c0c3d40c1c004541c2400000714540710028220203400c0413102080d0311201e01d5914841c81109110b07409091140c0d01607401d4100d00e034a01400c0c0c2038400c50a4000704404000300341c3c001e9111303580d00c4941c28002050356032078407901e5062a94107821156032000140012141c9000c0000c2604190b01c80540c040300c0d548140340c0f0076000a0391140f00308010581c6010207040380a82c00342c880b83d50700604a0303607a9284c8948001e201c86104c0008841c100e5001140307074220b0505101da00800305002d056003201c1c180f16141000701c0040410b01000494559000c903050b085e07000001d404403403280c2c03111910780703007080030403500060141c02c070303e102c1e901c10f02c2102407040040ca00c0100321b42003070804503070306d0700d41d4200f142c05040103800507034052207401d0000032803410000301c0e1004416240c0c0d600b81d42684882c0c0c0e403610b82c1e2040c0d9004103400c9400390300ca590f442caa04014a251446401d00203402202c2c4104003d1b250026071000c0400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 427348129 1250 427346879 427346893
    0x405071707080c0604260307020a0b0405091b0d110403050708010b09090a0804050f010e030d080604111809062101090204060b0a080708060d050a080306031903050306040c120e 77
    0x282c0c810040e424109000302d81e00742c2003d00b0040c40078a511200c40035480035214013450442072020a00480f0040c60b0060400042e00e9200d00c4030f9a01c5d540301c0c0c8100c50007807012b0030010b1101c200601b1410b440d428a410010310f050703803003502da40107484648090390702090704000000014204001c0180208002c20020482d07009a2040220480d0000d03c111100e4011500110000e00d1500c1110140c450403100b904025007240c0c01241d80081680c816078044c892680750850880e00050520b02c00d1008907401d100030010840c0c100c0c401d01490311003607110a0308034660442d80c9415424181c0c030220180980452070480303e20440c910801145048041c0d6640b061942941014000c110141403401501d0340380c80302d03100004001d02c800809a408011005c80400e1040d40c4094440300840d4000c41150320b40710690030072404a0340150b40c0355110f4491000f8554290451621100f40650542c80705401c2d82c1d581010b0102404203000201e0810030003d4400a008150b48a44c28424680100078a19 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 427349379 1250 427348129 427348139
    0x7240222090b01091a0f0712020a05010c03060b0412030c0209131e110405060a0b0403240606020601090c0207030b150306071d01030225200d0201170405071707 70
    0x1c0b80ea0042103607040141d20b1074180103640000c40c0560b40440c1c0a00c1c0d0300c4e81c4050242c1030803801c0c000c0d0f51b402019003000c84004644154000341c03400106020b50000c121200120006408440441c801c0802c0c40d1000d1100300885901241c285245500900300381500d04502d50005145441c22103170030140301c0e40c00b1900c0007841404100c100c00300c2d007820581d1021032169103402c00b0100034480740b14410380d05e610000f20380342c0328480f072800200b030042502500d4544a16002c00e219000404080c034009185065008120041c001c9904a80440c0c019002d145d08000c0c544000d4070752005c81500707600c505000040043d0780c001c0141d101300c04420362010440007100806042c0240a061030041000140e594122640c41045040300e22009082c0166960b550442c41c066140d00790104403078400041c5010414480d00780700034076900180c5c2241034207605040b82008002e2081c520040e00080302c460107200c0c04500ca05d260383c2c0181c091401c07940203640e684032405460140413900c034040c5d00207200402c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 427350629 1250 427349379 427349381
    0x40b04030e030d050403020409020a0b0408030903100b0904170f03010e1e09191b08010b030f070e0114041e0c0e030c0310020a1407030c02090603030724022209 70
    0x281c40c401200500080743c2221401001c3e405139000c0a44100e54445c01c040031981c40100c0880108460448141c40325950b070711454aa800c00c0444900074001c881c0900f020701102d10810b900000300411145031503d40e038494000303280c011000074072403400802c1260303804a0b401e40a0350007001c004040c0c81403443c0030030800c641d45840c43c040142d03803410801800031346007011454190000381c0c50243c0000034020f0800d0008940403000c213070828141c0d007a010505500642000e10f00e4071f010b03030031144c1444189901b20340d106182d11401e040303035402c440144403c42a9034003401c1103020003000800c85501001810301a00440c2d00c00c1d0200c50f035034040714098550805c4115224178802c0b0054002000103d0109440741c44100c80b10900b00c0d40020000c0d0300c14012441580c0c11004a42295100c1c0d050385070281c2400d018850592140c109803002540318603000084420a0744d1011003400c00c0114800b002040f8240700160882680e0280000d18040041012664202d2507410040c01c000d490140c081d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 427351879 1250 427350629 427350647
    0x27070224010f0e040c0b1c05090d08090a030801050d020f060309070315020a1202030408130b040305060c0406051b070519140109030302030f03100509040803090d030b0117061503040b0403 82
    0x16243d110030030400021590036603d442c01c90340b1182e029556524140079503c14002000c0b05600524a81024010303850320001c1c1144001c0110346030b1800c1c5031a090070391039480764041f8000340001e0741d03c1d0061100d0b090075808417551a202600344a0040102d40000320290000c40d4006266840301c00200305025941c42010001d0445032803c51800c00620001801221100102c200380b40e00000441d08015181e01240c0001200c2c0e203401200c81d03120040b803043c030361182c0b2064440d0b02c2100302044c03990f084841158104d5031962180ba00c0c14805a00d80b21198002545064050050f0100000c0715100e686188040e01d904410350074103181840c50301c082c012002d88181e41086000e92081c000079800104031080c4845030168903440e66281c0c03100d04240c00030b40d00195040741414051208116100c0c010354020700802040d1910400c4903e07040301200c6141041d64001790a00020b650027583e00144242c2059003e0400d80e801d07251032030080881e900a81e4210f40c1510b90204002c14150b0203c016 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 427353129 1250 427351879 427351889
    0x603040b0a0f0b1c0c1707060e0f011b1b08030d1a01020a0201210c0509010305062b230718020909010b0c0f1005070201060527070224010f 61
    0x80050320b20308004603200c111030b003013a180c1c00080600020b0500c404541c1520040c001c05481a00303100800c4100340d16444c0500c1900d001c1200c0070349494180c5130010406002e60011394511103600405001c21802a800d054281c4840c98462075401d00c8441581141000d0711580c0021a551015120200d044800210140708040d50600d018000d681c3d0100c0c0c1070198680900e003003204c400b411904507030344113103541003220a207107003002d100c2d4050b4000c40503201110342601c04000380e9a901003808440c46440d030b1111486c0c00e001101006192038419000c14140c001c408004404a21502d01c13900740420002c1031000d40d020880801001d2480b00d00d0701c41041c0590400e50038400d500020528a16040c004c450081074013050342580003004011888125000304125501c44400c03160701e40051a041ea880c0c0015400c2020124040c14180203289580d88031440c040c03600c3d0380c1c0ca8034000008102400d82c404501038124450080190403401e2510196035869040f91540b40c9502d1000e5182903901c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 427354379 1250 427353129 427353131
    0xd060b0f010c211e2a0f080d0b0a0e0a05010611060402150f22060201090503120702070f0e071e0c0210120213051302070c170a020603040b0a0f 63
    0x5803000141c21a407066258a107640301950000d401110558906142104107150a280502800c41250380b1004041c01c5c0d03c0c10040605c600c043d07003101c1c481390031068140605005810201e00c1c0c000742c2408002d00200b0006840080c88044000c002007440400768403125a000c00b5401b408840300c1544162801480903080c00d040c02d10300b404019407118001400688251914045920034240080031a944040c00d110300d641d03640c0320900d4000e042c3e80d00f5568603146100591001c10070310b005201d808040b9400400a5051042d840390b00106254024984000c50141200000707a0765134050219001e040041d080d080d00d0700e00520002c0182c411116907108400d9103a00480700303180c2082d41c0c821996015110003201c5905002d0545400d003500012012039440099a0b0146201601504042c2d5004131a90481c1c1410f0300f8003101a8014050f0140104107040b0081160030900101030000b0070a00054034040c42c410340020f00c19030000c503401e664082d003420802c075540c3c0d103921440c403c2d0090804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 427355629 1250 427354379 427354397
    0x9060903070b071112030a021309050705042702040b070501050f01050f1003270b0603070e0c03100503011d060f04031d01020304120302030a0f090828020d060b0f01 72
    0x102d407031280502030301850901c600801c030380031444e07801c1c0010900748540170704256890809a2207813009510403a80d0107040d03820f4040c003240303c82c07250141a0003000e050783d40c0d5080c42e00703100d160182d40107400603000e100006001007913101c0d002030001d00000d081c421151502c61800e41040c0d42502c2c1d0040c00034080d003034044011720603961011b00d6110207420540b5401c900c61000030095008040d002c0ca00d221049000300708086480904000702505441141c2404854070303150241550f494032030103521010003005001520075140e1202541d40110308051003000c4a0380c48004c40c3c01c4039951118525060304501c18401300c0602004a5604210090400801031401f41c5009154030340580e0a1b082d489041d4200d110643e1080041c1c0d009440804102d00c2045000d140284d601e1303210820f2000826110700244840c80c0c06207441e034013201c0802c4080d154043c2c00e1513081c1d00e0050444c0ca03076400781149004cac00c000b40c0c039400c4410000da032060320006140ca2915017017100e00d00b0340d11001c90401842c62 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 427356879 1250 427355629 427355633
    0x30c0806060a090f0b0a080f07080601180e070902070b010f0e0601020a1b0b0c0a060e0601030c050409021512180109051e0c0d030f0e0a150c020105130306050906090307 74
    0x5600001241d108000c0020b00c003082d8800303078014050425821b58010300d01035020405e1003010a60403410340008080318101540c0700b28079921401c0920860710a0394150840c0140300802e500206142c41107242503810154988030300a080b42c102050a450903101c500c014000d00900b0000f0b00c002d001c4480044c0150302c0c1c60300000355112070001c0002c040c080341401d003c610000b004c440d04040d03d61018041c3e210324892000582d18110309406480503820100c000701c1d081da010540605803900809290780c0c0c0c81c2403c0512026015401041784c00c401144007800858407004003600c01c0105800c15840203040c0850741000408050801495a9160480c0800004c00015a0103210000f204084491031003024030203080075400314074183c010515034170000c00c16500c1240c0c400d0251440d142d102c8550070480038421134955602400b40c60314040e10075252400d0142c0f20010311140705241c16480c00b20210b880d1020038a00750700c01c130b4026868400f030000c801d01c00e102d029840241c01c8002c42c1082c41603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 427358129 1250 427356879 427356889
    0x19030f0f14010504061a030d031a18040c140a06050a05040b03070e0307080c0d0b060f04090c03060507141b0a020a082107050a12020f011404050c01110606040b0f031006030c080606 79
    0x106400c818954ae0701e074003803c4024214858032407404000c150342d203603107111446e904011500b2941201c820720a150089109545100281e10201000d0300b01406030381040300a075401d900c407503d070806201081c000091104001c0d0300551088510303a172075441400181c41494a4080361340c010603156040001c902c0c20f1134541480b0041d2480d0800000700440d251807001c00c0400803682c40060700203003401150820f11111480c0341003140d100c0d0302d04100c940e0341c0010403680c40c544500c038420050b43c00c11541c1c1c4000c1104510024161190058a01644031680098000c1c1070641c04080680c200840083d0481031840d0948130040e58210f12510f040000c0e516a134a6403841c1000070441300f0380f0b042d1032800324800c03c161410440004001c0000d81c4044020301c0c0090811101103505200303505002ca010751181204c2c1c0d03130803044e0310300401140e25410108406019072415003504811840b40312665135408002c0e42e21000c46521000078414190b00f00304081a01d150801d40f620742c0b2020a000c142d41300c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 427359379 1250 427358129 427358143
    0xa0815130209010c0f0b060a06020316020405073c020c13021309060306021206270603030702040f05070908070e0f13290619030f0f14010504061a03 65
    0x459030005a070340c1e42c9040140c40101d030030320000c3c0c40c1d0440d03140c2d440c0401c40e000e0100c501800b4111804c04840d40c1e51041207a90344582041c80504c1d4103801420401410f040d000030f40c000d18030381441030b0a80000701441380310f050303648581d0034203825006d003c401290000086a01200e014405080030b03101810118024481c0307400a101c00c2c0c1e40c00102d015111303105c0c60700344010306201c4106002031355890820340041e41180031f281e400008000040764803460003000e201d40070800003500c03240c14455400b82070011a001407080b0f825002c10419000160340724072030040520380152000600c2e0078190300003441d191580e04104d8155108050500000a0b14078680303500921101e04914507030f94240003841080d203814070042029203101d00c80ca100c180464201c0460801710012907280f80d1f1441d003000903610100340d03480442661001d040c4085841088000e15090140c0103940a00d00d0035903c014803140c5c0c00b80d508107982d55030024001080824000c2140345240403181c0c042d803000e07100010703491b012 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 427360629 1250 427359379 427359409
    0x18121805010503010b1806030403020a030e0402210c0408010c0801030605060621090a0204092603100306090602090619020d02120a030905210a0801090207080405010f020106050d080a0815 82
    0x5d4081842c2240e80410310a50000800241005440342420f15000e5580c080070700c0201c000c2121110090703c141014805c0d502201c14140f110a039403204015880101540905000040d140030480492800c40c2406904035070170325a907480c251036241d810060219200540303507a101d84820041d680004ea105009140050250440215540c440c03003142c916000481100030b422505140300441071004480901080440180c280d485451400901c0314251000704c8031011904030050040c008141e50750f03c4000594821840140b0341090300c0c001035640d803c282c1202000a01c400c481144039941408000d1716082d00b4001002c8100c007604040b211405882c248404065950b420740b018403c0030030a03060307960920380ca032550303600030403045216613072200ca2940042074070340c2c0c00044c4d400c06600c2290442a00b061515040508040045440100c0d00103001e00310741d00c40c500841d01d9640d4444680405124111044d9200c82c6202d0203018540c00a0240c0700310440c115250510361565111a0002c032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 427361879 1250 427360629 427360649
    0x8030f07021027170d050d0e0a06020301140a0b07050304050f4e0c01030b060d06080703020f010c022407050f0f1e031c1812180501050301 61
    0x10400b82412544145002000c1140d40400c0d1810090441042c500c9425030314070710a00c5003001c144441440e0f0340c42031500102c0001e4810094040f002c4030b1035000c038184180e400c0580c3d8071040c10380c4910081c0e07002030700b00d80d84c0200c2000700d123040c234540140c0500040450146240c1400020f031a00c1c3e4517401288a40ea010707200d0484004026540c5414512198174088070b0400d952854030800701002c000040301c070001d113080f54200d000d299003d00214085140f900e0061a061016800450107003045011454000170203000c400d645144502844010340b030940010209170385180100b10041800250301814030402c101c0020258440100040e00541140c8124070200491302114251748580c4502130004e0160300c071002e00340c00001c5200419400b45000300d52800c3c160007821824a014641090041d610401c0885d001e2a9500400844208903c00007d1011031841e84071054100c0c00c030301242c0c50380a01c1c03031065032075801800c40a84500b41b920004807544c10480042d001e0700c418002c00003c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 427363129 1250 427361879 427361899
    0xf190c0807081303061812050405130b04020418051b09060304020d0201110a0b04021201051603050604140106020a03080f1e04050c030d020a06140709090f0603082208030f0702 77
    0x1400120380044000d641c17081c0100714a2100c181e0382c400c2c1e11280c240440300740c4c0e1003c60301e000030340c8948142c40550300024002412422209943c0005041206d00d80e90029020b0100060082080d048a208003c261402080901e48140c0401e0f08030050391900b40b0b160002d000c00c3d0025140c0e5400da0740c3c456419144094110424001a10f24500414240703100748202c0244004102d00f90540c18004c0c1d01c2554004000c1e02c26952182c2601c104a400c10300a1100c1e02c03801031000e03c00d4001940180f4040c20002c0c18620b038201c00c40f40c44000b60000d002680c1714031044820107900ca100c0c0e99020f4403020201030306041200c0c103842020003000d140700742c034550700f030104041c0300c018485650041001001c640104050110294803650411000d9401d5840d11034070f1058140410440b0f4031854503503561003282d6080c07000c42401070940140b40298075036171701d001100080c100c5000340400b041100c000c01c640c00c0d029a00e02d0b0350503190341151403141c00500086c050206000c05450009604403411841 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 427364379 1250 427363129 427363147
    0x30e040603060513020103140705090d030c060212071d1f0e03010203040c05010f090501170c07170409230a090203030f0a0305250909050712020f190c080708 69
    0x2500303040d080070b00660300d0002405a98141c096401407524402e8a0622405901c420000d509210498000300465401c021740b0700b6030300d46111881680ea1007410400310300b410a032508800c91708081c5030300405100140a12038400d8003c0444e01d0340005103a20400c04041c8140415400200d0149034a00b103580b14201c40f040038055906c100c500744000e0021522841c090030484d180160900c12a03020940f50034040d18154402c0001c00d040e40ca040c0c4035480b101c454070f6081c180b20403000303001c0c18980c0b2083c041c0c8000a0700d00c160601c810104003e940d0344039410502104105c54114208840748400004101c18001c1252106030f4400c44800000844540900120382544101c020300340c6200e500085c0143c07141d800d40d200502403588607602250341142a00c01400ca58002180352011603040c010402c4500c1c266049107030b2154152405055461180c0c41d2030080e030b0042000181903007004076804150002c6041110524a45803a00c1090504030786c441031200c0c401c903200503100d550005100c040f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 427365629 1250 427364379 427364381
    0x1050d12031a0d0501060302040c110601050f1219050c040207051506030a0c0303030c030b0f010e120304170303010312020d2102071713060306080c0103020304060e06160807030c050403030e04 84
    0x4580c5001a01d4649103e0711864224024605400101d00c11460b0040e450040d40c85955108000c00003103008100b40c1e400c203820010a011261a001e5208105081024003c041401503600500ea500c0c4074100b88842c51500b1810101c0c8065128081e500c1800000c01060001420350161005a05080d9183e2120004641000c645450140049440520001c1056456440100303000856a0704120b40454941085040f502013903966000500070184184070b4608000c10743c1c0141c802800720b80c6030580d10801e4900b0211000200510350700040010003d100c1003010060004c8941d102400c50a1210b6030007418100800c50b801079040403180102086003800d81c119003009401002080c0074101d600c07401686903009040521003400c011000103076517401ba020300003d81d00848090040920a40d00441c000d400003882030760180d4032072813003203121001481070b28001c0150340a0598520040d100241240d8005030040040519020191030001c5d0300105a0f0141c990501d42100f441c451140010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 427366879 1250 427365629 427365671
    0x1306270c091a042c010609030b0a0b041e0606110d0f08090304030c090e15090304060c05330906010803040e040311070f0503070e01030c03060c051b010903030501050d1203 75
    0xc40d03c0c1300b0343d6800010f091603c4029245501c0440401c000da1b2209030071941000c051000800a0030350382c0100e0b24001c5240c10010300400040c00005664941010480101c184800e440c001c00e0355401d402d00059070300516100480c440320004145c04000d080005003042c1c111400442000404400b00d42014014000c5900035500800e80600558884507000000c10b54841040024816008144030300b0203441805449104954043c60409250174801c2d203a11005143c01c80e4075010341030b030142031620b00780302c98000480b841c290360418012914055100d000d01401d14545503203c1001002048400401c55090b82c4540950001d2074584d4a015101180c00c05028207890107401e134003243c0b4580040f40c0c10210f81c07040b0110380c6c496550310b241055200d0700b0700010780207200e188414000300c0c0c9141c010659140345880c01519042102d504011118511614059a81d44998000302490380c140501405420111409680500c2a0342d6910070541c580541e6400c1c983c50710302998a40855184c0b80c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 427368129 1250 427366879 427366889
    0x310020702190816080a0c0b03100503031c0e060f010306090c090c020f250b0703020c09010b0904060605030c030406050a0b030a1b080604051002091306270c091a04 72
    0x4140c07140c3c41d41020b6849146030f50000004400c0140001501c1d00700103002ca55044e080f420200425003040410046a88000d002144200e50408001100d8500b04024500e00340075400944040e181100301e24140e400c0080b0300301c03441c2d10080a00610144203d84141120b07800b48000800451914081c03212001c1c1ea403003003c0040c58144000780711078012030303848100c003040e0003545d10201d2880581d07286046a154400d0038100c0360807080c05824400f034000c0049a0080c0129400c81500c03000007940144e0036080300300142c00101c1c415001741451301030340c8041e11807410110f046240064a020303190000820241c035807501c4001007444400b075948191030005019090b50300d00c0225080402d4010030050070504a00c95900d40010300c41000310f00345c0d0091b0380c800e01500c1d10b2a501828840a900559520b0fa0301c40050351840807886a2441048d0003080d2811540c840380000c0d01c10007106003400021015000d00300b01c01810010f90210325982910345998508415454011400d00e940c0030750303000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 427369379 1250 427368129 427368169
    0xc090114071a0a0612080c160807090f18060b1809010e16030206030c0c0c06031003020310060b030c0d060803030405150127020307030f11180402090310020702 70
    0xc03400d0112440c80302d120341020652040540d10b80044407001c40e152072103072001c80080440300d0b00c0000c0f01d5600a141c2804020221802050300140c1800d01e91a60780c00035030540d000420820003c1818040d86103000c0b03d00c0c03410441c102c0651801c0000c40640c040040045540386503030b10f1241c0c3c482c400301801000500c0440c1482c504200b48500030b002d031f658900742d80e01c613803c0001c070f800150032051002c1d640d003d4101400e54030b8411003200c0d59000045441294018401c42d441e098441c040950b1150499280c4100c1c0c003440d40c0103050406041141040c0d25a040280912100444e0401c80b600041c0410a55a603142200034200c01400389401c01d40250200005000038042c0001c1d5141154080c181c43c1c03446642c3e2050108000c8500c0200400042ca00406101c0301ca01c0356409158082580e040101d0441175100034642101c03089981e0f0012110b02003207940ba9504500441021254151402c5281088140009980d904800409000180c00141100854a501c03040820711156461 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 427370629 1250 427369379 427369387
    0x4020a05070c060807170c22080a030216083705030301031b050108190c030605030607090603050903130e0402010306030803010b030121021c170a0909051e0c090114 72
    0x2d013200c100307a5140c0c000070414007911022507035503910a4020508181c640745070000c0b1440020421b00b0030f129200344203901000c00100f00b001405440350320361103030380540902107500341c1c12200210395030404602d65005004200e111003c0e1034401c41c0285500e0410b0110503000583c1c1d400000840100030030602000c4000010007000014445010040c9010401e09a85900044500500071220380c48103222515250180f90b8066000880c41001850013154103a16030700032a02d03117081030700c150001900c0c0c40401c11030325a142c0f2690740c00c10b854030040c1d0302c0c05041900c0aa4040101c2c020100ca40d200c02010904580c06688110020369002d490f0319142d6070360b4600c00c1140e030000d01c240851b0403021020000340030070b5419174201c810340c010030703500c89a1400d0a04074116110a601201c0360052005800c4009000401810f0711a0f055a83c0c10360841c1003111420036220007400403151388220300c0d913106400d500c061800390701070341c00d0740090744948100d00100c4201861414040507988002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 427371879 1250 427370629 427370639
    0x8100b040b07052b05070f080703080a0516020705061804050403050a030507030b09040602161403210105100f020c04061805061f050702060d06080c1003060e0604020a05070c 76
    0x8000381404a0140050340c1549a94992001415954182d980c40354281c813241c0704466805040039000c154043d061502050400daa2145003581c0f01080a0340418004010081800ba880c002c040c0d10a907091109414500c40410207995030030940a110301c24880440c0560520007816007107000070301c004009010324105420040d046070f0101c4094000a800c1c480060880e900a000350218083e0241c2980b84035551615110004e4000302090020b841491a241e4086000c5004d100c074400c021501840d515611203009600f058a034030360300c944040844004001c9952001a11603040e00c4508144000f9404030500f00d06121074981c1070f9510a19285000c61100c1c50f100405410351030f40d02d020401510b41d0020082c0c00110703504041c06c0c05418208045866210314081d0100600c0505103506210306c1050380130a035469904244206d40c40103400d040149020700700081141c800e418108201810406032088101c80108480d002d00d07000074150010500c03d01c00c803a1540d40118201081513221 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 427373129 1250 427371879 427371899
    0x3030914120a3501080f030a1b021206012c01050d0201030504030c1703011404290a030b04050c1c0b010e0c040b1908090f0a0204051803070501021c050f0708100b04 72
    0x28003400d801c2c2c5c802d071b8840380d0050000008442c4c2c6c85425803503246558103480c0d920403140010a40032038001701240300100d03c0d000d0400400c2d01030101d42c10200d0800c04402c0000c0c1039403c48119140313440070b80b20010016501c8202000c0c4100b42c087ca80807a00b640c40c0d080503035818045c120000c294a600400074000c9010b0140614147c0d4103450060012800768004c100c2699800391141c10200c941907900074001100000303940c1484000341c02a40c8560b902e0301c030301000c20001c5070140d40980100e40340095038a0124164203007910450404040e1142c19281d907002d1500500030a1030010320340d80800c84ea4402c0c00280c40041c82e445190302c1d074610540c03450f80d0421010361540c0011801c4c3d007001c02e82c00040803403166074102c01035005103648240d580810002d000e014143d030000196034071a003d04400203000a1070454015000547c0c0c4029840c03400c03480800784400c00d0300151401d01444402c481804c8600e4002480c1d103810b01c041c0d240e107041401c0e070030074036440103035803450000c0d00207500c540d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 427374379 1250 427373129 427373131
    0x20a03050a08090a05090411010c0311121914070609062d0b090912090a0504060b071505010e040f1b0602070311060a0203040b0708070203060403030914120a35 70
    0x1040d203c0c4c1828603030320310521114200640300107100c030000710240e00d40c0d13510507080858258000e1505000c0b014000b42d02a0414a46000340c1e0f20360700d40090150403206218190054142031490705403141c81da0200c4130f0781c00740680c80c801008162070302140018081641c11402160b001120070292100c3c202c0500030414070741403095100203080a80804070303031402081c028030400340503028200c0c003030350700014942640c0440c40455210395140d60118403078a451080b4806440b556080c240c2d070380018107028981d0f058107284d1034440e07400c00703005100c01c044180c4c4140e0410b0788000b83c0c17140d0543d24070740b044402045540340080b072242064005072090303000641c941103a0181d944809040110700038040e00c0d101d8140d12101581c0108401c0203c0b503040c00042ca8440d00500406050908942c0002e0070000261802e03800680c54481140a000095000348442d034410401005141c0444100101c2800b60220480c24071142090240b02d05101210760305500e20095840034180006500301c00807544 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 427375629 1250 427374379 427374397
    0x150512240306010806070e15070507081506030a030503040f0b04051c08060d031b0f050102121e150a03050a0506070314041a040602040b0c1b04020406080f04020a03050a08 75
    0x45010400300c00d8200407035001c0c103898402024000c140d80314a41615841240c000c800d030095000f0780c40c5451803000b075022340001881140600f01880c508a221032030850f4162301c680341c074542c03102071141d80c2c0e03800034000c500c41e545824500d845c0d99032800d02c1d100794020410080e240302a94010001044800b0a4551120003052100c0c181010b05400454a485085503010b4002244d4160503000c60300400c048601c109240d294008414600c0d518810789129011045400369004030f0003620442c101c550240d40215084100ca041d2513170f05030002510344015000e80140d00070302c040059603032280f07000c0b04051900441191128420307460500e69540d421a480400070349003e04008114401000c241d000b40e0f00140380d5640328044403500e00c284040a00b00b1a10703240c0c02c1100240d1464020301900000d07008401809414104410000ca0791000343e132104d1080f40704000602c99a5081200560005040c01c41000280d54602c04940c001245030070180c940d21804241f6010800d1b044020441d401c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 427376879 1250 427375629 427375681
    0x4180e0a0c090c1d090a0b1221120a050910180b010b040515031909050a031403070203040b0c0c0301060b03220b010501210c05090102121201150512 65
    0x14001012034000042c4410074141140c091401c80d110f1510000c17542d0040d51403407000806400c20303000a203125841004020460b08204000c540c6c24060311030007061301d10b42e11520351070000a8440c003000414020aa42581941d50012400002041012121030990301e40108540c1c014820601c0c980d2900103400c80c0c403810340c0000410300003107010664003180c0d400f400381042031a026081c810582c0009004078044444d00301104c0d50b518960080307a491901401c05410b01142a050040242010503500340c2000320070028454015800002c560403641c0e44541c19844840000c8200c1c10000098481541913080040100d100e20207400118040d21780d2003100c0c410f0172900910002c0c2504e00c0c140241404140c5c100401032940502a030110490312180710341c80048141400304c0440d01d11001e041c00090340410203010558040040c4142d001100d62400d0520000f4900080000c105014013500f030098903810ba41a9401501668000740903e2000801c2c0e25002c00b03140713813076040c4640c1c0b54002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 427378129 1250 427376879 427376891
    0x11112030c180d02030c0111190f02040c0e060306010c0f0b0a0510080703020907030902010c1b06030b01230903030724060b030709030305030919060e01051b04180e0a0c09 75
    0x25142261a0078200f5a0140290100065660040d154100c944d403580d242400f039a200008001004142c100d102442068546000b00e02e500600c401c9a002404007418008000b00708000ca030344103403d5aa0010091030104891811450710703c180d0006118000c104000c513906114104540d43c00c400c1c0303e41500c0220032001540c6d100001d64401840c40040e40008804000c200507611035009030310401d0040c10081150b60560307580041101043c0000d1041042a4000740724040c0d16001e800441e5600740b800419503030035642d0400c1c1c1100b0012400411020010740c002140c2c50500c04d81e107030340d60001000003c000d110380202c10007800c641300c010920f03890040b01050381c49084081c0c0c1e01600403540c540854a041d0356041d60150b2010f00401114840c0740c3ca0040013504403c00c002c2c142c0d00c201008921203880c0d05c880b50a603517010b441160180c0e003008417a403000c8092400d4070111204441aa03802180303000042004080300c1000c5036041c0950078192050201141c01801280d081c600300f0001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 427379379 1250 427378129 427378177
    0x305061009090f023a060b16030e03240610020d031d0f011d030406140703200a02011706010203090d02040b0d030c050d030515011112030c 61
    0x3840014142601007610741c1000d00c450380181d40046640c07002480010301c3c09a290b42d03850480ca4140e00500145007142054550302c1d900c015404001c0da2005a0606c825410694a105680103040e10b10000c103410044400c00c1c50b11a2040711229074015068603058481210000980d48180c00a541c11103e11400701c0c116060901408460021a031f000c0c00d083d4100b42002c901400c80241c5103030040c0d4980c00058044981817040103003041d544000040c503003200d820003542c29060341c4143d05907500240410402c29402903800107001c2c85045013150750350034a280035112044ae1507901651840f0b80c88080d440d6100000b802c201d0342d4000d0326111070803140f07100e40301c40002c400c4803812b00681003400501c0300303820903405500709284000e00100d809000300000c91141c5035001801e03800680d007145608244082404011566140c615042c4894a04210407101d6034450290303050402070b8880c1000c24260050054800400c0c81d00f0507242d581c1004003510240340c0002500003018048032a0b10f00d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 427380629 1250 427379379 427379389
    0x3030b01020303130212100f06050a0909021f03110304150e0f190312020a0203030105120a030f12021314030f06090706140c07030f032703080c01021e03010501030506 73
    0x4411030151484202c407100c00da0a11980848010402e042031049100351f0b06819480d011b00454400380c60790008215241c4030802510050355407111601618000c030520140c0c6903c440c050240ca80303644402800c444402d0110010301e01e001c44002504004810b00080046c3d6050003551180403000601405240076011612032381c01250621181d800011006040d06d1040c07203c1c1e5200340a07044c0f40f07415000c40740410080e80e000902160050700000014405840c0c6a0090384a80c280c1c0030040c0301c02071241c7d80c060030801c8584551030070701003203268522070260507404460116034210031010985650344840c21041070160002880390003a400020500d040c00510f00d4032800b510001401d1803854810700b07852284010324040c10880c0c4c10044011f0455081015200652150083c44001105400c00130042c0b190810141c1540c0380d24032490000740103e54801c0152504007042d1595034128500c000d0081c403c0e0304890b642d4031011500507281940c00300165040710700a0b04c00b80980d542d4481080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 427381879 1250 427380629 427380631
    0x304030c0b09370f03031106160e0607080d0606030b060a0813050c0901060c050105070302092101020408151509061509190b0c150610180e040b0403030b01020303 71
    0x90b4001c000301c11035401104507100c0c51a0030303c0a18200a0191810f0000404601e40c581c100080c0521100c408204040d40010b00c511510703c280c0c00351101d82001c1e81c818089641c445034070303810040b20050900701582d5483c00c940d02654401c3c52030b5640d0810b1125100686964880d0401080c508521b403000c1d41001c2080b64000c1801d56a0010070b69580c10701c1c0028908107032001e07941440f4181c034003240791b11916a9603018124540301c80150095925142d0709448008005508150050003209002d44554031a6220081055042c10200e4103406080d4020b020f6070344050b0301d0f40300315192541070412a070000c030300554000c90800c49500d818400e22585e10002d807078058008550140e209819800080581104035004204e00c07040e5800888452469500d034010303070500741001581c04050001007040714903424842d443c9001500c2c040700040d0498a40b05420402d0020a55600740a075551380c0c0114040d01c85005402d000d42803600301340611040440341100483c2c41c0451001d0158000000e80b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 427383129 1250 427381879 427381897
    0x6040507020d020a0f0c0308030c0c0c0406261f0b0109210206072414160e010507050c030d03020c060a02070c050f040b1e0f120601030b10170304030c0b 67
    0x100404c460710354074000070b080707900750907180d0318011400800003900711401180103204031010142c0350f80340c440c6014144401402c2c03480c4190700c0c009003040f450441d12128440b00350118114040742c030b11490f07040d04128078030541e020800d40d0101481c140d048a680302c440001000e070f841140c2a5114422a04c0e0041c0b4000242803491001d010703200149401001400700c0c0340302d103210002c40c0340c880c2d02c4000c0c05407070115030620090701c6840500e180c014138610aa40808901c03440d1201c0030750b11700c000d81001b00d9290090304004000401c1810f00004000d88120400041c0440304012000300004002b50000401d134401d40c0110310110301ca00c0041d0095580060300301c0c1ca010b807401c1c54481001038400e8150740090f042501c41112007100d940d00246660340d00e2240d0fa0f041009184801042035584152401c103100710115801c0254441c1d000442078150381e8444400c030502e0701c9180e4a1100d001699200119250800101c40e0780b0f50004030180080304c2c8030706e1801020945800400001d8081d10b602c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 427384379 1250 427383129 427383133
    0xb0a0e120c06011a0f041211190320031e0105101a09040b03100501030c050a18022107050a0207050418020f1302040e04050c0301020a080a050705040f030b06040507020d02 75
    0x51180c0545484120081c1801c1080746142141000340035000e031b0011b6000c0860118501c0b0b070801800300b10303248401c00703180c125115206440440413103010641c0600001d060890000740c46c056100c0107489690102d040101100d64040c2d8100c011002c956081a20390448e50a11010524402201201d041981c1800900e81207880e04c4400d020400d0300301c001303519401511a000c105494800b03200940030400c9100002c111581941080481c1820b9640881e01030b100001c0200101c10f2007002e821083c0200c44070150707907905d03015050940f02e51055815840107070114107000e00c40b41c00c000288041101602034580c516904c00811003140e02807000102d0f940700700101c8a0051806207680425410014194800400d040800d0f804030b1300302d42c000d8104182c11000b40418072504002c1d4a0890074110005c2d8580b40d05050b009084100140150b01c00301e4403800880c480740d0090342590060500030744503030500380c0c2d64184950494825500caa004918001c0440c982605c0480d00200141030760300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 427385629 1250 427384379 427384381
    0x327030f07120e01020a32010207050c0303030912030a0902041d01060f152304090c030b06070c1205010605090a06062304150c0218040507061805010f0c0b0a0e120c06 73
    0x101e80b0882c0d035144401080003445000b000940405129030480041507d100050f1201000c0c54428070305404001c80c14802da10038400c01181e84000990710540e201c0f841c200036201d446900038440030b4800031030020342c81401e01e40070724012045107440e0015102c0b5103000b402000d42c2c40c803940720813003150b01484801c10464010b101c19503010b14807101c160103c4440815842c116800d0b5005242c1094101c030f0030480e00c60031100e43c8264036010700034800c00229501846c0c0b104039034136014140a1031280661283c4c000303c44c00c06001003036200b80010a0f0141100c24589040c605540003007041d805840e022401d0380c5a0401c410090407038500d102c02020900754545400d02d100060403070322030b8400500f0000c034540c181005032250405100c80e9031202d42c80340002d0030325140442c10150a0f40010302008800444504084206041101115008c0c2041c00081e040f4803c2150541c20360007014200e03400c1c0702d0600c405041c1980c403148040c1c18400581d0214090090100308610481e4004281680010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 427386879 1250 427385629 427385633
    0x209011a040e1801060b0309151012020303040f0605130902160201031d03040f0815090a030311300a02120a0c021f1e020c030327030f07120e01020a 65
    0x3a48143d0400500c3c0142000e00150300d119a0a41d11250002c030342000c0080b0900004c00010007000c02125201e140c80c51140c030b04440345d040031070001e1103940300d07111000c0c0c000c5080d51414022a0060f00a101d034102916407030b500c010f401c550003955640c0e0000b403540720003c2d14111034030030340c0c5d001a01000d45110003641381d00110060620101042c40d4001650f103441c0b42200104014002455100c00d642c06081c41d0072031f110700344410700051040000d081800c01080f00d03c0800c50712581941420001100c3c00c229841e0001c0b4050b90900280c4161400408542c0c0c0c8520700c2141015005841c08410b203550f00c0d000003040c0d009044400041186006c0814440c804680000040700060300c119110208117854122444c14001c03201103200b40d80b1151852080c10304e00c501d6528010f403a50544c50302c0c025007052680d034803004000c450a80280518503880c0c80400b0440c40107448080c08903500c484e010080031340f0540c01a10201c504140090322040b445000d0031003103001410580140415411716 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 427388129 1250 427386879 427386899
    0x603050105090612030c013206030d080408040f12200d0b180a08070515010501122a0525020a030308180307030905031015060c0503070203010f090209011a04 69
    0x21138658000c1d400709009130b40301d803d000d01c1840000c01c00e0160a08a4101d003915005072603200000c075207401441c4104201c07864500148000d01c1c80158070b05200a9503d504000243d8060364000c282c403889201e0740091810100700c541c44000340951403601c0c101406807940d000e09144d800c015500001050b8101001c1041e01c010294000d100c54590711400341c04030002d60030a1100380046840e1000131400701c1c14442d04001c201c03806882080622004e50410340007800d401d2144103140956a22280509505607a409101c17002101c100369000c2e100180c51005401d41d00040e0444890128800c1069440140c800540e48260b40207010f800d80181162011209410700401c20702c041010742c00c1380034080fa02000140303403660190752403420550a00782014108045410400482e40c10820510708400c0c400340c50740300710390a034200445201d460b45000d500354000c006001e941b5510b050900d1008446a800480c5c10070301c00c032251006aa03d40040d0808403000c1491040c4050b01400107214400700 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 427389379 1250 427388129 427388149
    0x1503060f0406230612012c070315141803270310050703140103020f04020a0c0f050607080606030601171902030901060f0501050f04050609180907030303050a021204020d031115060a06030501050906 86
    0x105000c8d076500b140ca9454840180001003126180349542e100180b881000006a1035080007400c901c030b10703181c2c070525a440c0c0d480c02a41c0029041f4140c43e072401c041c000074506042100c500203070036104d00151403110030000b003108496039000709040040d85154881143e810b00e058960040244400502c490b080c40000d4101c00c040d1428826001c107010041901d602d42070050f0b9200344028851480d0686d0018200a405861540204030601c244a0700da0f8120301e20000d03031114000c1e060066540c4201c00555801c0b070f03000035840e00f4800800d1058219040d00800309481403031412036903240d652401111144104160300e00002c400740018071092820b10010010b17500020b24821440d02900313821004980159680c400680c030a4600700f00301501809070907800382c804003003107045c0b90a42204029040000300001d20488182c0188003c00d80183c02d14440390320305204980c80d010282d0102800008190b84280c405c12060100240352407107401418140ea034054014170315500c0c0d09003886400d8030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 427390629 1250 427389379 427389461
    0x1050409020d08031005060d1e1e0e1015090b060301031a0910020d020304030f030e0d030e01150e010f050901140907020a06020307171503060f040623061201 69
    0x44000c0c000180350341d4240181c10040344045000900300e409400361001c034059070301027207046030415000c0481c0b0588410305044040c030003030001c40c140403000090b034109020030743e0000b4418a40301a6020004004220301c0c141c600003041044299201400c011050000748002001d68204082e50781e001c0c0003d2103401c0e0821035840c1150860002c0d40c021000341d030040609120000e83c040b003084140341e8000c041081810030740c20b04004030459000143e486880c02038400c0c05241e101e84261030900003d61102880d1410801c40e4a00c50391210b09680e6010300c01e20a1002401c3da070040402c0518261400724129040b85100e003058400c2802440b082d020f0081c66081540250080203011801c02d000440c4180761a6503121101034910360b0030115400042c0604140c8140101500050740300080d0f00350304405140915815a40e039807030264081e1002681801a0f07102c90402820b00d0f14916624500a1004031006012104100341c0c440c01c859000041001e034905505d074500440a0490740006586 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 427391879 1250 427390629 427390651
    0x4030f0e030604080a030c11070902211006140a05042c1008010608031309090c0902040b0a110604030e060d061e06020c010903050631050a0201030501050409020d0803 73
    0x58140c80019051600071601a00d4110001502d01001d66140c803548a9080aa003410080e030503800f01a00d503540c48074000c0040060780020300700c2c40c4040d082c0e0080b10040c2d86070900d8400c1c7c500443c1c240d1151020b441100046111030026030803001c0c0305c0041d0364070b80b6826a265800c191500c0740b9040c0384103102902c00145400081000010041101c0302c0f0f1203003010040e400c46003403406580508580c0b5660101816030800d201002928081d050600119003a500001c1601d590b24140034544543e160f0003c0c000c1d070710000300029480c21b10300203451101419111022999085001c40b41c8404040354000c000890031a04111a8034180740540010303c40c80500003201c0d03840b07001174000000c0d03401a210b400790140004104856041100540c00142841c1054010b0700c3c65a40507030301c50f0701420702c00e5884601070b01aa03005085803003600c900030342d80303403442545034583c1403003525458aa481a40024240000840c0314180760040081e100e071f000d0292525484103481e10b204503000509940e44c2c01d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 427393129 1250 427391879 427391897
    0x10509210a12050711160510141b0c06071202060105060708090d110301020c011a15030a1806110d050f0912030915010b1309050c090607030e03030d060f0906050904030f 74
    0x30170b20030001c6c08128161000d1850000e401e0108200d40c11010401140800043c0c0303141c0340600906405641500c610f20062484404003d00d600d810201200107840c0c0000006c0748103005e20103070700c0402112030416025900b899072a98144030b400d228842d009001c000d010040a007031403c01e00c0016804030300440b4480081da00c402c0c006401d9900240b0f50054a030744544a00030320409100031148143d204846055400380d42c501c1041c91400001c05004001c2e50b180080f075401040039000e800421b40c4004104946c1180f4602208c140e00925450303080c5914000c00200b880f448284211b024548450080c00c1e11008000344130003aa1008002d458a4090041e81c650045c2d00c040040f0301030102e50031800d440d060015282200007110307500c2109038905183c1030103807080703002045400542e002d60340765039100070354141500c81d8503901c00c080d80c051000069213000c0500540c041e1082c1d51000e0100f80c48260b035940064199403250099650100d04200850000790042003100354818460500c0322807 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 427394379 1250 427393129 427393157
    0x1d0d020d1401020403050105090d0e0d0318060909050703090305040b21070228200303071406100f05060904020c160b0a0f0810030210050903010509210a120507 70
    0x3070340819080540150f900800c0a200300f240030700485520204040040141c00e884034001480851b481092900514031188000705051040300e48218a0f20200e0302413210a64550006042ea0b00c2e502c90f1030310b040e00e00301c04103010070701c00d000f00e20080d0381658421742400c1c107008045070103030b2083c100ca0003002d031203841a0103441010025103114100300d801500c0010711152a0300e0242c0a030b142082058030900c0c006900040c40381c500d40c00c2800140d88040742007044000406d20314403e005001c1c2c9103009090728030f0b09140000070054032603c0c120110100c03550340c504185809400e98001d469201c502070200c0b89050600303502a1204440a6007110030b0340c40390000540869580d900000c820300c00c00203103240000d0b0004c540c400f85000d41d01d0641001d250080309260308030401e00000784600c186140c0604554855400d6407680c480c020000c00c143e040402240d0b95078260b14055a0301c00440e11074411b1102200310030f072032040174591034182d424115520b07020010301d00144544180800b501900c0b803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 427395629 1250 427394379 427394393
    0x90307030c0905011d0c0a1412090105060f12100510180204050108010e07080f06030f0f0705040615230d050c07050c03010c1d030f19121d0d020d 64
    0x100700b2800001000e5050009000d410380001c40c5180c0000610424040d50440c6a404c996601d1007601e403040000780b04001c0041c091141c2200440c41a0802c02402001e910650059019000c211042151407007040240141841150000c010710382014880d100386100a801c03080e885103030708400500341c546401501c2c02900c8138204d0031642a6010505028035600581d1071030141943c541031900c6440c04a500401c0c0080041040e2032070744510b800300d42191020032040308080c40f1041503d03000c144090140d40d8800c2140300c3d1911440c201940000c05e2158074000382804e600540c1e40e00c40400c03030640190506000540c5104050b20100004200040f443c8501070103441032003445a40c4404500f020752804140000007803103a49005420b10099410038a1503251110a4007542052a0751500083c02c00c040042107800340e000d03c400a10b00b1205442c05481124418120611108004081140c00011039181c1143e16406d895100003903242644a000d0003d2005000b003881c60fa1560343c2171 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 427396879 1250 427395629 427395653
    0x30b030a1b081b09130f0204050106020d18050d080c0a05030d0203040204140601020c130f0e03030711070506030a0207060e0109030203040602010f050415050714071101080c03040201020604060209030703 89
    0x20107000600c101840441014005124040c0c0038281c01c82842801d500040e0b42c903440501035403910404011410308000c803020410004540040040140d503035a0b442c040c0d00c6075000144100002c001074081d403245c034401c0700f00b48140c0d10043c2c4014000300d103941e1443c0f5180d000c80300b03c0d00b10f403041e02d80460009004000801025034005005621703410240b0510040d1a44447c2e001a19411841004066603000030401600034088840c4a0100c1c0003000c4000140005040003001c00c0c100a0f00c4003401c40004021400346000f0b541c2e9881c64000c2c60030240d2031704143e011701c60340000c0400200c0d110720f8a42c1c0182c91841e0289000142c0c2020803140c070740c00c441444100302c01580010504010098080c407403944a0780000f031052282c0c0c0303801d80c0c452152240700114119081d41d96404076010502c1a8050302c40410001e0320207944109500388007081c0041030706450f00054840e000290031f2051101030f24000d5034181c00512883d111552100e0184d0445e05076181c02d0f11a203c400000b281d141c0c0304213 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 427398129 1250 427396879 427396913
    0x70c03140f100b0109050102031810050c250b07080406080411040c0f030c091212090e0114030c04020a0f0804020f0a0b030f0702010204060507122c01020c04110a030b030a 75
    0x1400444070f00001d0f007030300c100d039000c681950014443e02c00d589440c04142003120508030f403100f90110b6000010b07201401041d8030b010340b82c850207481c0608040e00c407190010b40c1034180c0040b006c85a85e0061480c20788030715440100641800d1004214050140b1400e40d0068400e060961a000405021070112500b003414840000c130352001001495400d403150200c500503074940a5640c82c200070304940d282c101caa00c01040204140204e80c6403501c80e0b45054043c1c00500d071207040d00e503520b007580d07642002c200d0207081c07113170260070104d100e580341c00d1080b034101c1d603e15210001c2d2030264080c00c2d541e0030801403081c0e03001078a50480010950350707400302402420150341095202d0a0041d640440103038000c200d00300b507a1040005124543c0c004003941c48491b400044942e241180307410445500b142c540c000012410b80c0301e40d0200804001e04101e0007600c0a908940d0100f95000800080e42d80884030200a20790070481199154400e070001d660300b5201400301c490118441e901c07a9900c017044a89 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 427399379 1250 427398129 427398131
    0x31d090a0b120d1b080717030403031416030518060a0c0305130218280e150106050301170a050a03090503060f07020d08061c06020409060605070c03140f10 68
    0x1d0030046190804150100b07101c80d5009101c60810b4500142400803140f0061500714041c2c1200f03402c004050003128220741c0e028100052110100e9884559600203880c1100802e080c11002d10401205d00c200318407584902442ea411000c0011080e4001d100192600b460000c3c0801c1342140c1c2801000494000d440c24100001c8100340c24030002e00302c64018181401d405514200080075aa913002682c003001714002c00344407140c854070041d42810204603c0c40f0002c200210205e80c8401140e404100740c0300110007690401c81415602c88600c4109002c0c0360301098040c0014003040720401c1c0075100180201084440483c61074031001d207000d024003c1180064440201031186040134000304d82c01200151100c800d609006401035128101ca0800100b0000b12000141c07017959000c6501140c102468500e41c0e0080281c02c2c010b01071b522501501034001e05000000821074490b134110b40019030801c8608078402d06542e1210806118200b4001462048410741110b25000740715150f460398103064 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 427400629 1250 427399379 427399391
    0x60a051201270b06030718030b100f0b032401030207080715150305030f0307031e1a01020a02030c0907030b1908070e0f0f07051603080a0b040902010c031d090a 70
    0x1e141c0d402c4031101410321800c1e42400490040c0d03031034440989400081303504060016110054031142481001d82c0064011a2008140401d07556442d583c80269802212035080c1581c0703c0f01901d81c0b030b1000b40c80d20b2080b014520850842500c85009070240090145400340c1f6207d10b0fa111040341e6004003406542488280c1c0c417081c540a101d200f440c80b00b080c42006508600d05e103840d05503c90042a00007030b9074520000000d03018a10a6010444105010003820b9050102c14107100042940c03d0100460b1240000f080b0840e40c000219074582c1603004009042055402041c0a54800d0242c410803e240d140e0b00100a5507032040003000085092070138030b104a51403d41110724104050303020652100c2c00ca418865244a0144880c3e03000c0d02010880802d9114000304036514868240080d0a03d518900880205070707020304141d00075074012109000c03c120100800c001c032002124001e01184241904400080c0034850501c20b5000000c041308900c03101c0800b103450031400311a903c810940e030b40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 427401879 1250 427400629 427400669
    0x140f1206030d02011104090b04140c070203060609161d042d0612081605030c030c0f06090a030f11070609030210030b03030306130b0a0f17120306060a051201 69
    0x8000c9402c20700601c000e00414100c8241e0b000188518055482e58039120070961401d919507420000090700c0748001c01c41e09141c0078002c1038264000c510104e00c0b0340141004900b041c90b0100700c0c9400b841000a240064040c480d0064800070001007000941203c12804040c2940c3c5520924444060b0b6010100503500c10005030b42d050058220340c2e003c41454101d043c0b25160081c44800a00c079403141070940d444a40d080c051801198601c0018110b00c0002000320a0010110240c001a94a442110b00c00458000f240e500c8100845584125501c9002100c012a02c6442c43c0620201c403802c2c48900d1310322055449003824100d422200c00305502080400440c109640c01d0b8a45d10f1940ca400c110000c420300001341c603071102401e0325200f0f1422a110700e01385841c1e81d00074000303018010140210b0f59926011a21841c100703224114468400000c4140041c00220364142e20b10400089140b4540d030304000c210494221300c0d5880d003001010701c0381e400c0e030254040545018080d040041c0140007580 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 427403129 1250 427401879 427401883
    0x30103050708010612020f0d050a1b0b07170a0c0c0905040c050405060a0513020405180114030613061107082b0204060503040b0a0b030d0309020112090203060601140f120603 76
    0x1d40d1003802260701d0208200040d00200b44100324441d412640741c00380c20503040c002480d844e96107101604c60700810b50400200206a041d8600404035695000e81d80390b5a42c00c07010141c040c00b100500800309510480c1c8480030450010318500b640c40c10074812021494403002c241080740c1d00802e80c402d64601c00d0200b030191031604440101800c840038007240c94a48003140100e1000e21440d80101038114003020f60104507010382d800313041d01030f000724900140b851400c01c3d1140203200d580c02900140141c2c180c00c1c00c0100f08644210504220904c0901150ba9004028030800e4106800390001b4131981000072940b8005080c0b40d5440c0824019202d02d0000d89070b906243d80205905880c4100010000550000c05803a801900580c0c0f290050390f0300840728015052a40c4007513410f000790100d00d90352541652180304124000c0ea9031007000c414242c0b00c0340c126000250065856030003440024580d43c4914012500f5003070385d042c80c40c1400c403441c0145040d60007090445a40105182c2007000074241 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 427404379 1250 427403129 427403143
    0x2030a1a040c05153c131d04140102190203090405150102100225210c0206190c05010c030c020f030a1b0318090606110a080306100e0301050c03010305 66
    0x10403100c8214038001203c2d0140305202d24403985e210000d02c40c1040080004a001131050340098401214400c0700d54469100280e01ca4070200030030007407005000c6080c1c007200c4501102d807000c3c3d403400303102901c0c1c035118004c1c1c60034501d05c1815030359020005420490055084c1c1d500380c9032150025a140e04080c0108401e90b0f2000b40910781210b580001f0100c181c3c1d0011300008080700390040141d840c07210b0844004490305514114858034020440310080004042c100105440c0a40c182001d450042c03600300d034083c60702d2001942c000d805008040b400b8949030300340303412900300e402c28644240359682c600742521036007034000c03020a0751602400801c0b9014428081c107042c001018510b8000e00c01f070058071380c81d000c02044100080c03900c80d41c801c06009075081e0081c580021508821542e851070000f0280c038541c047c400000d11901400c005c40100041c00ba407005a101201d142959102d409000030700b90303000c06800422079800e00c0c081d01624288a5940145201c2150644d2076045040852501034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 427405629 1250 427404379 427404389
    0x3190204270c110c010c1713080601060815150d110c0f06040f062c010c0e0303070b0103060c0e04090807030816020601051c14010b010e0a050a1202030a1a040c 70
    0x1000680314030504404588132500d12801d0a00c110300700898109003480c3c8060800516140c00001162011800e031a00300340c01712202101110340680c0c84800072552007000b0b8540c001e0888021300840c0a900e010b9200200703181030540c206051644407901102659070100c1007a4410303c00158030060003c051088090440704000109400d003025600e100c00801840805170109a13241143e809602403c040141c0c00340c019109103000c108004680c600805520411001003020803040d0241400c0101c1500c2c00b858004008119a0780f07940c0303515014149881604040000c0741861030f40c95580c5203d0001e03000d0041d01030944410007864042d00000d0082c040320250340c9160901024641d000030290705541043d20071300310161100c1020f42c01d804071440018041841054810a546015031048001203002d03078408070207000980920000c6101809141e4008440007801d03c80030b411031070b1038445c0510160846e0009422a11412844140c2d03d000307040c04031191080c001840842c4560002400c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 427406879 1250 427405629 427405637
    0x1b070f150618090c051203030604060e071e020316050105010e0105091303050c0319021609060609050906030f010207080307030501051806130e07150206010806060603190204270c 78
    0x742c188041160b080714010041c0350b407180c5032040301042000c43c020f840010031002c1c0421030b840903c20202034403600100d402500a51409200081030384203284114054540e51300ca41d6080101e041885031801c00700341c070140135407100f00108801c058003080285400c6014100006540d41854a4030180784410380c00144502e00c950107100381a80502c1d00f014203d0b602d4140103554455014845055009070103021090449001100610035000b090403411b50100c51141c01c9525201c0c110030044580902802e070000d80480d405100900b008003802da0002002001c503681c0a240b01c807110309a13400680d013264210300100500004640501030140501400c40328040b103080744803881d03000000020600380c441c204030300d1230406801c01070344504c80d07104011080d1403580f0346a20010342111030703403260480188120000043c0007140400c85a01485000300024a15192100c0001c100b4a5890419a9159080000280c0d135422005090142001c40203402804114810240201c4030303208000000c0c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 427408129 1250 427406879 427406891
    0x311030705070506130306020f03090c011d191203030605120c090a0902010e0a090b1c0c03260a030f1a01020a0b0a06080f03120115090902031b070f15 66
    0x58000c01c1a800381c0703605a8120317441307040404007101108002c2d8000760010340300142c140c4c2e0301c009040c02144a03900005c11254160004001107a00102d100001e0300b00001800c80d421391442c0c48a11903000500d00c0100c441c2407074540101e0719000a84103c2100840d0307640c40104101e0400a00f01a1509204400b50400d480350030301040701d4003802001000c45139954800202160b0040031010134408000d081100c1d0365448107000c00c0100018903a1910416070404003103105421816817040c1c103a80200202c0404c1e15560b00d42918058003101e42100104136030940841605110280260b009665800300b03075000d840010504031003001010160106013102c032006903036000a41650361a5002024201d2682c0c0c12007550010720341c9410140e0180a96248440708600c00400783c4107401180306800c0036030745c2e0381c0d5810200c640c03a441448041004036000700712502983d4007440d48600304221010030344094011044140d4070001c411500a41019001c1050003503061903524021286c500400503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 427409379 1250 427408129 427408133
    0xb0c160e070c030f140a020a1104180b090109080307170604020301060e15040f09230405070b1c1404030225030f0c0b160b071d01030510080d0c03110307 67
    0x2c018980c141c080c003404000d080280c1c80c07030f00c5911000c070005c5200c1d92041d219100c500000f5107074240340d003043d81c040031b409141c400300f8a070902c03504901c0082c001440003140d03415a43c6030401013004049003255582c03007400780c001c03600c0c15000f0352003408140e440c0102c0d2f000030b116090b600200502424011403051006000654010401280500040700c540013690b403850421903480c807070380d0801d0b03142c40381d4072000052101030b54101070002441d0502441c0041d1071032a50000d40c0204a8002c1e00c99481030a04003c40020300b070080030520380e9443c50400700b51b0b00050100c00d03a01c46104d0411030a190404010506505206948803c030751000000b04000102e624501c000c3e009000140c640308621000c00c04100c0c44401c001c4c0109403e107003841d201d014441d5031008902a1450030340f200b85021000644880c8100081451000c220420140444103100118024040140000c1d00c0c4080d0601c007003070400f020000340300d8010483e41c40549030403661800526291400701e050040c2d920502c19000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 427410629 1250 427409379 427409387
    0x7050d0504020d0507090204170d09060507110915030c030604020907120905121902010501050306042a08010c020d03090b060415150e01030509061306020904060b0c160e07 75
    0x500086221021565881d10700001c1c5040e4185480103143d4031660030b0000f40b10200b034024004a0b5400c0c1140f1401040c98404070b134441d1072918036500010b100010601160f40280b001e06407860050011100c2440401c1c0441d007070b00b1040d00e8bc0701c07102d0300001c0e041003249810401d1042e2101d046e400381c07000c2d04003540418101032000e404041407028000c0ca0005200c02c5a018040c125006030803142861803180d1440d13022b1713020b089030f0100c2014844007880d066005000d01812200c001d4018545a6940c2c1c440740303602401c0c551600210b44c0030102514890210542c018090a02e8000010715140c640358082e2030280100000000d1508010440d40410340d140385c850741c011815035000c0f611400582e20307a00910b005801100e454509598440c8c900340e4810858203200f6800e032010401a14ac480446a46581c200c852144141440075010006012500178010500d4041c2000c1039031600c1d0003501000341c003d04965005540080c29170000c501420200c180202003941140c0320074104030130010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 427411879 1250 427410629 427410637
    0x40f09090b1b07020901030f021008040305030f040809060a020c1215010302060d1401170601061b0201030c0909020d0209030607170718050d1203060603061401080603070909080c12030705 82
    0x3a1942c0303403942d10014156450122240d5550040a0700d0752503859203809030081510180a0b8003c503807030080c18607031038007640c41c150045805880d0142140d48011900000020060084a00440602042000e511100007406100000350007412020341e004040c400b101c16030540740c070a0b0303601059440c04041c9200c451181980c3c5c0580d44d1550f102d064074030700405400740005280c503260301c11340001a503042640c0904002c140880950b0f04603680c440d022201c640f410307100742c03500890240c101c1c0019806075100440341603e6081c04008a640c940c110404c0745c01010001c030034107400060282c45c514092040c03c0c2d1003506410b20040c4c6039030b19890240c03c120300405600074084c400700103114548155408030024180148011040e0f0900c0ca41148042c03000618807000c00d08054000c12541d002c5e00402d415038143c10601200d4025000045840500c00b62001e905030280041c045982d8404c0e000f00c20445005445256480c80e04600f594540340b680024212440c000303005101c0c003c3e51000c00c44d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 427413129 1250 427411879 427411891
    0x115030204111201032a06080c0c1606020a03020f0609060c07050a060603030c2f0d0314160308010e0105010914120a031d18010b0a02070f0b040f09090b 67
    0x40e0070410086501c1e81803140f0302208040c041c2880000080045000011400901e40200360388211040d030910840f0002d03601460010441107400903503100c40e02c1000e044000031490480d25000d401d615403003852005500004016080f1200d0b07481850340411071003540c81615002800c043c074003c1d078502e4a9160180142c0801c0700d0000e004c1c0e0500c40c04102d0007456640082c81004071950740c2c40c0c0900402d01040040350751702085040241d02c400d401c140480d070324110564006d152003c07a81048440148040c044007407219038101c05071000d401c6000740c00c4014252001480c2c400303107402c018145000503448111225010401849180d03071042041c011160b40d1102d4082120485002609100000ea680069841007050000c18164030045204400304d10f4001506074150a070240405181403043d40301c02c80700404010010314607000010484800c0c02e2042d90b0005849814201c88010f141d44484800b9101203414480782c1c0000c08450001c0c04030b064100142030207503486e1081c006000f0b0038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 427414379 1250 427413129 427413131
    0xd020d113307200c09060907051608094908030f01050907031109060c01090803090703120306080d12061d01180903200c06030c1b0115030204 62
    0x400200c450091403141d40069000440340704074035081da401442c250303200e03190f00c8010b0b2195031802c2e058240407403000d8943d80043c0c8450540c2d078886042c03098482019068100f000030420101c241881034400b0364501e03038802c03c400c0383e48180400402940f16403e1881c070320000c02d0071880008104081009503100d40902c56020403007012100740180384280480c0250006100000b084020407811200300c1c141d40c011a500d59164549c004110120307800c0e020009583c50003040224120300c1e012016001100854001003511222a6650192900705491445059101290500403c41c0c10302442801c04142e1404200c1c90349004002a91600e104a80c1e00078003c011020b01510440c54010750054401d880b0020310000c2c100d61242c40707198003481805035060b00d40252142c003c680d405030b00c851a405130b841036542030b84800f4802411824032401c800324414010422415241c140141d4420226403000948032040400403d5010b00c1c48c0c261907405034585041501d8200c041044c6000b9a501517030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 427415629 1250 427414379 427414423
    0x619051804140f04051e0102030603120c0309040207051e06092103130c05040c0903031211030408131e031b0513021b010e0102090a0905010e0402120a0609050d020d11 73
    0x1c005d8248600c1034000c0c0c449a0680b110458044015001580284ad09031304549003104032207a11070a5008040d008076841d0410040c1c41c13607520786500900b071401d01400940700703074901a41c00400d9211040442d501c2a0b0803501c20840114011f02c0400440c200707004840880da140103100324002c0c44002c042d80c58040302001e00d0028000c020742d186001e0040500100132900c0041d1014280301858882140040c035400100340c840302c00c0b4050b50890b4944520550309603200e0b0b6854a4180e0040e01510300105401680041c60902c1426071040900c0301141c01d950990071810305501d5103c0780b041d40510740841010800c0707a43c03100c2281c10f00c4141d08550040c0c90b41e001c810700c0410032a5264207042c0c82c2d82041c02d42c1640c91410343c000d048050341210b00c900c140c1d584000c4803050358001d20441b0760b0135182d10002805400d2102c411554840488280c0e082e03008280e65600807103483e0350003a101c0754480f0740c003240c042e5010048404044003030300786001c0d81c8805203c2e00c0c1c2c1d10186e04030014a2410410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 427416879 1250 427415629 427415633
    0xf0c0c0601061b0609140706050909010603020f0712091d07120b0f060c0601090c0804030f140f1c0e010b0d021e030d23120403030b0619051804140f04 66
    0x3000c4082540d0001045c013803c481c50800040000b0b00d00503008243c0a8190001107241c00703442151072600300603054005503880e040d0154000d400015103078524003010448440080d05220000351014400c2d201c054590f820203450a10030034201d01d011781080d0444061010b615003040c6201c000800405c00481c00c8008c1d40040b40d0b180054032881500500003241442c0070b5440861401d058030141c0104002461a03164101c0d4a040140c5019010507200c4d00b030105c482e8414800c840009801d944000d192031a06e0004429a03400000520b404280424240c078103510140030b03111840d0f0816009203e00903c49000512a03145100028400ea5040c48591011280c050001c0d060b400010f00f40d9413458800c03140684840c001040512031040000710f09070301040d40070140e840d200300d45c1e00c240950342e8956500350700404a00c8035055200354284070a041c50b00600640c500d841e281507a503d926040360380c600036686004041c18912171740c00d0803110640c42c0c81c040d52582e441220603e040c812901e40f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 427418129 1250 427416879 427416917
    0x120e030f04060e090a140c0a09050d0f050606190905130803090d23030a050702010b0402042d081207170301030f140a031d041e050f0c0c060106 63
    0x66800c00503440310101d000201d10b80c002820109100c02038030302080310750b10901110f0031640c0780d00b55400e03094540004641b02c52103040203024469810b040c4401c9054541001400c090030103442114030341d20480f031000800c03a00b4444c407a0010b2041d00e8050801850001e909200001d501030000308507076407800281d07031010003091400f0250308050300b40d0b0b881c28140c0e1411348503118058904086145042c04c42c14060000f02c0100c1e26070000020700c2d0654451b050403c01401010300001c0856486844a241547d41c500c01000148202c009005c0e0700682c00704094600b041c000c590740100c0ea40d0420401c003190010850002100310150b003903075600424034100310202040404007180c1000070002104110b11518030034405401855002c40d41e00314000c05c00d950380c2c8504d60080010303080000b1038401000a0f100307040d44140090010550380c0d040c08140c4c8606c8a165010365001d9241d4040c40202e84801c0c130f041c0c0c1c00c5107a0340e8079a03161141491456558400c184514400c0020016103140b01c0c10340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 427419379 1250 427418129 427418137
    0x1050c03090a0b091c11280b0301090e030403080a0809070e0f0105120129030717010203070f05070c031704080f0d0806040605012001090b01120501060504020901120e03 74
    0x1001d5500c001d8a88045a00039003013620494010380340310701c96540c6290b4a89044400382d900c0700b5001c602d82e034404103202c81d680036120011003421524400250400c3c004202c40c015005000c000c1c1d84a600d04148032042d14000110285130f50410041400411844022201d0381450741c10640c01c2a1640c0c1411490611158030241c018185d40c030a00004c0e08402c080d00d8100d560484004010b42c10350740041c0e08072404100a00c00004a4401d00140d410720074080301c0511344010305580e4100e0303450b03c00f60351041241c41c143c0303210b07540041009416500048101c291200510b815410004c49544284090120340006018403c0008000c42c0702d00e1301204071405020000140d440c40207000040d0b41d81ea6065030b0040000ca10310340700181d59400c09102e041d00300c0344140d5070055511541d08600030300060040ca00c1c140d554968000c08007007031490300c90324001c0842410080c02c2d0986424800c0c00c5070307070b9038000301e20a6004100c00b40e082ea0380f04007017249132144990b0001d0784202d1090346a186100f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 427420629 1250 427419379 427419397
    0x4050a09030e100905121f09150c050d050a0b03013201030b01170a0606030807020a0e0c0d0f0e031b0d02010c090e09070317070303050603010509030a0503150915040e06011401050c03 80
    0x34100c50103000c1c1c030010380029840b40c0c40350751104080e0080270f0010f010f0b03507a0b010b0400d00050042c04501313031100b099000746812442001c0001000107024020a0035103031340900c1d0100e074200b010800700110325504014451034600000d04004c65055589961190206110b2600c83d04061550380308900000d2181c5050140e002000300705152340c0f40303001c02c7c180e0080d80c0c1c04c4e07108a8041c0310003e0411040d5140a103c0d80010f00184d00c0c149011443d5001040d0319481c8100b500d80d08d40c040740b1403540c1000180503180e0070500303042d5052046132503140b030040c2c848002400c6904084041c50250380082c52802981e40c02002c1391440e03603400301503500c2c008031940042c1c840310075091315004103039404e00244690760080d0340601c03240e0703078410615003030319403e0722500813680c0704001561481d44540091a0004100c241c0850000c22039400290300000c142d4001202002c540c00202c0c09103058407481082d0b0040313101402e0150b15042da858100030f25107414906003e4001541c10702c6002c1482102e20f0b043e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 427421879 1250 427420629 427420663
    0x303020a0f0c051305340309060b130b09090a020102030a111f020a02010b01020102040f05060f042310020a0c0501051c050f160908191104050a09030e10090512 70
    0x100a1310b03540010f00390584554096004030801c0104291030314490125080000420302c1030040076030021002028011070585240307a540e8a4500c1e16504c243d201c036550302e84200086074288141c03040003004074006c1d20b6403071650301c400104001030b600801940c1d15441c00d810b000b607500684220b01420111090000426104108009102075810754040c0c020b03c071103540204051441c0c000160b08134801e03400b414021302d8000300d0030811403401500401008851035085d504082c0d84140c401e10255054103c000180c400c07805601c2c281c142a6000424500544000d150700103081d19041a01e41c0305005d400d040000006000b41c1080c415110303540c6d48461520b04202614140d118840002b00a8991041e410607188194120340c0c030502000054850441c0980308006561003100c261251205d02282c014240804ca808546d6807480b4041c419a100400441c4000c1e46280c02410301c1c50440566120b4000c69481048565101c4c1e03d6100b40e43c6d00f600d040f5035040c40780c25040d01d05400000911120 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 427423129 1250 427421879 427421899
    0x110603060a0503101d0a0c0b0d09081204052a010c0519030e0a06180b03090a0209010602030304031107120305160c060f11010c0f21050a0b09100303020a0f0c05 70
    0x21030707005c0d40003082840c9519501452451030005440d203c030a5160003405e2103244050511100750190010700d401c00075400005803260095440100319003000145410f1520444100000d0181c244040306919500340034802c154441c0141d000b01e119418094541001a900703002d00402004001008e4020003521624040d1070451038010052043c07808518004c52641c100003d660340074000011349019814091003020b802c0440c03800d801d82005044c210103208079004640582c5076070220318003030400c0307502031940c0340307407608028040140003241d440c42580300d02400c00125042c0700d9405011585441c0a6544044a1948208920302c21a000d040184140e6000a0312030304400c001c10b2094054440061558000541e1405c075001001fa403030100e01d201d080422aa4130071002c7e15500200175030445e40c031468190409088620403501d044046585540403e268074107000c07000d034801c07001d202075a003003070461398000e4036030702c941500816000c1c481c3c030341c4000c0014401080000c2c010240188141c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 427424379 1250 427423129 427423153
    0x9020f090a09030311090d031b06140f060a0302010e0d0206071704061b050705101809060618050a06030209180f0a05160c150605030709090507060804110603060a0503 73
    0xd00042d02c086010074079161010441e50214000c1c3d841400005090401c0c3d00b03066101034407850014184c00c1034040b0203480308000101c107031040305485a4001d90b40e0109242400300c200401e0005401079200300d10004003000140e90105100c078514000b0340d10014003a00a1002c180b40b8018014010105048441c41c103001e070740c100001d00212489951203508401c103504108040c4086c0240c01781c180e0300030700c005011508025030b10f150740418516140c0541c90141550030302c0b12046800c100105503c036001080a690702200e8140500108c1e00e240c40700d0b62030074000a20100c002c0c81844281f5401180f1703152a603032400d07003003810148400c0004440e45072112800e403420700200c880051179850072000c0390055401c088401248500d50700d4010040c0304135100c0701701114010302030203203998846001040311788080c04084010055440041500380b00c07442c1c52410084140c20502c04c1000e09800c220104200fa4103000945c0c0c0248c549603a2901c81c800480c4140900340c000302d8240c440d04402070341c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 427425629 1250 427424379 427424381
    0xc021e010201061d0402010906090e160509060d0504020a15081b0708040b03190507020d1805030a05210a02031e070b010308071b050f12070e0108060a0f05060d030309020f090a 77
    0x842076102342c0c1c88034085500c0d00320644881c00d0500444104c136500c000025141c03040361f2002d00303011b50759050945c10441d440e00003c895500c01e15407100115200c4003030008501b00100603034042e03c00044141039149580e640100f00c698000d00b12510341420174154041c1140d00c50403a590a1780144c80b455032143c4903604103946504c10b4560800c458117806030030700c50440e20322032180519030950141448101403481100d250500e000001d5401c15421000a1242d608000000c17251340300d6806005440070740c4107002d042e4166401021400035041140c1d0107001e5011003268940902d00c41c80103200a440c61148016000b82c4a00030841408880044140f241c00c00240271a90302c100d240c1100c4d507802d6080340b540f0820b5485626000f2055802d400c4451503c2c0d41c0004080c102d000c221030031565910782c585d0740c0b10001c5e40054500e42040d01880111501800340c0c03c82905107405c140320311304203000800d181031101103000d020143e449281c0401c654071241004503220380200038040074100710381044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 427426879 1250 427425629 427425631
    0x6090c0e1006090f0f0e07120e0f010b180f07110d09030203160e011214031809090105041a07020f060403030b104b0c060c0c021e010201061d 62
    0x10000c51402c5030000340c1e0000c011112425105202c00040b11740c0d282c02400411020064202e074103100013000d030a0132030081c611440006401200040c284218092501c1d0700712034201180c14050040020b0400c07007181245040c90300940105403000003aa10004212080710a0030041800e034080c44800e0300ca0642d1084418066078005c400352054501c003845005d41d0000c40388280440c100092004103c030100c4640c1103608a40034941c0e0b01d0740d20781860601400d541c08188001224101400c1610060900c020340035808100c25002b000701d4100360715a10b900103101b43d003100c3e80554900003d40039a03c280301035990300100c98211001400c19181c060090070100000a010700c0c0d44800380c02c1454403c41c2034646c071441031003032019078600302c111400d24004510003004802c0c0a91940d40004020342080070200e0b0002d03916188a140186061415511181519800c2103414a030203c0941d503500200ca000500c490001e0412008000c0140c2c0541150740c0324118503d5071419409040a81002c00c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 427428129 1250 427426879 427426889
    0x319020a1202070f0503010903022a04020d0507091d01030809061228022a0c100c0c0e01050616020102071701060f0515070318050604080c040e030c030706090c0e10 72
    0x36540b4991505e040c1800c0380d82121003c0d0060b0302945184a00c03465040c0d14544000d42c12501004402d02c075408901030741e0241400660b0b01e5030b80d004118802d680074191340302900c4490303400c4441c10610782c401d00d541c440601014100d44000900c0341596074076101180c60032075804015403150700d1b0040350380c64408842d03c3c25140301c4610b511200155182403080ba40d03800301c2c0d00f18404400b80000311480e040c928800c0c4490b4240301e240c00021007940c03041c01180d0402c1c4181c3d100c00e1386424520b4002c860880580c001602c11810000500040d42d819007914079034075010803074407500c0c011800100e20b404215400001da141c843e25194050385410f4100c9802c2e16035107529158015038503c1400316103040441c00350f40c898400c0c0800ca002901c6200c1d4640d0250b0325020211885884e0780005e082c0354002d42c81140160302c4401c3c2c0c10418103090041c030560341c032540069424940d201c58002c1e184d204a2000130a0350f9612030490b8200414004020090030304041c00100c00c0c80c059448081e1480d440c090 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 427429379 1250 427428129 427428149
    0x1d092107080d1b08040210020d0f1b050f0703050d0e060403080d060e0106120b0906060708130503010501090f150b0327010e0609070e0601020318010c02040f021c0e0319020a120207 79
    0x50360b4008d00010701e0303140c404210758031141e403245002c10407100f000103116a840103480989201020171410820b18440078409030281450a1440c80d006140103601c02442d808d1208208041805540c2c1c0703c00c1e60b080302d81000401d80d503070640d0711000d0f00512803130b0000c2c04540c08000002c01e000d94090140404100c010500300148403a40b800c0150007401183d100e64082e10400050300041d241c0e4018047d950100e440f0300d070510351914000790940e50240c102c08200e95440381c25210a8296010329014013018101c003004c1c490a100301284c0c148002041ca103c0d06a003459011580c148410f40c1c00032001144000700120081c0040386501e0300415a6441400d104548002c28180301406201e405108144c008501d4403a10703000c910200c0d209020807505201c2e44403528005621140115042880c10070001a910600e00302d406425030403128108941078641a07038141c40340000401c5600310300103c04490380c0e28810302d001700e24080038050010b241c1c40143c0303a03950040c0d40006070780d02a039615040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 427430629 1250 427429379 427429399
    0x6041506300309030b0c1201090209130e0f01020d0b0a0b25020111190c090603022101200a0f03180204050903041d092107080d1b080402 60
    0x11035a291465190001d0301035103200603034885120075000314001d5184241802c43c01a80d0300e40310300c00080002c440041080400042e241100d4800100701405030001e21070450900c61100082108061004411840c1e1680e407140d5041410080020705050780041d0003c6d560b0344041c407090400380080c400064045c9100540201e00c00740b8010503104200b0703000e914040d03843da007401c40701c0402c0700c005000ea05001608442d00c9001c0c00a2140b80f03569034244403081c07414007540c030700315030f06e15825400350240d079103010000e01c01a502c0b80290340c0c0e113429140d45d24211122144d001c42c0102800584801c0001c0301030001105c00340c1c07000140230407000741c0d110a0010a0780440a600f0340b440003044d27400c00010b5861580041c50103138403c54001d51a20210703424141c03541541c02031480801055500c980c030713010401408240410507460080c002698101e00010503600740b90031806007600051460201040c0c54403102e0f0540d2040a043c0380080050b81490200c54008d402c44109032810703406008005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 427431879 1250 427430629 427430639
    0x18030a021c02061614040f0608040308060301050615070c05030f210403020a051908030c030408010515092202060a03090201121514060c01050124020f15150306041506 73
    0x20500510440c1c1c00c0703254501c04151a88100c60b01c0c1101961858140011b020114002c211060103d0281086403205400c43c201800e0152140c80014000c91203a0305001c1046a41d441d2411002c030042203001666131281c000745003045000403030381c015a82600c2850f0310000782d2a40050009030002040c0c00c02001e8142c4500c000705503100d40e0002039044108140100300500303081c10010507407800540d401d8051a29001d40c9400c59009001c445002e61001c80c081c41140404e01c221031300000b10000c03100c080c54000d404100ea81000800403810020448009501c2e40c11020504e801c003a401420308da81d03103802410280050200e50016400101109030003509041507100c1c441c3c03c1401401c0c5812a146844a00400300030200031840d00120107110b560076204090140314081c00d15422034881240755190401314081c05c00100208643c085041032410290100301c6004a03047c1c83e104034525036601c16210f03a00052103c44c0d030703050720820701040b003071109080b405201c80003100320038040d450390350b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 427433129 1250 427431879 427431883
    0x30d0e03040510021603380a0e011b0305060d050d0507200a17190501060503010b01052128240b090d0311190b060108010608060918030a021c02 63
    0x982c801d481a0700c10071050000c11a050300341000303003518040c103602030340f804004140080064644520340400f0340c4107000d40c140b030902030034030001027680003001988071060781340d0f03411013107802c448003407556910204030941c84500f14000c6641d001003c64030f040b004190010443d030b1251130180c0318200074400801401418421408504000521070554075080401b40c1e44c001c0e1043c00d0303074402c51060307054607901c8404c48007449074031a010b08000182140340001b810b09540f402c054050400008220b4451130190301e5034040e201082034000c8500654079003601058074106602807045a400c103040c600c44841c3e49030445000a40500070b564225062003680e50120941e034041c5070096003040c030450f1807904181803600e03000b50207071400b2003442c54564140c40c10102440351600e45a41403400300300900031181c909607003210307007844c0c03108003076242000040150078058001e078030800510003c550182c01c0440841d044620f001c055a903554039500c4081c0d0307504c021071070307252803054100141c01c00c0703c1c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 427434379 1250 427433129 427433143
    0xa090905060306042d0606050301050903030c0412080702060f130b040501050f0f090607080d0513020f1c02060a030e070e2502030d0614011206140d05030d0e0304051002 74
    0x3010b4010001900c0f03565804600b80c8818032070340e801e10724200d4001e812070594403058010030300801e00090481d0424007030500b036034001403662036264402c00c03c2c422111b40d040125400c0b16891002240000080d20302300486103d8024003030741c0110003060141e11640340800500c481195130000000c0c407603440c0360ba40203600544c130075180842c805000016500c070200300204070301c50442c10b02e0340c64600102d001070080d8006030703415136001e8000b00f80710306d942041d40306464004940304c001c00000350051b80082d401c95051803115021b2a400c2c43c0300e1460700d400c168410740c1d1560042a554940384541e0000340100403006000500f4071481c1d6000820b00d0190110b03d0040c40f0071945050400801c19109004403d44020003085100801844c150314665208840c041c11641003442c1116020000040020320b6240003d03a440d45001c8040200707100a003c5007480400c281d61402081c0082d0a0050450181c051404005400c0803011114880b0200041c025648225000030031403c41c240102d030390303401c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 427435629 1250 427434379 427434391
    0xd030902090c09190f0f0e0c0f180d050c03070e090303040201030b010c0b040605072021070209180d0c11130e1f0e0109020d080d0e030f0a090905 64
    0x1ca10007250b01d20310640010580c0300307000707003114003a0070b44c51180e04400060b6070b0141d90200b610701002c3c0041300c0c5007038092006048410801e085802e00346030068540c1b045013009100c800700041c5040e000e4903081c0f42420251002000c51182d640f240c2030440e1900000126244a401600b00c00325602c3e208510036809840f22000450071030b03589a0055000705a20f00b1014140300f00030325840c0008585050840c032070751040001241506000401402654581c0040403032a0381482e100280c0d0000054a058000000403610403030107460088403417288241c540103908010304504100641428030302c14850030401500315094000844c408555074920b00740000c0076081c1c810000c0c801482d0510440d0402c000c03003800015400004680145040d5040991620381c20311464408070a500b148100d40c825810300009100c455815400100c40850700c51009141d4103010803074080d81e41e20356105901e080001011a55a410b40184000d1189c001d440400300054620074080b420000a016441c0541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 427436879 1250 427435629 427435639
    0x9061a010c17071a1014121f0b040c020105150402090904060b040f05091b040e0309010809100501060503041707020d0b07030b040614090f010609061b020604030809030d030902 77
    0x24261444140c440d80f0120003914900707a9054500d04102007100300368007455a860300e044d0414584503459440002c0780c03160502c200c030304107840d4074480c00100b40702d402c0503006080a4032449521240340c00074104090015041807030304400d10381282d01540018080d003482c1c14074042d901503203000c0000781e228007406a50041a0580401c0c001102608070b0701000390b0050000c034100e22561035402c01c4940031601010b00ea03002c2c02c1c12483c4054140c2800c800250706079400e100740c0090508450f41c034804d82d0b041c5410041c0407000202688011b01c40d115041040d00e202740220f580d125401003645c0c1003a107098444290300301d0004c43c54401c0b241200c3c005c0364007404030711650318252500e8013400401003a0f0300c185515035042c1c400c0c84d640c0307104480140c4070901c55280c8201880c001e002800310000c00c4200c4400c007490040c81035503081186801110002e00c1d0a440c0040300744100142465000f4009400140204000c0104400355001c0c280d426016801c4843d03510b10b1010403003d9805020010b034101d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 427438129 1250 427436879 427436903
    0xe011104061103070f080904050a050702031603020a230607020f060a050421030203150a081203100b0414010e010c0c050913020603040f14060705042709061a010c 71
    0x803402003090b501c08505880a0760f042c03881e15210b0083e100e40341d60f01107a01c000001000c85a038030781481850340122348490100301c0d41c9800320001c0d50300d104c0d5200700340c501407202c0208405c061080101c684000da003e000c1c040000c0c0480050301040440468624060180400098015100080303d21110070341074002e0406481e140d8074a40100f0000d081525a1180140c0302207103680c545035a20310b88605aa00145d9a180c102c0e159100001d49603504c0344a0341c1460740801c24003c0026501554200300c014072540c94a9804a130250440f09501c030000458011500080c404408099101d1102e07080e03c0e0108010700d400300448091050000051108550000a0185003001c80901d42e101c050300c0b500e10300c4116540c0005a107038108440071a842403020310000b0820081c03c410010488501c0e004243d035040c101c4018100c0d00540c050242004210360310281079804004c0710600c0045803800c20442840315080402c05015150b4000300000a00c2001c0009944202c889460294104100c0012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 427439379 1250 427438129 427438139
    0x30b0a2909060708120f09030f04062a0f020f010e0a0509130506090d120c050a080c040b12060a090902030615030c04051504052a0c030415080f0709050d0f0606031e05010e011104 78
    0x180533101002c4100c008840c485624410b1901c0c074040b40d10f018080e200c442407080e104104860100440190400030408003011441c2c07035203400d1070141e40c401c451201c40c541d148c1c0300407242a155031070302421a1090b24141700c0401d90120f10080445a01e030744050600300c1c095584d4058405c515880c0300080c000700640b5003410310a1144a4205000c150400d00e03165031110503402c0c540142d50740070041c0c4607440601a10346000096080102080b0380103006101c96500000d8940038010160184124000420340300c40c0d03014415002c1e8000003c0082000342040041c5c1c14815041e01d003402c1c051450000032401e0241c03100d4170b007a0038081e80c05510140f078031410410809500081d04d024103074801030001082040c05500c41d58403600150303444854500d025540920000030260810003400700840c0e007844640c031f80e03820400c0720940040800c001032090b850004010071281c0d00240030900c00d40361107003601c0724034404d1400c45401000240205a4100241400c0b510340210002b1118420001004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 427440629 1250 427439379 427439387
    0x311060a0f0828020a090f0806010302010f170709181a0d080f0408030703090b090d060534172a040e07030b0a2909060708120f09030f0406 61
    0x90300c20152585a9000090140c40804683c1400c180d0120190045420400341e544010507000038004014083c000c9403410440302e44a0302d041c000a410170192003200035099004040b0b44503840740b5a111031900f894a44801080b032410307400349038044022100001b0702d000c20b5004844408401255003609030501204108070002c100e00700b15100365080c0031f407c8290310742c08003510050611001560381e84095150040008526800030b04c00d4440c2800203440d103407204034440c458594080000181e03a2524140807401603030500c22103074414a20690b0714040b0030401c4819407508456205d182c190039072420030508600c021260250748951522507800340b081454411441810004500b500e003035103920008450440848200c00482c2d1981401c0020341002468000140038a2141c3e04006240f1008810700448181c04001c0f51140480c041a990341d400040b50300c5240c0c404c200560303900890440080110046619a040310188800520a100c0200032038100004005000e454107042220a031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 427441879 1250 427440629 427440631
    0x406030912080f22080d0902011107180c1101050a360b0c220303020607030203090615041b0306050906090402010f110717010e0f031306030506030c04060f0311060a0f08 74
    0x420404449000c0f013001c034642c80300421101ca000b050104207a03080d80005000c50020488801d15603020007000c1000c1c2c11107100c40d00f2071307035a86040842c05000081e4115140715501d45001803079441d03c030a220321020954444203009035120103000012030500000da0154802010781070b6548000301c02e60001610320b0802e140c0c4603c002581c0f900341041031185074030301d00310b000d1a00c0d481c02c610f030000d20034150108142548005079103000d5285180c012401900d0b4103000e099114607203200001c40c000b607aa01c2e000118212190f182640190076660310085c080c190a11030385010310740c080e01007001400e040011034407458040c0c445100d4038185030310454400101d180c40125900030b07034002141c41202c002c0b0000b0141d522100108101000d14000782c20460311a2900305141d02c10041500c024402143d00421200e40d070400041c282c2c0c0c0d03d000310f82011606405158002e1400350041140f207214600e10050300c0c011204ca0b4000c0240d9001e1113274034440c0180c480c010039905030480920381d114101031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 427443129 1250 427441879 427441921
    0xd050f1501141c06060224041709032e0b100e0915031c030b010207052d04090c06080109050121050f0a052a0607030e12030406030912080f 61
    0x50042c25039500030960845a04c0c5c2c00c50070058114000483c0960305082080e42d04d070241401108080c11300e0340d6640d42c401c1446d000744244d428045190f10199500380091100f118400c00d80d00314079605c540c008540540005000c010b460b140c100440380c14240305507800301c20a03154984c11a0010380074200315070300300d004010a191080301c2c2e000345401c1d10309100d03503183c2d000050281001e2104100019080e00e07445c0c03101c6411980f00150030403090b43e822a00c040e4035415401c5001e805c40f0300400f44075140b181c0500240d08079082200c0f84040113003194010701201c40303e9444001503600c0c0d00ca0310b0140c450030b00c60208c07044041800c01072070b0340e40d824002603414810400c075482c00c2c4a0002c206d00301850b85000b0f50b0b054211540f42c06680303413840303441d00f10210940482840c0305600800a02c0d00c0c0100240901040110307410f00d03030030f9100d42c10f000580c200c5e61000c0f20f80301c655501c07005000e4000031030300f261600c4000d20f83d140030501a000301c5000d0812888509600d954407a11960000341107a40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 427444379 1250 427443129 427443157
    0x9050a23091b0c0102120c03060f0105030603010905070b030108060708130816152403020915030703021807030b22050c21040c2709080f0d050f150114 66
    0x541c8007401d0b0850020100c403c00d040002d0307101c515081c94922a51801070a400c40b2440070010002943d031b9000141c003107554242049610786e106d03040800c0c010207a07013900400c00d03c10504c0120303210303510002544c12104108121429681c4110317080340c9112082d116201e038945180007000001d007020307026202c0c9800310040d41d81070041648550710301d1003040140544403682d500c5032548000241101b0b01c00e901180840e00000c5146a01140e00d20f20000c0031129403c0051804900580d010f100240080d900241109038a440c01040c0103100d18064500401007403601c10031803080d0804e0759000c061898410300da41c482302a1507824402400c0006d00002e00440100112100842506803246d1241441d0030306441901c1c0501d00300b900416240c0102c000309100c1031015a40300901c03102d0410701c400407500401c140c4102d1411500d01e0191400c0703e55a00d00206101508251984c00684036036000032100b005078541100c0d0034909800d00c0c0307420380000c980c180c0399600708d0401c030004e0082c2420480c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 427445629 1250 427444379 427444411
    0x90103021201061d090105010e0f0310090318080106031e11090106031e02040b190314040609050c010c0803070f090807150f050418091406010609050a2309 68
    0x14a01d89a40300c260040b43c08900c0749a1406602001c0c2c06000d0706056007070300c602c00070354180000a4850581851041d00c552401ca4604c40c01e6207013807000200d5190030000900140b0000d1a01414000c03581840c0d104002c80b01500045501050240740304403504000016511503401e1541009169446001c0e00c0921b00e182c00c1e10440e031603002640d4001c201c103540c001880312a0141910400c840544901d8095005110a11541c2c00c03000445206140016460b661411015000c2d0054a1017891065464840d10204024084103400ca880d03400d21401c140d90480380b03240d00642d1a60707180e1401424070700c010f0001a6015005024084141c5901e08040d04030aa0b103c45083c46d02d25260000e1440d90300c44007011521a4010742e0256403000c05091541c2402e04140c0c610b40368516024002c0e021a4a0304d41c404248508110f5000c0d011900e00f056035819a151500900320440c14825540144c102500c00212181409208401e02c450003010748040d00c400803c102160801a0041e8010b0040320 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 427446879 1250 427445629 427445647
    0x501020909010e0118060b0f0a1e050d060e160e2b030801060f0c0803060406122d021c0305090306041203060605040b09011409120318121209010302 65
    0x601c0d4001c0c2541142d848096042040d45034484224000f100b091505069040c0050190300d01603072002c0107044685511102050320444e4030319402e0105810000d11800d13040c80384c646c410010a40003100386014051565603070a804440d10003240d040407803002603142d4580e4103104008141843c407000300b015508013070160b40307801c418482e10700100115035041c905004158010000318010242070600410444140501030314120745000300900095000000601503a6241c0c4007402901d45000f04111945652808a41c00c2d1711400b01d10340c00918044040706e0078854906c48403501d0b5409480d07d961400004544625074017030020481c1400405c0c40814100d46042098038811401074a403244400340035003024046a2040c0c00050400a081105100a600500440e0b082240030701c0c141303050407000715611006000d10300c100307580918602441c0403814400005410882c000322001d405a016003c00c114155002c481209000d82240c843c0b5110084014050250a44181130251a0401d94 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 427448129 1250 427446879 427446889
    0x106151b050106170c2b060908160809120d09091d011e05060102210a020703050f0d080c0403020d02061804020406110f1b19030605010308071505041106030405010209 73
    0x100c0003644440d880111005e8080c0b44c05018042c0c2000c83c40a5401085040f041c084480b0041c1c64018065a13214070541041003a9035044400744c1c00101d07030110903010989080f08641e408415075500c1a0010fa00b54035100d0300200e01c0c0c3c100380b0040c0d00c0b18407002c1e160400406c058046855000900011801d410000d400203010301010382e11906040785510300401404012500c2c040d01d81411903220b03482c240d0400250980f10080405041c082c2521403200a404a150110a40000b48a030103030200320944181c00003000056a05c0c140c9600b0161368601c01c44101038082c074400a0740c01640070741442d001d410814010b100c07468903000038060340d10b040f00108042ea403096100c400011840f1000b1854000305102d084a200c5048000d0b15908001c400d5078940340140121030b40c4940740401250303181d0383c0c00742081c2d001140e01250038840c42da5a400c102c00e89411100c4181e070120078141c3d064102000341d03c1f40701d129651080c0d54203104240d160a01000d904000c6c011140e940d0b0800622550b6510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 427449379 1250 427448129 427448159
    0xe130c0212160b07030225051e0f0c030a0f0b060d060207050606090a140105040c1101050901020c010b03070b0a20031218030a0e1c0803070c050106151b050106 70
    0x2ca5690301c140030704615000780300b154020001400c0510502004d4100e60460614003d420a6030042d095a2910340c148182421031807440403801d204106002105820003041c0d110103010524182d0390501400c009264540c401c440c03008195100c080c04600000d0400e0921941144002d05180034040d1107a0700c2e80c0403071344003480998060f4080d01c200302ca9450034213100369010720800700500030034803010000c00440310180640d0348a10b449803901d25034035104901e03610b40e119680b0003d03c09070424404450017540072071507240d00c40d4203150802406080004200045a0505001602d00b1300144000c0702c0d81203440c0c000104100c402480c0300030082d010800f4281f440c0d501008940030303007032020485003082c115082642e0140c2003803043c4207500390004d401034074440055590f44440b4081c60340100796124810390003000000f01001303000590747c2c05500516424447d40080268588500c6542c0c1031202c01d140980008050080344940b503c00701345000d141500c540d0002c20010340b40d0f0f04c1042d120320 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 427450629 1250 427449379 427449397
    0x130e0408070b01060912020d0213020a1d19090509010912050d150b09010c050c09010305061501021506100309081602180c090111030403020a06090303030c0e130c0212 73
    0x41001d0041c0030b401080c260050013542480c400c220b1030001001501190b20700c010f480389030301c00c180f030f0159191030a840500c6003450740215030381d2500c1d4201926203400e40f164440c040c0303c070084010032424400350b1a54080141d1900340591403602c0a40b6000d020001e150100d69500c41c000e01001603060030358041d1002064803501d488880038688142140c200c0c0c500c04d40180703e03d0710100082481c803011903000c203100707280030401c5100c83d04002c0e290100211255800a000d14000420322030003258003030084110006c10034892144a0049079100c08042401623241c0358400460083e03d4000416150407840703050208085d07500d5103581c0b000d50081d55960211038410352440c02145014844400705400500d96540941000321b614489400388075070403410300c05103442845c0306c03000030400d6074000c40d4000d25030000c941d02c80c400101660781c98401280842d0924013100364007405a6002344401c80050f058941416003c0b0806001c0e10301c0f503501000b58000d400f0b184139190118001082040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 427451879 1250 427450629 427450643
    0x6030203032a0a02010905040b1c0605041205090901060804150606030c030b22090309080304030c06030c0f020d1407060e2104140103050a0b0915010801060320130e04 73
    0x900d00a062562800d00d00b0310a0003a0008404080140e82001800064500960300054230042e814041001c010180b04440300d03400011102204000031500080d1103a0300c9181da50400f241a00000d980c1400340c1d19000d03520803450401440300d14480c1c4a4594070178010701c0c0044103122855561001c55102d038000c040000d03141c9000c0b82580ba058091074000b8503054804101044000f050707500c3d4680038520901400ea240c071081024188540d4100d40a00b1203801983d61f560341d24a008070000c00c82d4810741c40071a007445c10b12000310340241d40380c0200501d00c0d00608025200e012040310800b00c00030104002031002c2c007001001c01e55a12425075900398083c010032000c90700d105601105041508010300b008410417040c8046a500320389141050001e00b80072171140c0710100541c0140990082064100c2d1158040050b8442c6400d401c1301c111400b0b0301e4110a80c0d0300d0384000c800350740720040e102d00c04540c00524078583c020402d00a164603420701000e640120f40340c84480c03281a00945080d1506 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 427453129 1250 427451879 427451917
    0x4090c031205071a07030b12060406050f0c07060b01120c1106010f080706030c1b050c04060b0c030403230a0c0f141003240f17030705031c0603020303 66
    0x3030007080040303909802c0c1030660510316555514041082c00d011119120403814000ca11483d0281d042001400c40003000600b040900007282590740c3c030203c0742920071505000214000c01460f8424900814000c00340c540307040056281c00700a00180c060407410084005104480144248200c1c02040309075aaa990003601605050749070800c1138000502c110010102080951400030381101202d07594200401c50340c02c070003400e03125a20540d40c0305d04860380190250080000c0800c3c900681d000481d000c001550b194501d0407054021420001000c0d4400c000500220311403000218010890360050b0a044880f4020346090400c07014007112690442d581c00c1c4200c41200c0002c8011b402d03036440e0780d15141515400200c2d660300541c0c240b014140c0d41e03e00c1e0101032140c40c00080e0401101e140301141c4c3d55481e1310442c082e0340d852144c0c03442030b801503c0e40b00000c82e0210442d0a00b5030480011804d0403d002406a090300803070011901655945c03c001005880500291001d050030030310b0344c1c0744 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 427454379 1250 427453129 427453133
    0x1050114070512032715010e19060b0a020607030903050a0e0609040e06250c12110708031c0e030a110a0606080a02090105010f02120d110c010b0f030d0912080904090c03 74
    0x1917400303140c03030192036500204c4070b040200c3c00c80c0c5c0700f80341181d96091964000c3e0722602241c0e0801d26a502c000c50980f030401201080b5170900d0701c01400400d50035030848090303944140084049500000700200015000c02201c0400c034841c010700600c600c4010825443c000446c00064121941031081d80d20301d820400400500e04c001840303649001d041c02805450b8a02d0802005150078a0000c0080540110084085400c0c1c0f00701070517003c80100400300e0388a03d4803414029541c0c0c102082402101030034961030399481d40e050242090300100d02009604160200301c05880001c5c0906a41d0940e100710f003103210101c0e100d80070b581c00524000002e805452810700511218a505801c20380c107000c5112621500680d001654061144008140b151207400d0407050741c0240c00701c0510000b80c5000442c00209200040d805440806002c135880d4035904001414140c503011140540310104000110802c1081c0300c040d23100b90124824117800f03252516840000e07049031403c100694100605681c2482 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 427455629 1250 427454379 427454431
    0xd231006080106050d051005070e0d030801030507050312090d02030f070e10050f0108070f0323010503010f0c12090203070b070f1106042d38030105011407051203 71
    0x201601040e9036001c85d00185032111952111403520000310141d039040000d18141c400c40000c480548001c25841c01d92446040c001c1c5441c10a0005035007500a40d200042d6601c6e00040641071078803140002414a042c0c242005051040c0a00031b076018007500c0b20f102646e1205001d0000544030050340f00b129400c10201c94440310f80242c104a000d40c04c2c440c41c0d030340b1a03a040300d0700c25803001c8a80b400030b0385404480001c41c0900316502820041200072401040e5001648501c1d6040c4c1d08103600030030046c400086800240c598504010000c0340d8101c000512109540e081820044c0c0060220742c000c41d910315100c10568002d03802034600740790a1a903881000a543c01c07420820000311000e0b400c090404044141c2d000e0070540480980071101d00e04c4000001828800000b4031407803001c0d00614156246e1200c07400b44000700c0c00c0c0041e800303041c056101c601441c156810b80304103942d800d0301d0319000c0140c0c0c0d20300e6101100548580c8541e605c82c1c00b400741580c008500c5080b003910000765000012028003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 427456879 1250 427455629 427455641
    0x60e061b0703050d15080316030311030403081801061e06120b06032206020a110613030c0201080c12090c01090906050f062d18030c0d2310060801 64
    0x800c200c004008010220f0b41c800103994031456013900000f00081003641d2042202001e510807540d5000104101810b00a142d0480501c14040d8800380000e00003848d01300c1091000703c90080200c1c04074004078054110f810f0158415103640d17030001a80c591158840c280310341c0400d809580c1c091345410240105580003807200e102861207070b828000c440c101070001d80c550100812010040801c0c2f40388000322004000c1d42030134141c220600710350341d0b504072900800b00712402401d0201880340340701050380c11031020090b02185030140e49204003052940e0044641e02c8024101c0d1040c41d105100703da072041040d6018a014400c03c0c4001d0803204814000584500499030048560354500101000561500400c41201c132004072600c86c1e591a00708807288108540701c8010350308402040040e41c0c130829000042121030070741d85000010b05043c84c20907903505e070721421440c0c1140c0c4000f65000090b4141c001c403110103254a19100c10803500f5011545803c9a88040b03502c03642d1200420003201600b84944 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 427458129 1250 427456879 427456921
    0xa0216052e05041a0c0f030a090c0f080a080f04210209090c0904020f03070b03310206091e06070b0a0507050f041202010315030b09070503010209030703020f0d060e06 73
    0x1d1016140644820200702119803210b002c00c0076802c00030f032113802c05d0421a0b40c441d075a5611a40c40b401c040f161135000700050042107660380310f06100411202c0c0301d041c5410440c3d022800524038041c1070303a2601c00541107100c40e0719030f0704420320000c15181404880c1240503c041080380042d806140100705c100d2101070200e0610781c00c68840341d4a81d8680e04111313641700b0340580e4003a1100c1c0303440000c685061000d9109500c020008400d10070b4030081160305a0f80207a010019010b0305c42e0321a450300020364000300096100300c080108012a00b065050044284011601000b1000315200400c0440e40112001c40711041c08a040000a018a11034030f40c02c6004c51801c9400d01c450020862843e00c1540500d18540001582d024116840780d0000204801130351250001c0d10b03901d1812105020003943c0080c6640a4844080307020304051007a640e030382c00700034001c1070250700d160240310030344c00f40705805a044445820014045512805810103403440a0b00400403442c0110405042203800317112 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 427459379 1250 427458129 427458131
    0x4050a02011d010c1403041d0a11030f040f0213050711060a06060207050114090307260c130f02070605070206060102070f05010507080d0207020a0303020304051503010308030a0216052e 81
    0x1d107003040c1d80c03044c40088040e9100d0081c03007141c240254202e02e180641d0388845c500162983c541010752212a8050340100740007a003c0c0180b14688064400a0008480da01d140d02004030000b800300d0040420201d215002900880440d120166440180c0f241101d0880c08545944503403c4800340c20491940e000c00448010041242002402500c0d540b03940300b56410030404000070080302c1d401c101101c0001c0c0c1c0060032105026a22150b0103100f103440090f0040c041465401c00040e118046454103038210700500e0041582c0035083c82c0c0c8000d0030706901240340c09500340700301000282c45200322402845507400a107114904680020b10304440c54000d41040030a1840410641c4d0f00103040d100d20640c41a581c90701d40324405a541c009000f00f0001a42c40034500c1800024550040010300540ea02030f40c07209036400104a028031503200c280300042c80104100006507074003005901400e01d01c50842d4102d8440c0006803a4945842c4090440303110303150b180803840c201051a82d110840140301c200c0c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 427460629 1250 427459379 427459427
    0x702061f08030d0b12060403120e03030609070f0909110304050705010c0b04150e0a0b01030606060302040f0b131815050418021e06070c0503060606070c09021303080304050a0201 78
    0x1254035143c0c02201109100c8a8a070002e03c20103a4902c141200210032440c106c5820345080c2c01c00505040c28000201308240ca4609001e00580b00401264482c50002e03001f089140c94041c812900d00d10450402e00410203000710201e40242c05001d400e0400c8511045680c403801c0c68107009080142581c092070603c420303598a800001d01201660354060b401400b56000b08038061103042c0030340b00401c083c50f0240543e020030020808076034000e41c16a409a20208041d580b508003c0c0c0c12481140106400d80301090b40811203075801c40000d122107005c0c100034546007540c40c090002100d02030310f8420582a2682013a044105580f10f40030001d080441d0140405030010170302c10481001041d010740034803c00e18000390030f8094100c10b490016000303800c19554010601b0140c4604059019852203401508007007802440d00310706a8079070b103801c005085151841e0140c05c0e8001d43c0b003401d0001c240094a1800000b040260021b03500c261702030000362900003098030004080d4484500c00016801c507400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 427461879 1250 427460629 427460639
    0x510020109030f1412040609051006081009170f0421111306150f0816080c0307030908040b120a0504050c0f040f020d0606080c0403030e0609010c0b0702061f 69
    0xc402d0701d10f040c80c00e0612429440010300d41c002940300f1480d1110713604120328240000c000c00d5034451003a80d03001f00241c0702840d03540d00d07820098a0702031050900303507445441000c543c100c40f40e10401c08248501038540700c00840b901000344607004410360003190700010804100c4c26203180d00e04152056868502c201c42c20281c0d441041c00c10282044034000d0480d030032444024030440d031015014002100d01c1403a242110000103014400c0000780c2170001c0c49501c0031802e0301c01d0f011307070300c41058901c0d40780c0c10b000c0ea85d45014011039400042c01901095104c4d1111008507441800820103040304200040da14404800c00c80000a805407484d45410718184c00c000204001140c000d61f80401110585038000580001401a10341810f40c039071940d10010300c0b113802e0341041c2d010f442280c105403188003a03983ca4068203c0107015911001e07001c51300d000058003261921390024030740f0180c1410f04070340345009a1030721443c0c1441181c501c0d015034070403c00c4c0414044034a01902c0707003085039054030303025900301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 427463129 1250 427461879 427461887
    0x20d110607270306020d1a03060403050309070b0301150f180b0a050724060b0315090601090b0304031d0f011706060c16050405102702130b04051002010903 68
    0x206944100034000704441070380c440001560b0003032190303000200d85094403400c2035002540401d0079540a549800e0340e6003405044800c1d4981c00800c000c020701b015680b1500c2c1550264402020401e031070040840104400d10030001450103064040c8025852503083c02000e8648065000f00205012900c803206104640c03a0f0742c50001d54040044040c0c648070020f201796168000d15000401521007140000c40351501009200581204000180300c00c1791341b102c0c110000e2005a45044901004001d400740c1814030b41d00c8980c0102d070614014080965a40141d4180e4200303480890000750100b2600c45420482c1c64520340c2e00d801214580b00d440d0700030001a01d034100103900040303030030008000940030f617813078000f07841c1c0c00740707105042d91000703514508200c66400c2540121031046103458045424032517040c0320301059890b0302024078555035001140542c84c065001c204414140c08009141c2e80f19004034032907008004c030118060701c56043c10708100b15181544031840440e890b00c68030001282d80 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 427464379 1250 427463129 427463131
    0x30209040b061e0907180b0c01020c0d0504030c0e1b07080309070e010f09110d0e0609100605090c090d08040906050f060c1c12020334050301050f0117040b07020d1106 73
    0x10500f041400e104040d1b07070000300000640d03c101c0f01c100012685c014080d0040d0020801d40340080d081e10044081150b054070360f4051404040d0000546000c1032140d5244002d10315000f40f502401c0340744100c803003010034449a00164044805030008818031081c0a01004124040c3c0041c860a030a0340d81410007101c041d601c54829540995195070038a42c98a100d041103603000c8041d0310f0180000207240703102a640321001e50303041c0750310f1140f401c050075101e22074450369007a118003d00300b81311611510101c01060300311081c0b903a405501e04070309400181c9040000d20080859000225100d45800100400d400440000d42e0094508100054440702d000c200c0c4c042c5881442c203880c0b101c00d84614103c1d10b403808500c0180426100000380460300303040a4083c03c0c151415000f100f4603e2000001c00203440c0c2c1111080080f030401c2c001030120345071064280802d0b68040c5000020100540b04e0380001c41002c0d50300342c0351103d80304c003440f8030607034140b2407000d1104c983d06161a08006400f8402d40d1040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 427465629 1250 427464379 427464391
    0x603060f010c050304060206090613050a06050c0d0504061b050309030a080c07080a0302090901080109030c02010f05131517091504060e060a240b0706050a06030209040b061e09 77
    0x3900d66104000da8002d0401d9050141c0040807652216103d81c1e01079603440003030300e02c4050351040344000b500c0ca9000d0404141102d80c0100070300a41111a034544003c1c1202401500d1306c3e0800303000302141c50385d85100d050f03c628014100806ea02010003004456806886525010054200704201b6a964000102c0751f2103082494401425903031140064206e010f0307100000d000352800510f4030f007d19459005071429400840380e20b4120b1b6a1408001d003258400c0d60001e0104a520305460003540c01109070b20b4020341c0c6810403520340b0444075002c580110454222a81e03448009502d450010340c019210708040c00450b016000d036040450300f040c2e89110754130008240c0c4d20311000150402c00c00385c10807580d103500c800459045081800400c030290000c2c9040c0480c5c030340e440c7c14035010300105500d40e000f02d8841108051031f1042a490355000381000030009a4000d8030743c00000300581303c02d41c0d00c078400d50160a2820b40c1342040c07806c00843d02c41c907101162000c1c0a01c82840c000d0b80e207400d01d69804c10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 427466879 1250 427465629 427465639
    0x30908070518061c080307030b0a03051e1009030c050c010305010b040e07020a080d0c0806010201020a0f0503090c03060424020a0f0e030f0111091203040f0b07030318080403060e01050402060306 85
    0x79072004000f070501c501c041e2013940351800d80003502d020810070704082d40c0514540d890074090010184240050a0002c0c031010f4480e60000f0f01c4550404c5984404000d45c812040030346401102c88250402950000d8000b18005211000301006000046c01284814202481c05000c1545040c207070f9981805240203005da11543e040206094500801202d0500c80d4071181b0591a80e8a40007060003e00c0710404680c041404180020215032040c4201c50b40b010343c80e00c3d025000c03441c20204481c035030001851781005200d0407120882e150390402803184901e04c15000c4040c5a600c03009111000b00c56400301c45012401404184055604110341901c0c070b04091a204c00c000f403000d000030f490b09038442034020943d440c0c1800701c61402c603540000c1003485820303a0401c481c0c540010000c0d41d00d101d21304c03400303203500072211080c001c02c0591002429500c1c0a03103000300d1401a060b8030840d9000e8048021204141d000400f00104070550048810484d9020020052458150045100d600c0010305151042d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 427468129 1250 427466879 427466881
    0x907020a152a18241416050a050f060711010c08010b090d06050c0406030e0a0c12030c14031b0c0f040e01150308030a1b020304030206070804090e0a030908070518 71
    0x41c4900b0344150850040d003a4960300c540d4413a010f08020144c0c003e10070390300e842141203201c40c500604801c003d5150003504245040c0c1800402c011b000c1c8120012241030090030300c5680422800c008e40601010745201070400d0b400e06c904003403e40250170380f2035031a41e410010030840d07103074100250310304440210440300d503200392040c0011040002445e000745814641000c2c00018418a0003810944140d91001c00094a034003510350398544000c1c000030140c5403035040a10003522901400c0c415544a81006400ea030002e03620009000380340d090341d071034950000c03c050004ca0002d00c800001d14640601601040080b040850104c02e1040c9005006a0b02c5002c08142e112095203c8243e606410f2441c9404a449142182441d8000d0340d40c0385c42c1c10b0401c01e03040b01c800c030310240710302c9218501d400842c501851a0f081c4102c6801000e000e690030036050200050000403402030500d8180c0c020301400018069280140604200350802840703944940401e00298640c1c110b10708104011800031849 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 427469379 1250 427468129 427468211
    0x4150506040f0212041e17162307091a010e030f19021203031306050a1508030307080106050a02030a18030c0e15031b01110a020907020a15 61
    0x38088108556124501c000b0b810140ca550b100c11843c01940b04840c0c80c80a030602224a00003024000000ba00104800100000d05030810002344030000d0366000c50910340e1415103a0109031040031007807108804c103900000000e107509010420280c42c07070803020088810300e00651115030507030851032414044441c00e00c00040c6c0c1e081010b0705803294003070100c1ea0481c4100034000c030130840d101e4040380a804810030402d201503010043c3c0c1c1c411095a401300308640080c1d259403010703000c0600668a02030f92074040d002c5412050509102404808004590724205504010050b00d4140c1c040410800e050140c0f0005503804002c03545203140901d41050382541c07004207800c01da1505e40c4000c1c00314214a0002405192110103903224041e010100c41c2075a011720185916451101d007040a8503035a59400c040380c2d0b0295100c83c40e004280001c40e212685c3e19030210302c0c0440d00383c0e9140d01507130003d0704450030011143c040ca040b0030315855060004029074003200f003080340000340e0484102d114a103801c034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 427470629 1250 427469379 427469381
    0x507050a1811071218051513050312070312020c030304120807020c0a0501050904061509030302070e01180f23060a17120307050f160b07230c0309040e0f0c01080415050604 75
    0x84c20303000304014103205124214a085a000c0c0707102c030241c0c2020348400030f110301c1d00bc82c801c00e440d04640d030700038a81025a54201c1d03120218502c0500e51640c2448001c01048003013006d10721491260094038030000e1501c1e000382c00717004000e15000c11075010024044003900c0e1280840101e403c2030070050784820240c40041c1c081c011036041182c1260f5046803822a8039402603010045078001c4c1c0036260500c1e2034030f1012080c02800d0003100d01001c400002d00d41c030150141e00040241201544c00200c1540700748112951082d1a0141545da11103903060002502e880d04a140080008611003040c1414010780c0c143c80300300d4a650001010004400100c94a01132400c5845000812a4030390356145062802541c8078004101640c081d2101c2c000112114005c0d03006a2001940140d1522502491021400c0a60280249440c10300082c8075201407900c07113001d0114202509005420703150222a44680f40000c2018081c2c100a46a4144004100f4001c02841201c103c0c100200da2a503070000460 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 427471879 1250 427470629 427470677
    0x5090609042607020315160504060207230402030f1807060207030809030a0f0302030309070f290f0d1e050f07030507030b0907021014090c04090507050a18110712 71
    0x41c0d007600501d010480f802e100c03030409038402c41c4647c09102c820340184000316014003840c028040940d00c00c510a00c0300d0580103505071801c00300800c041c3c03051000440810240c0c0c00503500d094035518104140035205030060350160040d0850401041c180b8600340f8020f507111054440909162000140c41c0d009441c00c0c0205070445400030502401301032680340007560b9a104403501c2ca101d0046400c08640c0560b460204800c40354042c0c8014800009080c2184050548815081c580c5400300101e0340c100c0350004c05070003407644032403000070007800883e60700705220310290b810b203036a608d00020040c07091172481c0d0302c43e0450914500081c07140c0d80c081054001f0924003c24950000040040240300342d8000b41c4412000c401b480148562114408c4001883d1070a40e00c40f102500108414000b500f400d501c04041d01d40154101d8100700c2d034540c04100c1917442c4e60805c0c1c4a01440c0c3c9424005403e8070302810740b03003521128016240c0305185e200c1100001d044003000c002c0119408088001034001d0380d0702c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 427473129 1250 427471879 427471883
    0x1404060806010b030a0b011b020603071107080109170702010c082512030c020f07090c1b0f021e0d0b060d060e0f01060b0c15270705090609042607 64
    0x110129610f459129096410071915100d00c00c1c1024803070700300d40d4807038107132000414140550524005581c9e8204145900010601000c000b02a01b10341e0382100c040141e18014406400000344143e06402d014005088035542c40c500030038108410300c0181d90180348242c0b51a00244641c0d26075511030705045103420340c20b1800300b00843d49001c136001d000e00b1900c40f8100444a44007000500d03074416040c0d0b1500741d0000c0e1007210f900010000c200507031198011410203042883c103200300d4440341d0410340350740380a854192074140700c00101c0402c50070400c4503003d5210702c101c4034242c0707460030714002803100c17023240c60082c80c0c82d0281d00400e109071035000070000c900303a200c0c506210b00c00340c140d01180d6a00300403880c40825800c01500003071054030b440883c3c1040c5945000b8100c025096803030002c1d0300f00040c100c2444614a80049004d075490b5408210311016820701070300515181c0801c00000d4580a015103102d00d01e04024080080e10014511401e00d40c8006c4c002802c03003401c1d070b4180c0380340540100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 427474379 1250 427473129 427473133
    0x100c05010e01050f09011a060c0106030c0f030308010e09070612090609031e05070b0c0a0c050604050106090b01030e031803010b130b1809300406050a03060510020714040608 76
    0x1401c040804190090340c401d8803a00c160360740c40e0765480f8040b4262201d0101e22160030703030400009811402d018004140485010001190185e540da0712040104480e5003c2602c100d205a42071080503403050b28680101a04802008c140c00c1c40340707030f2a4903a10386104004c103010354482e4500e5604803640140d0622600250104500c500504010f403030000303000300241c040c030340c400b1000080c4d0380100191941c42d90009a24041ca40c3d801c403000d21a070f4400a540018080d003880ca00000030010400301d4802e91045001180c00e40ca410440300079074081c4881d1038185403c202541401d040000141c480703400c03803191900711600490001c42d00500840d60f0b102d8015080005002d0502029000f59003100016552441024098a80d01c10b15103819941c00e5041c0e0480c0615184225201402015142060000340c48030030000d205030000354003da1000022500200f8500c86080d05482140014001134a01503041c40d4210300082d240c030014015a89080a1001100003640301c0c0d5200101404050741 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 427475629 1250 427474379 427474391
    0x120c100507030c0e010206010605040e060d05060403110c04090f0201050a0909020a051c0203041a0417070b0601020115050a0b1b010f051f080309010c05010e1506120105010311100c0501 81
    0x10700070b01601c03501032000082003940011482c1948001039480c101c940c42d50701c0d41d041c0341c200a00c44458407806000319501081d810060000301e4014800c0754015446038940e001c500c1480b1207001c0c1000039a00f80944903514201403c400708403030602c0c548286509190041e92071107600810350700c10a80380c01c0314498902c0451581411a001001410040451241a0307079004224001105030701c4100e50080c102181d0341041c6203004104201c0603045485040a030704d411001d850014000c0e0400c01d01940c401340040c091180a5070284152030741200c0d007141010f241403d00300402d4190f8441d20135680c252100003010350200411040c3e180e07514407840000e1152820050024015060a5034406824000c128000035240c02c401410401c031039102d0051410300c1105401500c0c0c1c005482c04c1a00c0795500d800e442d030100c050074440140c0003004211102c0b19030070080705214030301d410b451504d2a640e15080043c400704c0e180340d1842c1612001159100e90407008044100c2c0d1045000800810303e40c2442 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 427476879 1250 427475629 427475641
    0x20c101a0103141003060b281d090607050d0e03070602030702010608030a09091a0d060e0d03090804120302030c06041a0714091302160b0108010b0a0305120c1005 71
    0x4200c0d0840031209aa05001c00c001000f03407910705400a42c4d101c00403110b8201c0030000501940c02081400c60000d2000d4003045015540e51900110100e0030303006903a150b0000d0000d80c1c034003c001c80d0041000c401481c6a45000d8009582e036143c080c0c1000c050090214803209044c00e2a0030005409032440c055030346074111443c1a00103500103603072240155081007008201000000140d0740c0628441c0d030381550640c41d0003600c000500d003000f000d115002c5d18100302203103600c604408812140c8900c20015840f0400310031a0705094525841c60304040c14100020045030342c1405903000c1c1d07217402008140c04d10080c40c0691542c031598244040900829042209112016402e164040440145143c05a0300e54104a8561440c900200780e0440306110444840c20080030020254284010041c5400d030301c0b9140040703003012120201e81410340d10005000000382800b0382030b090303c4140c80d8622001d0031070790785a80b5481e01600b40c611b0380d034012030f5030382816404019030783e100183c42c281008641402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 427478129 1250 427476879 427476911
    0x1020d09150f0b090f07030b0607120311040b091201090b0705040303090605040f06030b040e0f0a0510110f030403020c061809060108010602030414030a02100e0a14060706020c10 78
    0x103420035141a1412403a00040d10841c040c0386007076a0000c0c1110700d540d1760080c0c2002c074082c0241604007003580da17800908040c4c80303500043ca601e03801007241c4001402c00700801411b4a604644610079224184010042c0c41c0c04201a031b03416034421507008241e1180c600c0400e004020032407019240032003541c280f218454001d8010400c1e41d01039a103480640ea1200b40564072481240b00f100e10741000060204401c3e407013607112030300030600100301082c811144040740f46055222040e4044540080c00b9139000c2060400480102c0b0001190030300804210300140503aa004810604140c1c0200000140404d8030034411441c0040c40104241d440e944a076455a900d04901c1a005010300d245001117945503000e2019281250450342c001c0d86058101030fa079410302c41c5444542c0303070948a00681d00b00180d4800c01c0c1d1b1546d02049030307500700d110064107041140c84826076000303201d800d09144032480251610012154400d810100150391000101d102600e03200108207008201481e101c12040c1d48051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 427479379 1250 427478129 427478153
    0xd2103062108270310020a1d01020f0706050c0d0813081606060806010905150f04271a10061d010c02030a03020c0f0f0a0521070b040303090b0a0215040501020d09 71
    0x130b9003100c21701c185524000c01207104d00ca080c98007007600725a1103103415545a2286e9055030040c416070f0344544104c94000c0ca04500c0d9000000842da02245d074601d603920402152000020b80d01d4800f00c0e50500c07101b440301c2d00c001420003404150700011507070f00d00d61064000404255016200b004966503460700746e03031140400e00504044030304140201d90003d00402c80d2400c01d43c8010400c5090041c0201003000400cdc0800d00311f100c0c0c00e02002410405898891030404050280702c10814a8528400040da180c1e030003460108150380d50701050107101e0744001c0180f0a8610380000014810b085801600c0380c24100ea002035040c45241c06402c109913012070a1100c01a080e59002d210900b81c030100103c02626440d030320f0b0001940c0404000d24501205601e4244070404101400007084544042c10002143c10803c684400000c040041591010359180284415600582403000400000303440300c0044140311031440f02e11003c501803200a42c1107841d5100c507c1c4041080d10320a241052034441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 427480629 1250 427479379 427479457
    0x40b030703090611070201050d051b0f07050c010f020a06150b0a0507121e030f1b080f01090204060806091519050a1502070515090d2103062108 63
    0x4240b180c1c44131031100c0d920036109840d070b05031210303402d210b00245051300600005042040c81c219203400d0f2201e0850480c0200310302c03000c2c00030303269540c0154180f2901c6d00b01c100035014100702c0d8400c8201e005c4ca60101d9948106a032103c0f0214002c3c5140e84a50302014083c0c215904258000803031445043d0048001c09241d0712500c080c103da03407c2141c040e80c03c1141c00800c05001c62001e01c543c40041e02c2a406286c0141e11600300141c01c140d00e41518440a0450518030f01040000040c0f00c40c0c544121a083d006141800c01545000c0c10003030010001c0ca406403200d4040c0200318003081114035485040d0301812405014009544065105035101a01600c140c80c0101048100818422001ca01c01c5d010400241c00a0a00c5c0d46440c051080c14840310352202c040703031010311002205035154040e949400f401544110801104200b41d003542c001d001c09408145841c0c0401040300d24207078401d45a00550702d52080240c0c0d502420428114440c507050800d00c40c80c6a4002ca07100c40720503017410f02c0c500c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 427481879 1250 427480629 427480631
    0x1c1203150603020304061d0c040c0c0b09030304031119031110050a0b040f20131a030f130506040b090f1203010801060806090c04020906190c06050702010b0a03080f040b0307030906 79
    0x40e41c107250550351f22044c2446030843c5a801440e42080e4200c801c0a001c0d13880e00c00194041520354207040d0400742c6860100d0f8000200780801e050303008841c120340d5009400901000488224495580324425500800340200100c030b40d8001c10040c4403504090f8803445c824000c924061000c00000c2602c0d000d6581706501c2c016006010b008103206603400c1602d464000f11101105464079030703158002070750390b22002c5400000499403914002d81c411040d8840c003080b507202e08020305403000300d00c8020107500601c45008960008104000340180d04281c106203404032a4807520019828681c0f5854000402d200700010300d1314400c8041c1c020b604030b400c000000c004168a4085007a21800c2c15114004190310003071030640c80340380503802045200f05c000c085516040030b003003088050142c100101008543e080000341d050042600400e94001c1c140d00c002c00001b90381c00b00280c2d0301080f90002600c002c0c03011620003440e6800c8001c90740580300048603580ca030b00d05104020050001030208540c25 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 427483129 1250 427481879 427481891
    0x30305011509090c0e1009050102010e0c0a0306020d0603020a09090201021009050a1113021209060610021f06030c03081c0b0d060203090703050111042903190603060501180b1c120315060302030406 86
    0x1e403000dc2044400840300800b02981c0ca0301c0c41d1140c10107500880001c1d000c05668501c0040140cae640f0b10808002c21a11802081e8400c10b400003a0810802c02d4030000e07020b013401000f2000400208405640b07d60002608400c81c8278400802c0451220024905c0c0542c400611089901c21042c030b410311400420080380e055075100c4d01480700e0500881018009a8005511289040c5185040d00031641c2d0054002888565a4560b20141d41d001e910584600000142000c01c100900b000c0304150188179400780300180a220114100040d40c040140c0910760200120380c072120b042c44143c004682080080c072442c01c443d80d012013143c0c081d111b07500007915242e8502d0300300c0c2c1a41c1045004000461a1542540d41d6122103034503000b5100c4c498802542d6407000800010781c14810039005e0003c0001c101c507201ca4841c5030000b181d0a48140a02c03912a05440361b414070716a003d401095544a0a420002d04940030160040c0c2050703c804118492544004113070740d5415400303544200e025040034041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 427484379 1250 427483129 427483151
    0x5042c0102090916020c03030a0314060f030c150403230d030501080c06030403030f110406020c0f0306060d05031c050604050622021c0f09030305011509090c0e100905010201 76
    0x1c0744a840d40540d045186600051981c0100304003000342c0ca5000d0040c1c408000a400000c0c0c1154050040302010941c0c0349038440309800c20445482d440b101c01d0340c00035100400d0000084d91099031003039407032040c1703140001141020422426a0000c48e401000010031506202c400072a0002440c00018240300d02c0c071409911621a001c0c0504850f444400f405181c1100c506100181c2e00081c4103406041c4c60720308425160340a4460088450a403201e034549440c100700c802810214022803441c0f16001d8500a404941e078040b81e82500403d003169044105001858414190300888a0070804040300c81107606400210360056845084201e03004c00c00d5941c1c5c2c60030080800800442c465503e40340600710325210001e5070080c549108003186240f041030480c84c3c11420f843c0c41e00001840f80b52500d0081c2e0030940c05000d010b02503c40a05480004208020000c00440e4039114011f20303627841c1e0404202c058000c6020041a4202400004180600c0c0c00081c205480c1841344c140190700c0c281c6d80c009 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 427485629 1250 427484379 427484381
    0x917010e010c0c0c0513020903030c060106090f0303120e01090803040302030d050c03042109081902040c080c0d0b13180b060a05030c01031d150103050d21020c010605042c01 76
    0x40f40da03501c21815400c0704c1c100fa05000c0e2031440c160b0813240d800e908010700c03465950b040014005003040c80e00101803035130400f00010700303c7c1000d0340206580c2000b010140006500b0100381048026140c0c80002c801000c148070358003503c0030403400342040c5000028031090590100041007103440c0e00e0418010307a00d50094840c81e500c81114042c068202d140e40d107040420400302285120f511900c3c0c42d648040c0c444041c1e0b4240300c8900c031a4680b0030b8003405141c085084c1801561050340d00e5061128444c43d01110081c0e0520500900100c83ea40c1c0311503880c25591070024050440103841d80401a000400840f11400f003450003042e6404801000011820705e000f001c1ca00544a014010b001c041c0c04d03d00054000e405650412907035032400c01c0d13103000301070001c004000449459070480c0f0095495400d140d8200112800482c0410000c034107200c110503010100c0d064110340d07030540103a8494002440c10300500c1c83c0d401c05940302d41008000c0c0c805000e018502c640000794041c908111001d050301081c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 427486879 1250 427485629 427485647
    0x60f040519120305340206090a03060e070612150612060e0c03191a040209060408030f0901110d201009031d042c0f0609011517060c0a0917010e010c 65
    0x24500c40170307072035000505001c1c014084c0020041c01e0042c0c0c244c0c80c1d0780c80b10b0079075805a64a0320303190700040c01004034551015214588801c90003040002d01c2c4000c02c074045130050303805041e051166944100d04855002c4d880072004001403440382c09141844501c00550b940140c44100142d0000134010a003081107108540d4140e40007840d035020740c000392050102940003461080c0c1c4c4000103000c00590b151040c0024101d1070014a80c4d04d40d00d0301c031103001504851039038400483c8c943c440c184109035280c0044900c0400030f020300903140780700a10210285004240d40940844a082c209400100b5810440100301c420488800100600f240c3c01880b040300d03008020381030081240f0b00318450f00200b0303640c000c06281c40c0e001525401001c40c5c0d1840d103008001d40340000184c1d521541034581d010225042805800410001c140d01071181c485995922000703442d0501049000410140c100d010351340d188000c061642c1c1c1807400118031641c241c020942c949c800e04083d401d00c000e4071000b600c00c050103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 427488129 1250 427486879 427486957
    0xb0a06030203090d0e0a09020c1509060c03010306090f14070e090d020a060b03030903071403010f0e0a060c23030f0903090112021c0f020705010b060f040519120305 72
    0x52130242c510580459560144ca00159040f07104000c3c0403030b0190290004081d61400800141803c002029001e250314200410051441d0000b20610441c0c40058080781c0c11290003010118180780b4909002200b841070402c0100001d03d5111064488500401c0c92800c984c54811000c074141e4440c034008e519030a10700740c1000142c101c64950700000315140d00681d0807030405000c8a00300300e100c03804a86005480c2d004401150100302d8010714901d4240141c1c900400010000c2c804415200d088a5171490110b500501c0551500702d0401d445102d030384600b461908082c2e40d0b242c084e49841d0780d2182c540c0291115601c10840100081c0f4558001085910580381a0364072a000201081140000e41021005007188220240e0b040d9200c0074900801ca110894010010717038801d42d41c03605c5801c46a4405410340603401c1403041d40e03d22a004800d5130100e032002e07140340703c880380340c125140c1d84d040441e0440701c94072040f1110070090551100291490f080d181000700b07549400e11005c42e4100e0039088107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 427489379 1250 427488129 427488133
    0x904020409050609071b1401090602220f031709370f05060a080a02040509010f08061024020a1b06080705070c03120203092806031503030c02011101020d0b0a0603020309 74
    0x71003000150f821207481f4107401800000520400b1f01c0e034921050364440303070301c0c1c00c0500d1540d85054144400d4501d8000204400340300340e00128a0740d583c80000038818409841309103008591151142c0fa1103038028002c0c400481003202120720310a030130b0700c84015240c8421148412190204085490021000944400801044c00c000c01d4040446000c140107027000012034003400001465158450380324080c06510b0404034040d400e0105051078028000c0c140641c0c080301800402c101c01c60305002440c56141000c04a0301044051002d902d49124080000c0212007000c550800d2201e44007004019580d103641c401d8056114010100c2d900c0c0915034002d0300144594800700006400b030007680345c4d4108a0700540e4280b0400e030b4000b8034805543d01030443c02d0350103580f0b00300600706030150000180c11142030030003018002c0500860f002040c0c1c0001000e1192001c4d0301e1f800e5a000d944000700c1203560030003d40d540d08106500b10094104002c05901403641001c000c61500c0c024001d40303103c1c07241080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 427490629 1250 427489379 427489427
    0x10c0e06090f04020306031615111b010e060c070f050910030302060a0906060b1c050601090803071e080301090b0f010f080a0515030706030209150c0a0303050a02090402040905060907 80
    0xb0400000b9840a420140d0600c1555950060b0580e5445054000c002141110505004c808005040c0c20b2620090450710741041480101c4074032617002c1c81020480a203002259160b04c1408941c0070b00c50000001590b2107041c9000900711360110b007520585005a40182203919020b203130b0440c010720741c0002000340c0c002c040000e200e4482580801c4105019010104001d40d1700c2d0800701e6142d00884e80e1900244021075040b5001c0074a000c3c0707a03086842031912204891030f003c41030340c41e4007988800401c00f050340300e85005060b404043c00c21101c1d03000680d00380d895a48184000c004c0508145890044001902e21540781d8080c5001800900d04c58980802036034030501c1560080c600101126408003000e550245036840c100301001c042e0806803001652460028104200d0300000f5180f07180d5407004002040c5000c1d404521000c0a039454107021810391103a150710000b80c050130828136005403000c42c0000316004550880b0f8010042a1056103441d221020b044030300751002e138410310034542244 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 427491879 1250 427490629 427490659
    0x10b04020922020712030f0b030c13050a0204092307050310290d0603032d0f050c0102070b070f0c081c0f02070302070e0112050705040c0c0203060108010c0e0609 71
    0x200104180b40c010800041c6031848a9440244014000b00c095000035a50b41060444540c64480e20382034907811070041075600b20540008408102905042d81c1c032580f144085003051103150142c0f4040e18406006201503441034203500c500c00d0384813428010119032400465149170041c3d04403405419240450344040341800709041c0b6000118480c040f5226280c42142041d100d02800303041c5140c099000461041c0c6181401040961140d00071100141d07204034901c00d4403125814100400094107204e40345842c09401a00c1c43e00070f400381141c141d400050144204405900d1091054a041d19108600030b100c040c100d480c2c041511000300030000070030a85d8200704242d9003441c00381c014004082100546942c1100c2130740c014410490150340010400d104108004840034098a41320460070942c100d01d8543c0e6644802c14880d00740102c1c0da8682162a05118550406d44190094220303a0156501c000700d90080000c2d9402c1d20001c0e1120f1243d80c1c0314038291f4100e81e25110000c081d540d24180350 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 427493129 1250 427491879 427491919
    0x180c090d02012102030108070605090d020910080a0501051603151a04050402070c03030f0c0812150d03020616051c0506041e1b0c02100c0602040f0b0309010b040209 72
    0x35100680c1805410303560f2261148403200710301e403d0030342e0000168507540340c100075030b1405030150010380a121040c0040c581d83d403504c203000904a87c0455001006858120203643c2c202e405801141d52406100300c400e0602205401260040298002100000c032034000704400701d4100c0c404509001c034810404014564051458150f104004140e8500d4541d0b144006400c903806954200c030741080c012020028140c1224843c11301041c0c0d800d080342c022085a0b5a8412172003200c0d080c00442c208500070461503911052070004040e4090903118010015080c0a03540b1881150102d628036508404044000d10078015188100c040d601032000c00103440ca4400c028045c000c28454200c1c2d904d016080b040003000a00a140c0b4806100000e175251000c8a400b100d203140c141b0500078442003003a10401615070390700e400080c807814a0000c0c02020345280c118040d101380da0104000101c0d184000c17030480040b100450142c0080703402005120300550a1105034052608400c1e07000800240c05040c0c0c03444 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 427494379 1250 427493129 427493149
    0x31c0e01080408090a0815090d1b0c03150b040c050c150903070c060c0303050c03060906041a0a060f1b0c150c060203010902041707030503160c0e01030809180c09 71
    0x41888038504144800003ca4170081003a400140b266011074508500700c0c80800080d030304052079102400050049030390140c245140f923030400c0c060328601c500300c0c4103005181d032020014647c01086003540c20004840070b8007500300200c62a01c00c03442e140c403540c0c446001e0b40440700ba04100300301520083d00ca882110328084802080c00e0b00c18001003203031070001141481224080c1ca07440d03c0305413990364103040003022108014042c0d052520100184a0f41d1750300d4944c40c44c0d028808503030109800001c441820b140500307030454103411103e0a0380200303215403c2030f80b062401c8495940c0440c80c800b61706205441c407100301170180000100c4074040c081d1074050701c400811090b050810a08801c01907030780c9806c82e802603202c5180107038081070070700c46004010f420301d1181c004000145091400e42e10b950742c403880707506010880c42003038801110400108660500c02040360350950541e030340e500d09080307645520a00380d56125280c4050740300b24120860150601650010001900f02462a010710000d816 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 427495629 1250 427494379 427494383
    0x60b03121218330a0903020d020601050a030b06010509130606020f06060609040902180403051305011e05030601030e0307140f0325080418060f08010c12050a140405010506031c0e010804 81
    0x540f280800c004050b150140261400600064400d6590030300900b80601124814115003090004201599541185800b6290021705c04009034440000586103803182c100256001000d00d800000029050340c8030804461080d002c0e1404240c42c002d00c40d07141c07442210322590104042c402da4500d420a6440016524070240030468525800c1c0204420560211412800568006030420407082c54000c024000c240078240b190b410601c503c0c002103980d002c1c503106402c110001c000200980e201303400c501483c060348000d0304d40d04c0c016030808031031440c22028081010b2050240c41d04d020350001049175044404ca80c030410540b07a6540a148504c09108420340c1c45003000d0002140205a032a4210301e600c8107000001680c034944102c40721200c3c02ca501008a5034500301d102e41c0d400c1d0300090b44520300030740c8280c0050f6680e900700103200140204180a0020015901040204401540920301400084089412079444030100004140786090311000085007103002c484035501400920740c2041c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 427496879 1250 427495629 427495693
    0x9050601140721090513051f030b0a0c14040e090c040203180f0f031602150c0601060e1e0405071101050705090103050c091507060b03121218 62
    0x96880114810103410002c801d903040c110340c0d0b01141041d4071506030010900b8190902802d041d142200140c3e000300c001160790301c9a42c072540000d05071001211101807d028614600701a83d4403401c0026508104850561000f403070168080c3e00c0a015002983c8425003188140c0c5c0fa00b82803000d03003072030203034068400b006900c28000210029030300c60020354890b0140d00640621085041c0b031907403407c14041c0520b45641c02c1000e0b9510f4941c000b0040f5011807280320302d03c2a404c48a8408108034044e41c0c011180622004034568100c014080b660714100c030b032a545d500385d040c16080200140c0d120241004000070b0900d4110842906003a0003665000e4442c4c2042c503003001e4000041400d42e0422104203000402c002940c81035907802d403060503000165030801504101c1e0700d4010604100d0b40141c8850145008a140000c1209540242c1c1180341e01400340c40341d800280c001d1078425006140214004111040007404043d560460680c040030b85000a16002101c803260740c45a180e002c117500801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 427498129 1250 427496879 427496897
    0xc060c0304290f07021e09150d1502091219150207051b010f110d05031305013206011709030409060b07021f3903021605040902060409050601 62
    0x1642c0b410050032140c22001038180d0741d0000c41c0704008030130505800c0901c0e4900e107070002407a10f0701c41c1e41c0020f40c0503000e03500304c40e215505000041c540d50100303040204404094904240d1043c200e801401070b0030001e95003a10200c603000c100325280c1c0c507500d0000410520203200380c0b011400e00e0b100b004100c04400001843c020090319040e00340ba441030442e880e215050541200c031940d02c103a4550388a400f900d442d07010f50040b490b8064943d500d00f81190100080440894411054508005005a80070703000b04014008840d04900d0009031110929101c402070103006a03560411000502c0340c40305940d0343d4030f4480764070703140c80050601030140c041501c0180b1010448142600c5103102620f0580d507156202d10144c8100000c50000862910400607401c4800042641003202002941048158002c5200d6141c80d170002c1181d040805030691614086108281500825605002c244510304624115110402d00042e5603a1450094128608010030041700842d41c1c0700346d8000340145010701c85 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 427499379 1250 427498129 427498199
    0x2091201140f06040218130e070801140a0507170403090b0706050417070c030303021c1b020645070303081918080c0a0b01170c060c0304 60
    0x71501008a00c48001070601c0c1809000c40912a44660140c41140c055251100c0d00c40c3c80b04003516150307807141c042c480d51030600e814042c0035009030910580c04001c07501c17004e50311503405020b4108007103880500b2a0410108403145c41601070309229035616114a16940301d80e10604144004c000c10035002c10000c0440800d0102c5944000c3c034040d80203480104079410a41498911000c107000c032000d0401c01000400700060080070414212905402c00588503414250303004299003030012300e1081036103000941590111401c45010b46002c0980c219480f0350344240c0daa00e00c03005940030785941300c1115480c0c4e007440c407040c041015601c0380c3c1d88011080070038608445444c046a6400440100d8800c07400c01c2510340a5100c544581900d080c014000684081a51001e10744241d2010b0f01d4500c0001d80383c00800c1d02001000c18041e03000c14001d02a40c1e486040100303004ca1b480c0c201005000c0c4140f40300d8189000015201440401c1c1c003d1450549031000d15001d07a040c217121040000406420611 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 427500629 1250 427499379 427499381
    0xf20030a0201062301020a02060f0f0301030309080c1207140a0b0f042111010c051504030503090d0c17071719090b07030905060c03072906030d021002091201 69
    0x240d0452070780003c034403d410060391180e04410500d400320003103c40103032981390383c3c0d00180c0042d1041e01950081c0e40d640d051404805503101e0381c103070000c89810010001081503417242c0c44204903854581590405d811070402c008040030301400d807050030390222106015183d2801070102e803800b0002c0c015143c1c80e9035000524490b410070706c60350f0350014000c2810045884040a080b0b03101102800c00004050103a03505040980c2c58110f0310b04004d0380c3c070481820400208161180041c0c0c4000c1074a0a25143c98010f10355407044075455000e01402070306008550082d81c07074681103a804040c08000341d10144241040350081d540c2681c408810707003200400612400000c0260035041071a03151607082518014180d461036a0212080e02820000d180110380c1c000c2c00002641e2040b10300542e6150361154003491030061910240070501e07800d101c3e14100001102191056907120b200856a03070b41e000415481d0505107006202503000046004400c0405500400a0410050240402c20a04100780d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 427501879 1250 427500629 427500637
    0x4020907120e0a0c030b060102120a030207080903061924030204020708120705090103140f070f05090406061706030d05120402011b03050d050a060f060503060f04020304150e0a030f2003 81
    0x41c4846144e50414018409124416540100207000a20002030726400200032407040480034070405074082483d004001d155004c440c03c1010080844055042200c4020082031502a00d01c0d07a1514001e001c403c1180f40c820407502c04802d903040c0e00c80d82491038003440003a622506080328445010001e940c210442030810178060340043d03a446444011540004d0110340303904401654421203042013100213481310030340c0c2d6400f034440d03e400e002008800c80b0a6446000380c00707003640c3c00b0b0300740180407074141d900c0140e0800e22868506040d09503107880b8140b58644c0c11031880200014001c024205248000410340c3e40c0092040c50800740401507004c1084d000880c20200b180004c10005540280c0402c078011a500400c1e031145c10011541b03050069000300c0b007584140d50600401000041240d55101c0280f0b8203107d000c2d005660700d2030320389801c4514264a2804488082c541076040512200006518100755030607180c4228426010310240c940342e03a4a5003451840c07040e411a01c01c03441d0244054 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 427503129 1250 427501879 427501883
    0x210105070f02010b010201050424090c0b130e0c03060105070c050307090e0609010606020d32090306090c0904020904021c080a091a03010b03060d050703210804020907120e0a 76
    0x150707101c094510001c1c00c0d43c0d00c0c1001c81d411a0f05002c18000072402404d941045940c0c0d801c51220504105000c2001405041c107000d8110804410300103a80d60b10315000384480b4110502d4210303c10b03222004407074188416035104485103001d20010700c042d4040c100030060030b40501401c0101a0340d80b4006490644c00b80c00c80c00e5030940b603111281c81c084d41049020b80100c1c100000303001142c1007400c003e54500c0c0d00c0b0904420082401705849000c4a0300d018000003210144c0400900c10781022008503590044111070f02a100e440000303884540c01041d6215004002003200c4035a8a4a800300401160041c00982c1e000e1005a4124508002c903400c80a0881c455044941c4610781c3c000042d1030002c0a50101a40c8400382c04141d000340250f8080b41c1c15103031a5910140c1380d448000101c0c00c0f020751954000e003d441440310100a201e000082c5040d4060020318800d00700407601d904492850040d50001d410070390020101340900d0003140f56400b0210300c410005100d07000061240d260181103c02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 427504379 1250 427503129 427503137
    0x150a060303121e050a0f090503071a0702030901030c1e0806030115050f0d06090807030207150c050d080603010f020706090b070507020a0e060f06040806071d0f21010507 74
    0x10010181c01102c180a81441e00200b002902d280c92140040c084072003903824040340d40e940010b4a040340382e5001803c11184170790304000c16165842c10550341d034480c00d02a02d0640e5041d820440003c400c83e02c0c0ca200b1500b60b800385007450f45010054010305800c1020304280a5428040407446600c00202200d03074a0503560b80e40103007480824942100e810706100d800411000c1c1083c000c54a50013503402640200341c580380744403081c0d0309080004003640c0340c00505000c4006485401d00d40d0010711101035454080c0060540720f24000142c9080c0044500101250000c1c20141c1025014244181d840040a0b0000c59400d00044450b0200c0e84818000c540e0203649060800500c07203107960701540660142840b82c908081a000140c2c42c490301e10810044211a60016913203840d64a0700c555000c80150040b6111a00c038104140c991404880d028009048004600c014405445111104020252445055032600401c0c804908903801c05907080f0003c100702d2001e541800d105013403240c911551 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 427505629 1250 427504379 427504391
    0x2319080a0605010810030f020303040e13030306080d2021040303170f16030b030a0305090906090106120b0d0c080a0524060f0f1008011a0418090203150a 67
    0x40940c120364541e08800e04022540040107544201190880c041c3d030b030402c80038207480e40d840c40040e195105981080000402c11800d01246441808a511f84036100740c4040c066584c84172007030703607079420011010700008403104001d00801c1c01d0918050722800d0301400340c403c0e0306169000ca10b14008011170114006400190070000c2c158030605000012600d030042044078100514140449a006044950b40740146030700520068029402a101d042003d401da4410040a05000c0c0483d00f01c44941070060042d54001019807800022050690700c0c2ca881d981c86000e4035405140090608008641c2c2000103070780b030ba10110361444880802008168000e040341c40d241e19065083c920543d00c840410394000c6007209222051560640e404541600d6240e0965640c000107154820502e169540090100d0100b003200750340300c01c039035041e03c5c40306071070180c005124660108984524030074100c1d0700000400c40b4020b80303400c3d0044450305000404541c446407035070321004076080e0292003c0001c42d035108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 427506879 1250 427505629 427505641
    0xf11030708060703111206060f0c12130503030c0607080702071d100f030f020d02010e120106030b0601020c060403061107080307050904180809040903210218040c231908 74
    0x10040861950117120582d06082e4000c01c00d011a40d00600014480d020100f403c1c1d0318003a0402c240d0303020343e5000c02100c1c0d00b101400d0407410150301c8140000c184c0d598801011559003000070855411034140e4005041940c0c42c03c07011140d241e80a0011000c6024122000400d20f42000c1c40000c114607030700401410b8180b05c25070340540c072495030046104015119041009c2003c880514001c3da070107540c60a6110514401243c540e450843d010740e114a462500799034440c1d0550184041c0d03031103811605071a031249401a03a13113001500740f941d40706404000030700009034a078000741403c6035450412420251181e840c00d9640d00304031407080009002044560b030a10306030140a0510194000590000030039455040261083c04c075080c2c000c0e525200250300301440340c15010888588040209140c0d03200400b8070780030758426000090301c00750755003d40d903440c41c052107a814021041d848451620302c002070300c0c460085106039020901c00d02800140b035260840f07109008110282e5840b401c080c80e100e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 427508129 1250 427506879 427506881
    0x40f0c1508150114030a090512070305090306060301110409020c0102210f010e0112140c0a0b04180510030b1e040b010e0a1103010b07060e0a03031e0b06070f11030708060703 76
    0x1400c0403410050351001345a0020314400849170080c3c00118007240a40c03007414554034085804000b074458550018107841456032103000b928610308110140e1366241c86da2000c050036944110381a00c1e210100b00420080c42c00305500034201c840c00c040001d818080782110021200d0541503194138419145010000b40e16035541500740541041402c002040d41070404000710030100300e100902c207050000c020b03540c9403001c01401d500d07030303d00400d904502c548410a455207074000b0311810440702100508103041040702c0c00b4280c030661b2080140380701d040c0f03107840d402e00814000d4001d800800515101c541035004031510540f180d0b001d0426450035516040c0c00c10400781004125503201c03440c2c00e082c50f0503c42c0990440f030444810114451b103070103103802c0440c02443c215003411224440c0e144448101500b58120350400155080303030402e6608280005400d440482d0041036102d0b80821401c400134184002c007000e901e00810400301c0d10407c078030102e4900078150300504d904c0e034058801c001c031203581 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 427509379 1250 427508129 427508161
    0x3606010b090330071b080f0c0303190c08040e0f160c0c09110d0608070905070c03020607120209090f0a050c0909040f17040605030601170f040f0c1508 66
    0x114142075100c03010142050320f20083e079242030300840800041c41c00140801da2241c5103d02084200052080d550f50481030741d5140c801418090602070000c0c48100c40c5408800e036418683e05407440c84003170245a80440760074071a400304075070790742041c400032038582c40540105100302c0c81a00116043e04044180c4460300031041d074050100145025030100155415203150100da50000d404603000089819040a034007480060401c0649040c00c00901c941001030500101c0701c400ca002c110940344c00100311a6078406442c0038002d40e20060214103114031412a400e54203003810401820200030300c2c00a2954042074034001c000d800c00d80c00313001d0b85580c80e04c20503070080030003215186010391501c042951000000c3c000740010080c441c00ea030600540e1030b2203014160200024980c3d840c1c40c1c440160080c0c00035514140050001c6c60b41c1c800c1d0010250580340580b040c50800c0100b50345135507410f002000c90502c101c40007240044002a4403610750090b914200075034407840100e00d80380780301d0815402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 427510629 1250 427509379 427509403
    0xe07181503030e040b04020c2b02070501091505130b090906010305061e03010906050108160b1305101806090918020f0907030605190602060f3606010b0903 68
    0x10358400801c00260030450341d100b40e0500380c0e804140e030384500c0c0014000f0b02402030249802d000e580d0820004640440080d1260032000d9000e60480107221002ca0f51950a4029a0f0100318681018003190043c0040380c400304001e49846468040b100b1030100c07820915502100c40f94102007410f0f20b0626128070a00c0d8080b0080c41c04000318908000003e2161401c4100400200400074600e00707142c40a410400e502a002902800207581d20034107203640b590b12412404c0c8182030520f0101e0075400900c1126140d403103c0307442c144035600704020004443c51801e000414850803840080011441182400040c4410744030700788400e1421034000251406a40e410b6860f1002c608000010780c2c5450501114040030b0b11002d44541e280b0704190300038100da070003103648507110408980602000c0b039840c200340c48080d400e881d299100c0a880b00c03603143c2c040e01c500d06003804440707901c240b504500b8100048035811032010005030302030060007401c0880030b8000d011714500005001d2a41c0c01d00b0410880e00030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 427511879 1250 427510629 427510661
    0x70506090a0c120309090e0f06070302070b060f0d020a0605091c020612100e04050303061807080103030e0117010810110a02030403020d02040908031e0a0908040302130e0718 76
    0xe00076a89042c03100603180142154440e10b0f046000c00d01d44110071942c0900410803007042160490031420f6524031880f440c0c02c2e954402c100000718114442e00a462800c1ea101800c4001500c4100421108840d42c440064200070000750010160b558111400300602c000c0d1078041c0c0c0c0340221024840028003c0880540f201a04a0420010b8071307001c040791161000740c2102078a80d00e91103681c0340c05000640c00880c0071220075041c0300521002000542c01002d04440121a0b0075018a414420480490f0160040380100d0010000300c3d000f80690807500f201450040f4541c802689411008602078110f000705038804880c041075501c2c14070462804188100215081c0004403500039602d01c0350b808001c0c01880c185208000310f4646070400303500700d079100340c00c02e03228900340c4a20031041c0e83c1d1a402c100780c005240d011038002c402900c6030b0056940c1105100c2c1c40c04d070130741d005d01101c030584c1414074904564400e004040080c060000d2809440c040e04030358103c0d00c04650780303815515002812a901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 427513129 1250 427511879 427511893
    0xb0708090c060c031918060e10080c0d0522240e0607050a0306030f0303242603040f06020d030e031303020409060906050c0904050a06050f09090109050d0507050609 72
    0x543c000420f45000c40c0354a0b03190700d81e8862000003161002408620004070b046030400106280b03800c4186005451005c0d54000401322803194119000441907600702121030003040045680c0100c0d1708002d0f070201a142201c6500d2982001c05002e042500b4000c0e142484100760080440005021009040b0b066000034014001c0007804692a100c024007608140540041c004001501036048400216040408035186140794200500603100d01f540307080c6400022030043c83d0200d440c2d07840e00305444407005201e2031610b0300c000c0c2c070303003021440e00c4800254441480001080340780c2a283c880034114a5014121201d007180700038064a01e0079910514582042c0441a03000c50400f005104482e0101d07004a0040c12604001000340091603010f17102604107810000000500801840d10550507142040140d03a103000c800101e8010303001d01d0344d101d05080704091071441d041c44400d8100303051600004144080e560745a140000f10005400812008100041403050a0021a0b80060544040c00303007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 427514379 1250 427513129 427513147
    0xb0304031b14150601201b0f0603090106033804030c06062301030e19050316050c120105061020060c0c0d0f08060d020103090b0708090c06 61
    0x74000203040319280c00301c80c891011040c403004900400c5407070380c65010345201d144450b032542c2d00c0c03c41c1140c103280410b51120501821040c008610040e00000d60054071803000c02800c500410f0003070a004030361001041d000002e0075603e40340107601900301d01000140062841c5413034020b50744540c1c145c0c15004040300d00c044a20310a040805480762072041e0704d20450396146001c0d109001c02c9840646440e05d416008144e041c04128a43c501110904403281052140401102501d41f10b00c201c1032150032040a03403040a00303403402c0e4000a44a2002c0c2d9041008025601010308100d00e0292901d9019900c3c480c241d0400f201000300c181901c80003880140b4128001c1048500c004680c64204140c11030200800202d0743c072003c05140d60341c41a1522400c041092000b5600002c0c0d19107103601490208124480c050800c18800b407060303841c1c081c202d40d2250100518901c0040c4145d041c15210150800010541d5004520900468a82c1c00c0c0d641000411580b400141c144210301901b010411124 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 427515629 1250 427514379 427514387
    0x1e02150301080105100f0b03071b12090f1d060f1008010e160f110c10090f0b1e0904200309070f060203070f050f1f05060a0308090103050403020703021e0103060b030403 74
    0x3c00c7c0c0304500b61040e07580d07c40903c01c1f2400307200007a00e1000c44800c03100000800140044449600201e90b903403d14468807102c100f1351889080c4940403640e84620130700700041d040074910300d50051001388890010034494005c00c4405030796a441c5000100502c0041c009400044240760700050a4100d103104c0d007407508406000d00c50020710b40350a00850f05200001e03c2e808001c03a004441c400b03800d020440110810151481e0003a002da810705c0e10000d030300401d440c07010409a030540d108401034240c1002e80c0d400703080300c00c1c1d0144040b560055221115030b106120191481091074408000095036450078113900783c140710207034100d12005000c3e91000c010450f0b0000c207032400d441d088001701c41e04840526040f1714290b01844054080d0066908030300b0303030180d02c40c54900303400b00c5031030144841d80d45c20082107414205030000401c1210b040c440035a89520030b6200309c0d030091090040710b201d661642c0005000312080300c0b000d428034006c40040d41c060b5902d0700621000b4056281e00340e0840c00e0580c1c010f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 427516879 1250 427515629 427515659
    0x201060b0d0506150c070311030105090c0904050a120f0f090b04092d050402030f12041211090c04140108060a270504050309010e10020a1e0215030108010510 69
    0x40c0715510350011031056a80c107200a03100080b41c1e2001c4e9a80c000341c0e140e40d0781700c202600c01500c0c1001550500c00850078123018251040d41440301400d20784141004000c1c0070381010340203a03140d03c6040c400d280002e41d4112484803810017900d0703500f1554451b0304000c0c480c1203500922420010362000c108010504039054909541540101090b00da5045c56400541c2801400c1070425440c014408002d2221550006000314026001d076500d640b82c40e00d80680d280101d104042107040104000c00c412820781c644030203ca0701c51603605207482078210010714912000e4451181c001d00014040107001189c094045c5106420308025040b480c026001030303e0b0920345d210f201d42c840606204045013058201c0b40c0800170301c660104004074100ba09002e07550750130041c10640440c803900ca01c0b0000341781c00f20400c102402581e000f0860046559100c0ca06206090300d54010010b4036200200181e5903005034116207120b1011040e10781d071602c40c9980c00d4078000382085100c440b0421090000b501c3e264115 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 427517985 1106 427516879 427516897
    0xd02090405130309060c020d2a150507021912030503040c0906050619021c020a110a06050a1b0602030a0504210c03180305060c13060201060b 62
    0x100c098450240400f80100d5100c4000b04442031003202e00c442560310103001d011104042c1c1d0f41702d0680d0110000c92030700ca54001c0d02c425003100c40c200c00200050414500b402d01c20000c0340310142031b5118110f03000e03000e0103000f5840c000c20464008003000400340c0c1c265682c894071035414020b100f43c005890440d031107501d88000244146681c0203601c00d41d10002e0455103090815209801492028000745056010b0000764040000895a4280701d100254024214070241c501c0c0c12038529030410421813007400c95210a01c403569211081e80c06800c99800e201003628425070174440c01204036100103100f00c1c000030401c918480582c12a03400341780306102e5201240103841d405503c08848030180380c000703241340070101c01080c413030030a0541e281614004004d005032691070326410043c00f29038140c2c50304800240c80160009031700d6284020102440200070003814004009024800c510b0301d = true := by decide +kernel

theorem cover : BRFrame.Cov 427338129 427517985 := by
  have h0 := BRFrame.cov_init 427338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 427338129 ≤ n) (h2 : n < 427517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
