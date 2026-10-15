-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4507
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:50:47.125697+00:00
-- url     : https://prove2.me/submissions/af5c51c6-e027-4700-b715-48ac4701e97a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 810431654 ≤ n < 810611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 810432904 1250 810431654 810431659
    0x70f0b240d03030c0c0f1a01050a1a030a1e051801150308030402030a150f0f0b010507060c091706010510170f070e0a06020c03060a06150507060e19110301060b07110f 73
    0x41c41c1e01048854840900e00356503050890b10b8690700e5030203002b06090b0764080c4030045603031102c45288500101000c1c5602194504000c216030a030300b0640301300065080d0814401c0c5131241d0500095442c01e012414584803400020002e26044601c40c20f42809944005429070700000040f0b41507441c28464009942e81004400d035007005180d9020300103003a0442c1d8000c1c20351500c60f041000311200d00460b14801d405950301c90900c0d6507500c0c0d2400402070360201c6410320180800c0000c4c1111001b4440c0d0501110708081c1041d5850002404580a04104001c040000d01c0482c0f400000d044912223400c110440c4a940190b40c0e403500a0b03401044d81d1180690000b102c800014070240d00085d44c0c010900250140c070500c1d260b401c840000c0e14014051515100c10302440d00044910407400b030b1405a0007031002080201100388400d0401d515103103c43d1940c0c0344108444c082c0319060000403070320318054000708900d03440c043e210080c45c051070301c004065528200c0051216030b03440030b100300d842500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 810434154 1250 810432904 810432923
    0x13051801060f0f0f060926100c0e030c1f030906021303060f0e0615010203071e05060c0f0301061b141605030c0303070204050903070f0b240d03030c0c 66
    0x32900784140c01e0500e841103d0b985151514007281d4500e440d40c1c81811035045880c2c8052590505a42d482100d141c200394225689015481c040018020008043c40300403501c00080d002001c1c440040600d0384903845a0f000b680014411021900c0b0002e0041c01e0002c8400d0080380408030403021000b5040350036024002c10b0006c1034400c803032101038030082d0880340715002c10040c3c4001c45080c0010303030703e0f0202e40d81030f0740d006640044c1d104044082d54135034291051050700d1400c0000e94800500141c1ea0040d400d44200b40a26041000410003941d6049200504101e0514621141c10303055407205018030402c00048034048a20514540010369005510ac07006250113140054980c0c0d4a4030a00c13440c0228503031200300000c1504010a465524401c0640514070301034180c0c00703101c0940406016184039100410170840401d096240528841c0d101d040d603100c290a020301c4007480910740e00d504000c00581c401d101e044039a00d003c0814101035050502040c50b4600480c00d07180c41c2c003460750242400c40c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 810435404 1250 810434154 810434159
    0xc0f10050f0108012a0905040e06011d04050703020f0d02060304061a24091914090a020301060804030807051b071508070804080702040227100305061305180106 70
    0x9600440d11580704915081d40381d82e660702945080e41d4401d0210200c00500020081101c181c07100d00701c030b041d07201d801c000a80035601e5010400b110030300b1042c9a1590404001406054196952645010701d1a182c0c1181814903880c1d55403600800d11009100d080d01d4510344e0301a44500d1a540c0d0080e40040c403094aa1910f810082c000d0911003018280980380c86040a200d880c1c4cd0004245002d11881500031a00c03180401c000e195110740d021a6101c034046050048074881c1301d45c00c03805080e06101d0580062200c03001e000e1030718405800e00043c01e0061005200c05540148042d6010b07405192411898980000c255164443e10a120520380305001c06c184603800c002840300d003219482c5200300280c5c41c3c110006c40301001d00343d8000c00001d00e0400030601113512030015114803400208018034202c00e02c2ca29802103016491000381100c0c0b228040d54103481c00c03c404032844e44040c01e060083d4541400000c082c0e0500c00401100b299907140800ca8450048401e0404614404000c01003141c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 810436654 1250 810435404 810435433
    0x90b090109050d02190b09100c211107030503060118060216080706091526060f0a0609050d060f14100602010c020601092f040503150c0a050c0f 63
    0x3104500c251080c0c40b40c124448681031000035017894140340400d9445010207541d450031201d2401505101441c445d150410400e0382d840d10070b500c0100140d4940380c03403075114443d1b102c0c40807a2554225001500c1e0101501c1d00c8040f0030216030007140d05103131031680c1c7d03a43d0b280181c400b0000c1d00311070b44c0002e502391008103080e0b8001501003030440240100002c80b81c1e865403001c1d03940141c2d0080c00c1c001042410704110400201082804408290030103084c07071308400c5078508944032805c1801c4043c000d00002c0c0312107400d01030102d140c003a005880b042c0240e420550003400d100024411603014003081029a030a00c80b403548502020313014540188030010159242d0344104c1e02c25100c2c07440039030320182c0006803240144a036a0781c4400030740150100da803800c00d1002c001c204070f41c0d001c900039107030b80c50180010244800d600b01d000350001c00243c5640c1800c0074149040c0242c00041100c0c0603800c1440000010401a5280b0303c0091601c140d658040c040014105040800c0440292044140082c9007a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 810437904 1250 810436654 810436661
    0x1404053304090b031f0905070e070806120a030e220e010c1e21020c01020d0906060b07050304050423070e031603030c060504060213031a0c040303090e0901090b0901 72
    0x7a01019402c1c02255485010940c40b032103090010304100c54211501700e0703822015005901081d00842c190b43c2d080c1d80d180004103000fa8100e0b400c40000d400c060030024030746445100d0181a01e59072000303080710761403a0f6016000620310600710707100e002c1c900b03401d07014826070b5040c46190301030188003802244050704078140a00070104445d004220380201d490001c1c80c03103c43d06112501d1562f28040490b6039455844807aa0203400c1128086400700202c10810509000a20021401c50b03c0003070340b10301904040f021207103160843d04004a003000040302140001040e1400c4d91030403038001811a441d103034009020080505400200c0c0c9035282040100707500070311842203044c0144c0554002c5200030281c1000210140001000b140480c0c0c080d9000c1403056200ca41e0003841101c00500d48103202402141c90300e165401203c0b281562003144050151110300c40d0780110254070f4403400c2900755a00500062564000d00c400710610714001001410b0940101140f0754106c00f040c0303214148034428a018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 810439154 1250 810437904 810437909
    0x9180c1611331608030f060a090c0203041403012703120902090f090f0111070507081209060f040306020412050c0108060105160501090506090a030f1404053304 70
    0x6030400b150403905110854803041c5108058030300d42400b10070001c44100305030064082007161082d4400300c0400034400000641c0150040c5180900c0c0e0702d003a000700300038442c06800c508400f03404d185000031002d03000803e0320242c90240d261403100b0716a85011070700416000c05036441c8071203110b056403024905a2410520a806591030706803043d942d03002c9070309492a4480080d0008209400a420a0710036504135800072014001e89101182000c041804d403000c10843e100b440300b00260007800c004040003000e005200c83c0025001004807620007200324000c2d9100a070081c003001070b0000d0140140002ca402070350b84100d0464945488040005203911031000454452184a03003500742580661710042c0301d01e03416910b4502d000f00c1d80a00981e1804107080888040d03480d10030180c000790040c09054810140100100003810aa0400a100010720748000c0c0030b204032814400d0304d11015604031400d81e0000d58507901e1700002400a034442200702070703440c184610400c0a0046005882006004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 810440404 1250 810439154 810439159
    0xa2a030506030d21050a180c050111010e0613141006050a0605030907051504080102030c0d180519151805121204021009120501150b09180c1611 63
    0x1060203400030030743c0d42801200c4100003160007040e4102d000013090b081103501280c2000041182050001045030390024160122182d500810050145503401544808000c28600c0280030001940d00c9071a228440908000340c2c51088120020600a40c0c04811755140307942011a28071052101e02035000701058090f030781c410124008001a00c038806d00c2502e000d80b500e94060503101d4034050400008002c803644030380507141c00380b10005020b20284051807240d20001d0310140c0c0d40f064030140343c0071102100140200d502c038004290b0042100001d40c0041007500c2d090801c156046400d080d0910007000540030340072401c03c0101041c0105040034000301314451021140b20202c1c03640b08500c2405050100e01540c20003130005000752070705980400d15450541419407403561907040766150b000c0741d41030658070350b91102d108134181e404e41c800080003000e052000c2820441e25600180701c4034001c000d5020110b8040010801c01d6001c2d100304ca100d00b08801100b402085280341c03803600f038010000000d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 810441654 1250 810440404 810440413
    0x20606010801121e020102010f02071b0e040302031206040b120c0a0e06031209040e01021b15040b070f020f03040f0f081603031d040614030f0d080a2a03050603 70
    0x103a02114100801100c5601802401c1c062100341303149110700350909070680c1103649485054181c1031252004040b0700340a2904030301d01c0c2a04c0d05012240b00301941c02114040c405104010100c0d80c040240c45ca040220210380c00a43c95500028014003590b40000ba03102c0700c407011042c104140010381015804081d241510802e40d00c0304811030741001150280d806400040d880c240a00034040100708051000b840001d500841034202801c982000050003072142d4080300e074180980c810481d007022100b40d00829521450955590007030403c020b01488203200b5201054100c0600038010110107503085400c403500d0300d560307041900d00d91415100e080009515100045400080894410b843c103007215100b5090520f103603001c50301000490504088209425035a5210355114047c090040c951080b0a8014507084400c25090850007100e44401e544042e0901081075000403100d46d0086031000005000c2c2841d10721407084500313503000240c0032028810301c01200d44d0103501003802540290102c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 810442904 1250 810441654 810441659
    0x80c19051903020c19091814060606090909010207171c0506150f190c03110309010e13020702030319180f03080a0c05030d0609050c0906030f150a06020606010801 71
    0x28012141016070240058000881070300c418200515034200403540c40400c03800c0699140703450740441c0c001e01806403a42440c9002d04040c0300711140c0c031304c580074442c0010f08194142680007400358886d402200740a81280c03000111001d9003981130700c0400e50451003c07048280303010003106103075004441c001200c0290400d160a40350700c1e48502449140e014050360854400b0745908030098101e50403a1804810405c60400c0c524510490703009603d0081d1903401001e0407c2c03602030040100c403504200f0503841440640e0250381e20090800c1d103140140c030007410700c0304042c0303200010b840b0701e820294240c80001041c0d0502d10007003c1c0c09080c40c1c001c0d079410030340030f00711500070303600441138840c02c002566546001e10100392042c1c010000d140303a500f44001c014803242d840c01e081d5000030162012641c1d4911041104043c20f000d0a41d2048007000c02d145007401501c0040c6150001600704142140381b2400035080b0002144840c003444001400420390301c1e92810020340c2c4d020104c1d000c6d8000390401000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 810444154 1250 810442904 810442933
    0x40b280e10031502070501060519050a06030c0206151c0f0c050906030a030509180f090105060604180f060e010e0709060314010303180512010f05010f03051207080c1905 74
    0x2034400342c99003c1c14400201c600051410042e4200c01d0081c1d849540ea49000582036503030400c84000303075580c503200d82d04081c40c3c54200241c0120a80c401024582018129091a82e021030860751101d1f00c9414020070304100c4002c02c0018002c002c2c10400c1030b40c0e00d00c580c02440701c031080701600c05108143c00382030135485500744040400140c80042d0107030710803840040020301035800751428180203000264003a403410300c00c0d1401030301500e0301124103003440e041c003522103000e025a9600100c10386083e40b070546400d001c8011406089829115599207056030803120b80160071010050850103c0f046d110758442c03c680c488541d0584107840841e14480d40000c1543c020302840e00c603000340c0d9211000aa1031a103003076a0381c26000b90201e1108901c0c510208030f81e81c3d01803076080f44068003000020f03a640c0c0001f4643c01c41d001a000707800448050b000810005000040a04404450401c05516090546003e03880c60181c2c40e030700c81c150700031507511003542c1e5040010404114010b90417a403220003907244 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 810445404 1250 810444154 810444181
    0x12080a0f1814010615081b0a0309050f06070509010f0e03060106030e0d0903020109050f03150406020433140c010207150b1c12110a050115050907020c040b280e 70
    0x1404101d00041031160791814000c0e299194445901f103040c810360010350800030081e50100e442e00020907a545c03405000c0c000100300106804181500514540c184040040c0c9980180850302d4100018451601119031048140c12184040a0202e8000303507141c2502a01520094030804060301c82d0101a0142d1b500c01c1c0341ea541141c0e0181c4500200901300418403413506845100c9a42510034120003c1c001c0106050b15403041d4024200140c0781c42c1400d43c1005609010f8480c9200010b0444420b10902d560307040e0000400030900700700c3c8910046803c03980542c0154030001041e94408a40182031241042000031181c84102d4108a5288054100720310030ba1019540724108a40c20810800206c504d2900032005103c0c1c2845507107021080c11251504010b00b6086071140d4481c2c0100c94039038488114030010b0b01040301c1003002c40c600100001e688207211401c0da841a5220751031000151100880e482d01d002805490501104820030220300880040c851403000e9460040043c068001001c4d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 810446654 1250 810445404 810445409
    0x3111040b0301050f0406030b0a090c080a05191a0117060c03090d080a02131d090d1209032d0917031608040801050708090f070312080a0f18140106 64
    0x1031460441e420501406030344451445001d400c00d5480c980807001c2901c48024522520047c030b00403441d08401d1814151007200d075800003a541e40304000c60f03000680c0100c5c2800080710a002c440341040c0e030b1402c00c07561240e1088100b0354004260390001c10010300380d13600310a00401100841d0f40c991210796032422248021182d40700217030032030602c140300680f24120658100000071400b5042880e0001d100020450725800b4000900c51000d04046070005403403150390115280e805070541034030400d4040d2a1b2518090010b84590f966000c1c0c504141c0164102424480c4d402e0031629003032800078040f90442002c54107071000c1000d020b00040d400c0c1042c129503107440c4410002d141001c01554039101003208c020030840381c1201c1440003007100c0d170092086600c141411f0340c52386518102401601d060000820f100c0e0000c0e00f14850a00100741001d1499507240e01070318160300c40f5912a240e9a000744007840e888148142862904240c80140c100e1301c1c20703090f001c5c650352a05480c030f8040c120708955003031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 810447904 1250 810446654 810446669
    0xc0702120d0f1b060203040c0503010c030c030e010203010f0e2505070302010b0f0a06180b07030e0a1403060112030c02040e0c0339060c0609150a02070209060906311104 74
    0x1020f00c005021600a550003074030503251007155940390380c0000c2c20f4031303400b802ca0030029586031842c000140c0c1c180200c9000140100c0210300d503505098007100354401d64059841020018004a0030b5050580707111580700200740f11100c0c10b0301c68420020801e50040d0b105400540c20200c000b0720741e1410044c0c040d40100024010000103180000035948102d00c1d1a0714076007440c081c07900049080c0c54100038140340c3e100780e860700000d181c408100062404a900141e0003550a0302c0c5d0110941c40c0050741c64190344034070780c030414488140c0c030b0105c6544910310002500203040041c1c941c0044c00000b00b140149030300b00c003607645102e2095103078220304200020311086924600d4441e07203510782e1140496442c0b00098010ba15201031104510b20303000041d41c50302c03d203511840300c40f504580d2468500d80c0000c4040810b602d05206600003404042d03000e007100e442006580041340469548515142500c0100a1420505543c040030306400c0102c05020344c61180c00c01c0103000e880c1916004442c240c9862307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 810449154 1250 810447904 810447947
    0xd0b010e130e0f071206110307020d0e0604120b040b01051005120603030f07030905010e01050a0c02040b130905010515060406080103120c06110c0f0c0f090c0702120d0f 74
    0x410341000042e10001180203428000c24000c1c40b44508148458405019903801c60b90610196150540850302400c6012194080520611035000d82c08541d00140800c01e15094884101003c000b0318107104590101d103402c094942d2078070400400d01c00d414480d0740030303441515442e0f0341c4809100b0898181c4000c1e4000541c00c0028a9240400010158100364054101c03810703c000c150745c8150340d40c4074203002d8004c21052a8100440d680c0b04000035649003003880c145040102500d805402d0704100e040081c403550700c4134201c006640b175440418190141e0782005000c1680c840c2002d900900301039075502441e5500c490303649480d007000011141150303103039650000c40303070b286441c5d03503214026210041c0c0400051007101d40108109004000038003e0003a0120341c4d500d140c0c20a2450005000404240382d00580745084041d43e41c40300c050002082900d04a40554489500c0302562060b00c07002980080148000e10040800049665a104540d00d40700d0520361446400d0b00c2582442034000b60342d03101c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 810450404 1250 810449154 810449179
    0x8210301061b11030f1b101e27051822050102070c0f060f0801290405030106080303071b080d0b010216081f110304020d05030d050406020d0b010e 64
    0xd241c003006402c1d03010301c2e2109a40018440081e0a0118803c00221203510500a0803803003030384080b440520840481d10108590030f145c40260142c2d80895014860b11031140240400c24022641c9948850756216204800e002121220780702039080d0041502486020001c5002c6104602d9014061000101c103030b1000d40e0a0080383c80301d810702c0501110607540030301903600011024a04040a042e65000f07110145080c41001844c4c0c1800303000c0c01c010050764400401229480001c0d680101041d501d40030002030b0a20744d2148907120340d03402540c1541c40d01000144429010000e50f0040300e042c0d980c003444000b1846048802c884d101c00180980c4800c2102c0c2c001c005482d4040041c2d01c030f040c0143c0b00030118a00c91240401030b15070040a81b03420a40c4201c40c0241042040d98494129600800986809404403402400020030003801565051031000500c6030401c240d412124560809000900d0b081c0382040281d0040d0815a2440c1c2c20322944c41082c1d8024450001d0b043c0000e0001742c250701 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 810451654 1250 810450404 810450437
    0x403020a0b030c04091509050a090b04060e030913020337051509040f06050a150b0307020f070b041e0b031b131409010510090902070501060b040821030106 68
    0xb800603180240b00b2104010028080c0b140b4018222044481e07074480d80300f10b00d441170040c151440103200c401c0f03d6152100d80300025000e07200d03040d042500301000080000448002d0340ca980f254624841d4028a42958503a200102d9001184030301c202110190080080c510380c50100014400f40d48162221101c0d8403c002c0354542c01580d000020f610400928a000f001040940d43c060b41d081c4c548100903000d4034144140ea0040c550000908001040381d40541c0700202c4590009000d8419100000004240154030800210540038101d20540e0f1401d5503c0c01c03000c80c5544680b1408010540e00001c008185010992040481e07100c40142803955580802c460100c0d1514515000c801e030090180c0c0c0f8003000341d090340c1c401900844004021904181003004220481644001d200305901504041e9031940a079120049403480c00c000768403496503150950142c52107800c1100c42c02c101040004550720001a4582c50b02a2040c03280d031070310ba0410716940d10f071000340682404115000340480842 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 810452904 1250 810451654 810451657
    0x5011107050715120905030c01110c030d0504020d050105010f03030216180f0632120307140a050604080a030f05091c05090301020a09080706050c060c0a030b21070b0403020a0b 77
    0x14202c1d1405000100d0081103070405ca98180340f003601c10f9480420884594003007403155034030401300c1d25089401d040d814445955607225100f40c40026540b1040400c0842d160790032681890341e4071100920156031600c5486603001981c0c80140d0051003070f202e82c106504510004001694240e0f030340e01042803901c06280c0c3c054815907090f0303000030750303900c1002611086078469042c031020a40140144c00c46101ca0001c0010500050301e40f0810000313020280349a00002282c0f41580d009c80c0060b2508020103000e0b05068038410050024041d2900300301c2007005941c014881d0000c00d807420071103095034058907011602e044542072017691051060200908808140307810f011454505685030140c1600400d080e40c014100d024045900081c0c180702c8490103100c404058000fa01c0d1041c10b04840003035481d510314010b040081d0481d8009070000032280310740c00c80060381602410720092030040340c1d59481c640150900c1c40c502800791820111300a6540000c07681126001011629120704008960659 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 810454154 1250 810452904 810452939
    0x1030506061c0209100e0d030804170a0e01030e0c0f130914030a0f140a120605061b010b01020714090711070815010501053612060103050111070507 65
    0x1c510306000b03074500158480c0004001d00c0c1400000f50b181c1c0900c0741031200c440001c001000c02d01000c1c00d04c284940e100c0e00311840d1101d400d8980060076854604042007615451407074100325090016901c1c254075000801e051003034400783e0f010056401c00f1320b12107440d81e0041255980c4640c214032074894030f28107041d0403500e6000315140000e04040595401c040340d074601001055680010956001c01030700090910200b00441c10424112000154600740520a07031000c002031050035680f4180b200c41e03d80c050009044040c0205984100c0c1200c43d0480d0001a008030704198205607002200e54400306081c811107591024495002d4a1607003003220341c1e50002c00d52010000444603a103106481084110020f14414000e000304c0050f410030a06c0c9510160840e43c10710008000034052000503035018a0603201d0040401c0450504080d2940703a8641d02c069241c2c031008614400421140104186040340d104500802001d0ba8950341c01c0e46900034000c02401d10341001100700181e40041c103c5080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 810455404 1250 810454154 810454159
    0x1a0402130b061b150108011b120603020607050a022103090105090d0506160f1409011815030e07140105090603130803010f0e090106180b040f091a010b0906030601030506 74
    0x18245410110301e08400000032504143e8460800404038140e004440d1740507080300320003400a510607503607007048a002105d11030300704003105d2200340d840c800f01c1c3d1001015540c0213004990b1440d090920b580d55042102c0f043c0e00c81c40c0500104c50600580c4c1c0c0b05040b200b020900651b041076914401507499800000301e540c3c01c081c020314060000b0340180b09052250945c06810b03120501171f00f000404114044da0041c080c00300311280d40b08805540c00940c4c01004007480c084a8212641f0f1542c00101401da00c4070010a0346a0f034407260103078240e003110701d0718036036041100e402ca503844480320341403010111f0306408070b10200200340c0c45040c10001180d10009a00641d03038440c03885d907981c0d8000e60090380310681018102c6070900c03461906002040e00146090024813081d420404504a05260218001c0c03100b581e07108048950344698101e50441c2c0e40020007040b0010160801c0b0104040c000001c0300c5810300003001185008a0b131043e50207951001e000d4078150750b034110055000b414060316103075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 810456654 1250 810455404 810455407
    0x803012d0530030403030f110a0209180d02010c030c031a010804140712020901151224090f06060810090203061503070e0306010602212209091a0402130b06 68
    0x41003082c024414110942040005565452440c100148802c196440d190304100d0352404d1a000e48500007003c6400b0f0360101c810000640765411407004414000c85031550754044c5c501c20f8403e035a01948034105541541c0c4003402518908681101241c030003c1102031001500c10700e090003940724000c5d0716131207846118002c00c1440c84840c80352400c10b0a03407115018a0201400704210308041e84818010059000700411281040e01c0142c0501d0311000c403009880d81d41e80a121030708000d091110903061048100700e4031a40c4800350907014151102c0003240c0d0034140040000c41c14440c0ca000c502c256580c00c0c480443c0344c02c0004880181d071014084540c491031079000c034500444003030001c60280d0702680320400c041910078141420020160b101c041903402020805120450036501d120f812002425015600d40c091020110b003038002031810410742d4000c0101080c180001e41c0400d40a07070241122009070a9092143c07200c0140443e0020b4001038070000000e4101c0350343e000800207000c003c0c0003d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 810457904 1250 810456654 810456709
    0xf0905090a0c03060603020f04060506180f1017150904200405150306160212070215072f01140313080c0d030b0f0102190c120803012d05 60
    0x30182d42c281e42080e529250754207030401c1140303007503c003023038408409031420b2242d50714002c000f46d07041c00f403440301e010114900358103000c80399034221085401c0c800c01088100450440782000340484419074001e00d10888243c00b0801c0311022884141c02c600d00102440f2035039550780d6400c01c42e842c0512403804000300e0a1107610280e0f8550140c42e210f49503080c1d0301030b0f072600f107942018178010000d400034482034450100042196400f0444117881090a21030668510b00ea1010604285d002a03040c0b0401101046190800284110000340ea2080c9984090122074000f540550f40e004450782c1c03400f01d00c80000350007401158178080c55000341c80c004503035142e00c81da88070421654048084014190403056424225940501c200c07039100c002035461101025600c80080c0d03403502152503d0642d0b5082c02c581804000320071160a010f00502520030040214600d40384640d0382003070203140c0346404614298040442101c64043c0f90300401c040c046105494a000d0000807a080c414000384d4503002881e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 810459154 1250 810457904 810457913
    0x8070c080102040e061903050706050f16242a03182a0e0c032505121e0708090307080f09030d05070c05040b1f030507180f0905090a 58
    0x1410007030910307022003915403405c441009400f81100105140c1c03112041000d1001c00e80c0025400c0c199286070070040ea0b5400c00801d00300076402035500f04803809903440740d00c3d42040001d4107102103c8116040d00b40c041c1480e00c004a041e20030700d003860f06826a4400c030031340c9071090350f07001c10b501c1c0441810b001030100040ca001165206151038241c4400c5000c003249a80508031507035403402c5010300030418070703c9403c085107030103180005084c181c03447d1004004078130703d031149100410a89941c1911102503100c28400a0a80c0d000080d00e02e16404070040021200d0740d80986071a0841c202c001414000d6981040030f903400d203001ba2a6000c02d1106000303560000d20380c400188140c80e440e4180c5601d4500c1c0c1030401d858840c1c107407045020403105100080010716159030000c241c40c800c5401041510000012034041d10401d04040c2e4821000207031b14040940507071026010f02c3c1580e6840ca0000340c20000d0907030b011003d21900c008054615000c100120155021680100000382075406882494a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 810460404 1250 810459154 810459157
    0x507121112191104051f150503042910030c0906032a050d06021b240910020409020d060602011b030e07050a061206120c0b0d110f07140105100308070c080102 69
    0x60690b0140c07004044126146c01c000c441c0320042c0518190b0303000c504400c510080c1940400742c00201007203610101140020041410300c02c1c5007408080c4002a4540050160541500b07807001382c4601400c190049011600c5009050544c0d4200c150003018600c0c002c0710380e0b40400507104070301c006090308801003101d41e83c06405002190048501580310503403800221003d1401d4800d8101c1039101e400d8508851001d030040810040c04844042207941d102104c40341880c55885041100c1d07440083c0100352074416038050a00a15618000c01c10039840d09130613801c13a00000504031407400030419a150103442600580700004900b025681e1459484020a480e10030a0700040d0105540c003044c074900e00490b100360b1004144403001d0002129441c0c561302001c40490040c0040c3e40e034002440c4065030529045945040125200203a44046c5581210000d07044070b42d04598840c0c01d040154989001405a140074080d2180c0918000f443d59039004020750101c04111845480b544000036591420320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 810461654 1250 810460404 810460411
    0x70806010b07020a0503060402030c1005090a0902040e0a140c090112051819080711010315092301030503040b0915040807032312030a020403050712111219110405 71
    0x150107030788810142c4104840c0d000346400042c0030b5840b8400300809a0390000754180d1000c01981c08080c880c4034010100ca1521601074641e822004040c400502c0c1003995008008580c8200701c040b0741074864607124030039241494161118a044200451000006100102402541410460085620510100c003560000c131011003040100540c4e40c40312640c1400300d02d40100f220310b407034803001b04a03584114031030103104c001034400522040b100d4031a90090744010109426000034035900b60b42c2d1602c3d10090084001c0c0180100c10b4426550350241401001c1c030b060b07942c40000b95080a0074589a01f0341d541140400a84c091401c02051a600503804001d00c080c1c07001001400400d802c5d8203020024280b15101e45081908603007040d8841a4003017190700d03c1440303680b007a039a242c488504510290140703400240c4035001c1d8180000ba0142d1905000c03640c14814661051a0921401000001008035800c129250000a04400c1e01030b40342c50b0740c1e612584201450b020706250800800d04542d001c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 810462904 1250 810461654 810461669
    0x3070c1421040305070b0a1409040e060a0509010c02031e07020409020a080708120f07030c0221010b090a0e03030a18141b030102040f030f53041707080601 68
    0x1000c0c0309100b1300b4480c800142c5404980c2500e800c0e5108001002c80d2065000010328036004202c03d949030346c2e0790304109030220659044444e00c1c1440300100f001424240d941c500c056180c240b003003040c0b50001c400ea41c9400300a10107400d8103108810384182e243d010504c01c99005564404a41c0169034494100d0068807844000317161090030046c0301032501d1030181450300c2c00e51050102c84031918138401190f00c041d9047c940030b071400300180f001c1183c480300c0c000304100d074003800020b9003e440c505611101c102d0b0402c070350c000e0180e112324528a00711103ca203000012500100300194071114207030004800d0303049101419410220f1a1101c101d00803a0000700d00c0c480e0080c4c5030600151421158030390220104400840c1741c2440c00300031011100c4103100050000100000e02410300440c10540c40c0c14000c0e014558a0b511080d0072510b101030303880d901c042900c40c11a400c62110709403410f106030840c1c0d44c401070a460300c2d040c105c4210381124900d4840c0704900ca035400c0814401c0060040c5802442e04c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 810464154 1250 810462904 810462907
    0xb01081b0309012d0e061b070201200d0311040e18030906121609081e0a0503030406050f0108030403050d0c020301020c010f0b0f030309060435060a050106030203070c1421 75
    0x89030800c2c416039803919a01703929948464144548500350003030385220780f8980c80c3c2c155600c170b9080c401a0b07502184a459000c9158501480c4240000301091402030861903680402c82c2c03803d800c5405403580598040d01c20400c1d903c1d40041d10b503010b00ea001c440c0b414444000c5a081200c154005451b690084481d00d11049800007400b407821807030502e001145000b030901c1c100140c20b00700f119658000b002074107050740c00e5400500001c0c81c028808d140c141d070741200a4079540e150505000f80070b03040030745043c2c1d98202280000581e0003004010349058941c8000502002241250101d4004a207a002644d05550030403a140141c5000d12038580900d581c4074010501c210712404004801d001c841016000341c004000c510f1130307a0350b0746007200e064414540c00159a070b003200c1d0440170030441030300514900c1da4000b10081a148000150075214100e02c0100344542ea80340c00c8102d040e40402d40b513a401140702c1c0108a00020480a940e0405550100c00c136038100d0341c40c0c0044505900407110b1016003050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 810465404 1250 810464154 810464231
    0x8090d0b070c0b07110a030503070507060e060921040302040515101d04020703170c0702030f062d1612060b030406152102040626010b01081b030901 65
    0x10fa408142d030b00c072500e030404e141e62441141c0103d8590052403001000c1003000000a81c03101d010304d0581d031300c551f0400702c1040006100d604113969490203560a200ca48111507010120390000c51680c0303200711401c000c107800d103441d40e4240710250030040c1441000c4165080003501544404a1504401800d41d96000034040c40d02d8100400f03022100c1d000380140d0040012001090b00001d01d0b2071008424450320b582c564031040112000d005000e4000d5050099449444c07202600044941c00346d000d0070010b601500b00880514001000042c1500005081c840020501c0c05020b01603055a10703c0c1c1480c0c00d21b0f91021240340d08903043c0e600890601c00c408024001404068422035500e846404403806c1c10311b0810300d55090308850b01c00c01c2e4440ba070324000078030704640301c5403c104010290080100c0d860701d8000070941c410825041c900d0f95661801e00a18010341c0b04240c020b0041c0c8010450a071056102e07918403030300e0b920040010003150340310124241c5100c01c511210300c6c2011500b046401496 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 810466654 1250 810465404 810465413
    0x501021c05040204060b031e13080a0908070e061503090c12011d0d020705120c040609051801110d0f090c06080702070b1206060a0e0414060f01021908090d0b070c 71
    0x240c81e600400e520407001c0c0304000104183c0232030503030486000300ca298016078a1003500030308202e1a0400822694000c034855020503004100d030b0080d240040f040d0790a054940310202003044085400560000700c40c8544801c40e20290021a08016040d0a40305868282800f00d030112803280f8086007569512030060404022580034140c01c00040d101914400d804c1c828000e559105500420340705299041e0460085001004007a03e6490040d100348190f598688642d001404100c0ea56081e00110460085000302c0612821f040c202c0103890840c02c02d61002c1e805801083d1181040380340c80e643e404080b020a140c8003080002340503d96818509213071045000341014025030151910f4441400f840840d1107409180310342c0030005403034098440708410000c80d070f500c0031480039603041460035400046070341808000620880c8103403940b0b14003031b421400490356614070003031203114003a0180090300011510343c01881210b0000b0f109440c2145a40c440e4407103190203a07100340c0030440b2241f5440412 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 810467904 1250 810466654 810466661
    0x904020d15060323060909030d051e07020a0308041b0801060f03020117040f0f03090b03090d0201060501050a1b0c030519030318080901120609020d02090a080304050112090501021c05040204 83
    0x40b10300200b40300d600410300c4186001c20001c2d0172035220750321001c00944098010016a0365048031081c0c10300a40c101003281c0d9200310001201c842503005080300181a0720300014690344e849034586d0710300545a40e00e40328140202408515090000b0140b1400981c605017401040043c182c0b5640c0d03d04058514800900714001c018103075000a20f4040030000402d02548041e5030742034015001101240c00341c039089070b42d4011500100c20f004800f02c14018400000030715862502e0040c0c000b0828580c4410040d07900d40108000c0000203003100c50661800700908000c4094076228156054505d82c0300c1d507905050980d08140c2200c0002e15007140001d041d41402040410700e0a00c9640d450504d044e115001c1034070442e60103e0610010a11f1101356028581c00b4000510400030115242d40a040070000694011a88a4420200105c0220303c66a0101c219011100140c5401d80c603548030444c000c000e400140002c0e140c5541c02d109800e10f160098041001c48541100d0000d0309180078410803046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 810469154 1250 810467904 810467921
    0x40b060d0803180c1215060409050a081608070609170c0309190e1f0e0f06040207050f070803040503100b101b0203010c17130503090f0d05030a0203190302090a0b0904020d150603 78
    0x34504201104000c40c5c000300cbc3e240c09050300700d080180e503a0702c42c44100181c160440c100074081d03c0d00261100501c04d5a40c80325561b50310404014010f580154040400d900680924054a4000300a136103554580242c0c0c04001941c140e0000225540e20842440d41c0301048034651a01e50011281300350f888020201000a00204c6c0c1c04120707141040100051040c00c0240028002c41e8005500030500c4410401c40940c8a8440222013515807280300c0c440c0c90790001d2042901030320500840c425290b03c45d0180180350500908048441000e14104641e804800328004250030840c0c1000d20240c1c40c2070044074040c80681c0c1303807c80c1c01031050b29244400c1c40c00800410040612810b4440024008011a94061421601220810b0015000604180440d00018224440026840107441d008806030041d00e44480b11001064000741043e4140d100380c203a515488901d41000707102e8143c0c04000b4016489000d000107060a088210355411201c800782100c060260011003004925418080e2142 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 810470404 1250 810469154 810469159
    0x609151706040803041a0a0e1b09070e0d060606030c09090b010207051e21060f1308030406021c060305190b0f0c0918040b060d0803180c121506 63
    0x110060a025445020240c001000c0c810300101003010b100d040c64101c440401d40c03104a1405040a0505d44002c0023400320034010340c01140f483e80b41800d44000038030301d00c52024108001c29a180c0d2001c54210200c5045150f01048006c501400700b40d06201d0100900074540300000d00340218840905400b1495003c40f040d03070f0411500c1c000690380401c4100c211502540d6851041c8507001090303550229110b2116002403c01c42013040e00810200d1203400c50120605960b026240c0c40601c40784190304443d20b0001074003442c414000030360750350020f41e8454010b00005044c418648000d100c1c40849011040f0303110b89600e001e0043c003809101c0480c0040708a941e505c1d80704096591003481200084c02e040210500d007000502020300301c000c84407507036030042c40d60f002801038005a4903600d00c15502619080c1e13480c80002e0702400c04210700900f0541044003e4116540c2d01c4c20600180c9030200c0e460014000d508652250740c59500c00c1500500700c801c0030b4a010700f1510501203180b03100401552 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 810471654 1250 810470404 810470429
    0x215071d090123060f0a050405150708160521030f0a0b0d030507020f04021323060304020f030c0a090e0f07030201050a08131a0411043b01060915 64
    0x42070f0021440501204005a0030120260b01c0e010002102802240ca602d03079074a0001440e441036545c01002401620310032076074a2108070301c0e04000790183c02588402404510200000b1403662a42500ba0407400d00c6141142c3d1020003c2c80c100803c50441d0010340c0e451354010091200b20f43c001c914969004010241c04c1082c400c0203030000c3c0340031000300400380500c0000681001907440da000c00c00b107000d20141040d0342c1da8000b00c00c20303502c140c1c0f1741c800c003109100c42031900b038811683c2103140d01c0141d8008025501b50389664003000f103605001a1180d50502c81d0700e401842c2e81d10345007001402440e801000140c4000c00308403c60400b42d0315180220150001c1500303100607a000780981714201040e01d46101e1a0b035402c0d00c00c889440c05141c0140164411f8118002014150780600b0b200314400d20701c1444907690304051105079242a40d1074519081050a82992354a184c0310b40418200441c1c07030702164a221141c401e003181d529030400140a5100c000300c0c3c060b051201c029100030940c01d10307070a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 810472904 1250 810471654 810471659
    0x50403020f06041e020604030b07050423011706030102130303030c09050f060f0c100e030a35060406121103010b090108030403150204080f0d0201290f010215071d0901 73
    0x40113401c0469081d810f0640f2840d07a4102992107010569001e5030740043c0f590001e00b8101e0010348113030441d124200420b2803000700240c40d0035074250f07400b000c050181c58108084610300c0e1800700d4900010321080d01994244002815040c220442500460082d00c000420814840c40203089a00b1a0070481c003c0100b00e207280307402c2c1c40c0d20302101e20b0340000d403e406465658080941e41081061a601d4415a080c685807802d002c20110050208583c0c07a16500ca45290f04008072803810b41650a011810304481e25403041c9450083d038066020400030000210aa02c840400031050f82c0060251408640c5e00070440d000c0c1000d01c9600c0c0081c0088500d08041e40c0f400030742c4d40c0d0701d11603800b005140c400424601407885103181c054030003a101c6602034030410a448446280c3d1200030520101c015800c04107030341080c10380b090070b40a00400c14000c41c0f24600b8440b09000400c0c0074050710904510030010f20010011031901e500c2e01a040e0ba96030f148100403016551402d241345402c50900c181e0009004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 810474154 1250 810472904 810472913
    0x506190510080601090905030c061015031103180102091008060301050703020c0d0c02030a0c0e04210c0321061503060501051602120a020909011d030f091302040f030303050403020f0604 81
    0x2204c0c1141c1c01401c0100b0b00380c09900d8183e085010b0301400a5040c482c400034030010005282ca1403058a0ba81d040072003550018180443c182c494001c03c089d2098070030400302d0030b24003090220441580c5804c0025240206880c08200e18488220210000468910900c401c03842d0a000d841c2e00036100b461300394101201040303429145d65442159505104864401504640301404800303001c81e084101c0740001c039910b020500580d40e040710200c849a203107001404108040b4141c03000e62100550310001c240e07450380e170b041e201d02c420324030b2007500c1c04068105c4100000720350285001419841107200030f500c00100e00941a243c007904042c0c18040184181401c6803003807070292524540440751644007030050320a40d0b0409641076400b82d00300444c001000fa1000c01504081d01e5414102c3c40e11a411403202000c507240d001d80c071051001c06400b045640081d18051460852902c2c02046c014501558ad2468103410351045e48100c02080e11101044145070301805503a100c07502c1600a015989040c0e500c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 810475404 1250 810474154 810474163
    0xc09090b09071d060a051207030c02060610051e07051203070e0904080d0e300a0f09120b0601030c051911030c060a1b2613050619051008 60
    0x14007005021074030751860002e07483c00e5291802015000c0d550321110480c0042050380103e2207683c000020703402281065201c0c4c410781c50039216550192806440b2074080001c106505640502001400e20803500611030800001100d504d14000403580d80d0310514110b820700d0395800509018040034410010101e4110b0701e142d40c4854125074041007999645400c807528002c841981843e946846022103909400148040c80d8400b110710740c0407030500301b4050240d03800c0041d0850300c4c025400d00c1410b2096000780c0c16a20014050300305804000d07240c1082d5201c441410702c081c0e0300c001c262000e02c640c030750301071203600800890381c40c0880c80c10b424010702113446007890715104100102020303900081d020600a491041d442c16007a10142d08000ca030a202508004c0741c0d000d04800c10b180a203411a000d0440051039001c1020700034103a40924041d01a51308000b1700c0800090f01855013078001507402e1126512510300108410080303e2050700c01d50840341c2c02000260902d001b007030184400c400018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 810476654 1250 810475404 810475411
    0x390e0f010b03010b090109080115080f01200a0903020d0302030a180302010c0312020f13031e0c3b070806011d060315060a0504031a010608040b04050a080309010c09090b09 75
    0x44840d903032a45c038001215480d010341c0c0542c21552801c41d01034246403c0c5241e641c01c036800d80c801c031000590340210107401c0340d02500c0b020a5450b031402d0803d820030b40f14005010030540354148180480c0c0d4036004110801c440e2441180140c00008800b42a42c0d00400c0121000d4469041c2c4c0075864103550000e8401e00201d03002500380001c0040c090040c5201d5011500710910101e480e54907511581c040300246202800200c4030032000807284000c006030351038514801500000e030032040510707010054944101030607102055821b590b0f5129003001d86403940015160580d82072000b43e140c140301c014040d40e40600403070704104ca648030000c60b004071002c0c100a00d0744112081c594075228602e4502c06081807200707003070b04030f5800f00c1c0011920303030040c001d40101c901030a1040780c50703c00d280d0301030440e00c0c0c00d001e14004580c800004c00c000c81d40402c102e60b4840c3c03080046030480ca10302d844882c0d4641040721406003607910740041c0d10030b082d07020362840c000700004401030001c010620300090070220000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 810477904 1250 810476654 810476669
    0x90203190c08070303122f04081510150e100e040b0a0b18010c0c08010504020120030316020c0901030c0f0e0907060f121a0f120a390e0f010b0301 64
    0x145d0b0840c2d20040b00341c14005d007030300140355000d000c4e01c02260b80b20141c0e000740c0705011403405407582d004c40046210618904c1070f804808004000c600f801581c330108541d000c2214100421400b210540792190305e5215400c0095885440b01d04030980d003000140c0f440030b0f211728001c80c1b031070f00e0410912240c141038030680c080d03100d6046207003070b82e41004940d40f0313020403405085a200c0704000517a03140103500031760150b4001c0c0d0743c4c41141c52008610a214411503100300c00075601c10030009000242241c0003800102c01441500d40d50141c0c80d0006102400031781003070b104004545020032820040c2e0b030341d00c401490303000e403102201e10388001f0180d226074040c800c500900a0f0f60b022129600d104000c90b4000e42082c036001c10818a5100707030180105040c4101074019034805100507407034038203111102c810958400051089449950b03580003007076654080c0c200c1c884001001e026200c00d494000000a8403010302008031649000002841801c02030003a100b941150380c01800300041c800300b100c0c10345041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 810479154 1250 810477904 810477911
    0x4021606020306150409020a031b140a03060314011401120506010e0402061306050306010207060c022206050d0f0203150405154201050306030d0e0301090203190c0807030312 76
    0x1d0718040744c50800c107480180e9108000140109411405038041e02006140b42d504003d044292450724603140d030100501d81c0070815910074401d450503200c004120004007482c0104500e6900d0351803c0c180c48550b0038400d00c90351285006101c0200145c201401000740514030034a03100a520341030b03103401d018010000e460000000050654481030110b0fa04d003100740d408001c0341d1f039885000420f203030401d4440b0360043c002e403040001c03214802c20b44589482e40040020146c40d201010016001041030304800d10681c80d0000041e0994175501a03800302405018000b03e010071510401d403c00340c0d02c024003801d4240314000d001c007007040000c000c002003050f403403201902e80300c50031000010821540341c0e040c04058086aa000c1300304070110300d81015580c80011300e100c01c45c0001500d860004032002c40d00b6510908031079001030700c100d030744100440e800380001403000e83c15008a800c0c1860041c050113651000c5105408018240000b50018500c207005801003034107694000340010450702007940030648 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 810480404 1250 810479154 810479161
    0x3041b0810151d1b121b030f0c0913110a1709030405062206032304052a0402040920040302150a2637020a050c0d030504060b040216060203 61
    0x102d403002da4105034100049611039003650f0596041220407503040c446e6141210304035550310807000c242c0c0d019070903000701c04100b0f941d00c44810301290848607540382c1c051103074052814034171403070710030260404082e80f51940d480304a454040c250210041da02413080c00d5041c104810494040107030f900b41c640484529648440c052403018a60b007500c00944c01120711007d00148203901680b14244420880c0d511900714000e4900c1e40d00150740031a0041d0080d0061010548014807540e800200b01c20302600c081031040c2c06001050480c0c005412080b111940c8010f01034454810320b4960071400c00503070035645841d0a590110b079164800c030482c4074403074001140e130600c80c90042c0c3c0030600e030400c454100c40c80601148683c06000e44141d43c1c03a080300403641c440704045021880b0b120300845905022030b180d000c0144884000754008c1842d8400c2100c28013941c42181d60610860600c0421507070003142c0c40c02e20741854400c8608418010740700724410001c24080f480400c140e112203a400120041c0c681c0e0703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 810481654 1250 810480404 810480421
    0x302061b070b12190902010c12090308070516082a0d0501050a06051002010608070308090d051506101d010324030311010c09060203040b03041b0810151d 67
    0x2007160300b224001040209034075002255200302c040c4030b84211180c1050705000607020508580700000d0181c00a90a800c0e0382021903100582500ba0700080c0c50640340c01c0350b60740c8a0300c504d81c200480840b11074003c9144900382c04141d42c640b0b00a84660400f416401600b444480039181107204070071060065800c0d083c0300c560340d12030303404425034112009100d14500500c4440c010206030160521607803400005101c864814816182a11380f00402042c2281c00d54441e041c8903080354001a84c0483c0c104219400284180041840080b03201249601418080e0400c19190072703841c0804200130921781201030500428006607000d003400e00780010454130050020305200003100c3c404812650034080001050782c881042c030310352a4007100070446114201c01c00c5039241740911448005910a201c00d100000e20740c00150740052141035200801c001c96414110440c1240d4420300c003a030001030b0008240c802d50f008248e40000b8424074282464180b54400b25165400031101e0f520b0342204001030780b4207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 810482904 1250 810481654 810481663
    0x2109230402070f0503090310020c030a03091e1a0106020114010b131a07021906091e0504180219081c0c0b3105030702040f0b0a030b011a03010302061b 66
    0x60b0b000104514843c150382001503880c2d01c9184424020304c00c02044c0d000302c004034400d0f1a42310803104041e42c6880340e5018124090206000150303000d101b03000d040c80c4044811151035000c180705014020b5038041400701420110350503400031007517906024204000796102004241512941d400060301d5078020b00182c01000b0390341c3c000b402080107581291004220300340c0a042468401c07220f5003c401c2485000d05618030103482444007040c800c141c140007030b82c08400340380002888846940d21056640c2c00007001e81d07540e60156403103103c805402c0350a50901401c500c0c0340404901301034180c01c1c80d00c01c000b55119000340556071a42c004150303545a1078407840c09018015003008075020a810101203000d13000c0c00e5590f000e80d64001050b8003a103c400c20070030750707407850b6003003006542841c81c15020b0102808240c0c04420724103503244880740071a9165032113031001d507000d54844100d5605010398250064940b40850202101c01c2c80104010394848040b61880340e204100307034091070420b541880c82c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 810484154 1250 810482904 810482917
    0x5070b0319111b06090118020904020f120a0809150702010c030503090102040812090a15050304031409040c02010b090a18060906020909011202031c0c0605071101092109230402 77
    0x76440d58600c2c038044001c00a00b02c5d00079821440204403050a40318040070f1010f001074001c2d04401c4082c005405490448952180c2180c017421540f5203000a100980c1480f21401007192040c03008560b40040c1d06280d08419650f856803d800c0d450705a1030340010302a072051900040c104000040041c4104e0760070b40580f4000c00440342140d61100091002407616004003043d58007548404c20700080200040210880040303060312103a1447c4c0310b035103048907424114500c440740f02008110f000c2540d180c5100c0d18026120a900010305407100104012240d4806003030b200b03c083c1003000b08418202c5550a40701405d0340104009070300b001a161000290080440140e0b20844100001903456030350481301402c40d20850559030007514030340e071103c0303050b14002c060b60000d602c20b51540f00050b40c581c06030390443c200d070030042c0807542000c032030509480c2c1c2000211106103040403201d1880c501d400008400400c46c0c02c100803010704042e007400e48400310402001d00d1103094900d030840307a15154101d420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 810485404 1250 810484154 810484177
    0x609060103271502131a0f03010b1305061c0506030a1b080111120106110c13020c0c090c071b03021309030f030e070b2506060305070b031911 62
    0x712214940202c2156482e4a10195000c0c0e0b002050324900808a2080f518045d0400b000f440300c45050140b681041402d003a02014441d50170010b409190181030b026600074510030481965401c64803074070403102070031313a07105502031042030000741941454141c100f0607200c2140c07800101a50f55800080c9480d450344006440480e1030700e28468507008544801c0c082e51600c0c4020300400d07800e04c0030202c4501c00c4040c4242d0441c1e00c0c00042c0902440390031318142d0700000c0c038100d0304082c010800096401304a103503606c0009900150752080000b040c00313440001401200c5d1201d5510b080c405c0d24041d03108a4100078200804820b4040c140916203002c0e0001c0c42d0050800c2c8240b000040051000b002c49080c16804070341003403c880e009620900803110022402c0c000b4106030f624143d0030b420580c000caa20b5000412100581414442440101000c980e005500104501e031a504165040c9640d40c0c100e9914070004204014040c08510002c08440440b4900042c681d000e82605140034003440f0070100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 810486654 1250 810485404 810485441
    0x6050102250314060609090714130207050d09050f0f0927060103080d06090b101d0d050d0f1d100905091003140f060c0313050313030521030609060103 66
    0x40d0340d400001340c3e0764441c0000342c3d414040f64071034000c81d03543c0318030a01c40d0349151060766003202d10380e00b4210490322100000c20700141c10b001c07071982d80b2030400031056800c2001424440cce08018034a454413080c0481e0304181c842c140c5101c1c1c2003001c0b07940c2c4d0744000c160300354007551907090820081060302c1000e0403c0c55081503a1840d41c6910700803600e42e11400340d0710003003400c1060200d03030f0200034421a103401340000d2500c0141e01d071066096861202861808543c104d80113000c045549a01d011041c5840c822409020800d6034840d019010000c8840024200006651010010a030000c52940585021140c40e6104030882d94100c40c0c142c80d90f081290044206024402c0d41c80031181309000703481c81402c620584600c3c1908955640000000d005003662011020882040e10b8400458018540850552045c40940c80d814507507440940703071842e10090104200b0034041c092040080e0020750b00e030110061420040990f640b4080500f00341e1285284c04003141d01a8000e0b80700303a80841c0c201d43c251 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 810487904 1250 810486654 810486683
    0x9150308070b0f0a0c021518010c0c0212070f0b160c03031106010503030a0e010302090f1801030501050a0915020a0c1e14030901020d26010f0503010b0301060501022503 74
    0x201118010344442c0c1001c607040f8040740400c501e501030462850b02039402006090404425440c4182002c0c110f841000e1254240d14034111080c0612034207281a51513003402c0b42e48600c140007500d00d03455040c09850300f0102d001d102e9078255001800032180900d500c0b42e22851000c84050300c0750010b0f84002d150786a4a04000200b5030816011a01c9401c1070081d14a03907030b078440034140c480c46164810f40000d102c1c3c20410781c9540c001d902502c00800b0103410030380340c20000f4000c80c01070075050301c031a111070785400c00400421100b406815071100740d201c001e03c00c4000350349d20708014108485e401c1600c1c640103c0c840706c540b8402e01a15a8080d0880940c441204a040c134120404081d000d0a50b003440c3c00d04040c0f41500c50005c03c80c2c4803060182d00030f01c10780c8003403c0100d481034880c0780c1500e0f100803040c843c1c5907100368920074a0301a0980461b08041686060704040c2100c07464444507009904202080000f80c0c0c001caa03418111b00e001c42c0c0c00e10301c0f8503510b03c4591b8840080c2c0000b080c411506050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 810489154 1250 810487904 810487913
    0x4081c1b081306120f090809011805060d09300c03022b09080601050612040206040315020a0f170106050306030a0f0f03081806070c03030219110d05130915030807 71
    0x7141c4004d910750001c12029a901c41010152400b41d64060000f850401c1820940d502c204c41800c410190200d180101c26191800140554007210b080106240c0311006501448034003800703501d103182050503030612341e048500c0d41001c21582c84040e509002c14010804c0c01e040c000d20210103443c040030000f200d04010058500810700d022261000000c2c400a004100300000040190680700024000d03418080c45010940c04a400104202e801800c184400030005402201310840045005005a140c4070600002001d605a07203c086003081803004041004120011007075064a1044c42c0943e600d50f02d04000c40c2c5030002d071070750003401104070303203184020f2048480422800d144a96180c40c62074460b40114607503501d400306400d8040d044003000c030700541c2c044c01901c00c2e0b0501c00d00b405414071071100a0280c1002d0b03c0c0c068400825512790346039903035020510490075007100710300f0b00c40e0400800101c5070400d61214000c07000050b07a00c582858040010324842e200955100b10313220781c0c2c3c0001e40341 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 810490404 1250 810489154 810489167
    0xb010303020d0e0303030406150f320f01120b030a06050f01150912061103010e190e03071b050603070f09060f0c02060a1e0504081c1b081306 62
    0x81a030040c05180c0d600c1004a20070300c0403402d048001001035041d9161501d07102c005020315030000785a4903403441c0000e80680c002540c00010410301001522440c61603e12031841c814103207046100800c1c800020003a5038642c6a07207000040c00786130484101001c080010002d203800102c00b0380c98468a6111000c200650700000d20500b000000c10046981e69480514028034441c852400718480907000d0088148000d51200d0f4203020f081d002c10380754004a1140c901c0e034000e80050380e07180c070007004008821980c40300340000b402c0340c0e54040000c0055100300d10b440c3c1c050900003c25034618845c481c0c40290a80040700080c14000300000d42d60704020001904800c801c074120808a0b00c400300c0011610301039203210400000c2c80d183d9811840c115800c004080d8000d030340c0003051018441d00503100307076600e0001075040780d0f080e100d5a54450a11000703030701d02000304040381a01e0342001b4800d50349a9020380c483c03038810010820002011a03038034080b0ad86008044403002d04890810340011100c0d840b40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 810491654 1250 810490404 810490409
    0x51e0a05060414011b08160503040e01180b0a0605041e21030f0c0f08030703021c0f06210308071b062012010b0a0504030507080a02120a0f0321090b01 66
    0x302d80c403000b411190300950140c0c45110000c2c2460790300340410325112032407803459140d032231048095030314060b2544100c4503090702c20382003404040c103295030a00c005401d620410b40c10000440350391041d1890510000e240344118029103034420003051030341c071040d055007041501408203d1640e8503410550080800742e0089602d0a5002404602d01c070030f0b100c1c6c0205114088c1c00d42140e640c98500607180c44500c610303440684102c0030550300700701211044c40c5015007082c2c00c29003007002145003040b038001c40c000d95106412000080b80d0b441400c840340c40f4004442c00c001603260504901980c0ca190302500d440c15400b0711107081c03c0d150900f610400207550310400354811000480051291000707204502d602850fa1070300d0000c4503c000601c481c0745280c018014100b000d103091172070039460740d86031030134004c0319484080c09a00440c0000d04500d4040740b001c583c007200c000203184000d565158032601c004c0094001e001d0000c4201c52100740d605025000b81c0c80403402c00d0a0240e4903c40ca45011006c100b417 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 810492904 1250 810491654 810491657
    0xb09060c0312400f05150106020105090f1015030209090d120209031914010f020310060e090a0902150a080a050c090a270e030d0b010207051e0a0506041401 68
    0x200b81c0b48403030000c0210700c400c020050012003040d01c41564000043c0e401125090300c4060b0141900c00010320f0400c1080e00301206d1868880165142c60300180c20340380e0141c80c00000d0780050500c00440c5400090701481c0a14001c0042440c180068110110030140e4002941240c0742008010f015000001ca03046070b550660b50700d00036451620b00d003208074041c40058aa01da044030040301e900500716454944014002c0b03240c110b0341c540d40403c460860f0249806c80d01c0ca160080104000d800605420b08010403131820440045c030381100004112841c020060b110450f601c0500d03200790f44030402d9246403400340d0300407144e0340c110091000e0041c220485101181c541090f0001d04052408400d40300d8041d00a445041002d080c488541c150710000c40c8400081940d695004580000c03901a541c0e0722074240000e15901c9000d80c04034000c0d030340803003c014195400740300c04004e5500c4071158001d207888045150249417544200240c980040c65000b160f01c13072008100450f0180a00743ea540f08800309 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 810494154 1250 810492904 810492931
    0x20106141e2d010309020f120c0405100f12020d080a1e08090d030908030a0905010e06070e130501060203180607060609060501091a030103020d1407030f120503100b09060c0312 77
    0x1040c0118141e44460320000d4020074280030301c0720301313052140300c09404403800c030149c1d1954021344000c034080b11812541d410803900010300410056641c00440b00c050f101c000721a03512130342c268010514160100c3e000425560340000e410349010312840b0030101600c1e216502680301146004001c0900205071000720850141c080c060304814000d22039103003015841081d031400c60340c414405d076000381141e00003a54155201c0c1c0003159240c07000d001061066040c0d803100004190300d00144900b03043c0780300b01c40980601c0c082c0180050307a000426100170200f200c0140c0c592040100101b81c85025415000f40014284100031554100d290001000c0d10303400ea8888900a87d0303820325181000318808891640d080810051001d03081c10f901c0581d000c2e01540ca649820488000030300c0c5031201a0340250b52030110b18140718204280d44a105002c0d03121850310f5811414150f1986c00c0c0304a4600c165001c10310009040da506440d030b030003650f50300051902a651074086035100252103410031208a1b03c02441c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 810495404 1250 810494154 810494239
    0x702030a090e07021209041509050a05010602120d050606090d060c080a09031b1118070206131a0601030e0d2604121407021215010501020106141e 64
    0x48010615204105507030042c030510b0021900d220740c3d07030302c0b094406800523184c1c041c1c2c070801481707074560f43c0c001c0c96082000075040c075000c1c2e03010080f1030040e0814011504400405070100c00b0442c2520442c02003010001015241d48000a5691181c209a03e8111405185c480e061003001c0c3e0000140d40b800c0d89501840769200b40380d01d0308940c800800240420f12500310103209030003842942a01038805e5680310b88100ca01000500c58203104200d4507021442402003040703043c2e040c065242c201c0d840c0c2d100c03400d440c0c000d940c41c01e0703902e04240c00c000c24023446000000c3c02c40e80306c2c3e0002840d030031503a000d0300c0114500c0240201107504400b00a0440d030000001311865203140c8481a01c100d030005124441940600e400b21109a54001c44500c000700911801d00903950300c000c143d40c4140d0b04030042080803404400400c880c10143d00c0207065901d044020060140c44103050407400c001101e02240d0079545104a042c800d1807c0f00701504030503841b2401e4861a82c0c03840c00009803003200140d074175400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 810496654 1250 810495404 810495419
    0x60509250207081f11120103050c0405220302010b04020c0d020c0d1208040c03050303191518020d020417032802100b03010b18060411120408030612060702030a09 71
    0x1018401d15199602103990848a0f140315403502000d80a00ea6020810058542240c0170b03540200d1800500d00030303600010410050b003000406580d410542c0d091141d8035115111040c40f410110312914040054504001018404c0d80f1800011900600440d1114007032040c00e6030706c1450104040152142010303141d01f6181200c00c2c0c0320200d0b801800072900f042020070451b4007c00190040300e00961040002c4001001400a144541c88240c04081c20704a42040941591425020f600346142001800c1c82801c003806120340f8540322083d405030383c9265081b1030000078400c2d07502459a80b1224000f20f0140300b408030050900c0340260601c00301e0f811a0200e01180c40b0b06084404000d80e000c1180714004038811b4210000c05080200001484840c0704080b5002141c401d140c0c181410000c4c00300f04040c9001c6c4911100b0f07040075004541480804482c0c01404d280180018015010220006c0c00c940c3d929509140121408401c0d150241084072010395280c103d0310001000c80c281e20340105964 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 810497904 1250 810496654 810496663
    0xc121b05060711160510050c0f0c0f0d050a06150506030c12070908060f100b0d05010f080a0b0408030c07150b0f0103090206070210021905071701020f0f0c010605092502 74
    0x4d000151001c2c020300d0081000b1000326404228000c0c000180103000740002c2c2448407001d0400326601a0441103908d80404c6109000341d800c0b2840f614241d401c0d1004a4400285c01c07031541d602840000301c01025020644225860b1b502659005c000001040348516414015102d0101031070b503141c500303441d80b9800360f0b04000f081c0200788445d0f2015001903019030402a100c0d40027440300241c014a40e0302d072460b00c01a9803020b2003001c0d50a40383e40041080d0000080e0070710040c00c502000c4d1068032000e42e140300e00e81d100904040c0416170048007054080b011001281c201a43c0601148000c1c14504000005080b542040d640702d445410546410f035402802440844c2d58000d04180c030303044950303080100510250711150114400c1148040f01880703c0d16103501980d0041d0006c01e201480d006401c021701e0a85030b41c4140c2e507401844034090084d0000d055031600341a41300380540310800d1010301401050349901496202d610041400032210301d101e026030b00b81d00c0040c034200503080b90070b1003070340e45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 810499154 1250 810497904 810497923
    0x20f04020c1b0402070b010617071e0507110d0c03140a0b0106110106051005071b0f050112020c03071a15100e040e06070314010e070c121b05060711 65
    0x25900200b44084800c021448a80c4000400034001820701a941e10b0740118a4003d0b007180380401c0b04040e01d0b20341480068030b49a4091158640300c0103003000310030218406014100c20f50b0034040040303080400c0040c99103071400c5805002c1e040405040301802c040350110310610003078600003500c41c030001e0030741e0000c62035883c140e4100b1401c440c00d910301141200c1c8a00d0745100c44605560b101c0f4086641c0e5540102148610020359501e5103464841c202003c01c0d603030141404500717601c4140c0c00c000802d60b060442007285c50900f48108007403c4010040013a00c82c801c0c48001da0300000a00c1010040070380b050b468106d00500c0c9070328003a0760340312047e00950004c00f041a4403441048000d40790900c40c056260038000094000304a284402104900e00f010907252040881d45584400741d00940c140c00182c014088020b41c088a814079480183c010140d503400507144500c14448044400c0c001d6000d01c004205c010345125907031500d0700b005503c1d04400e40d1a103000860000d41250603400000d080c030003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 810500404 1250 810499154 810499177
    0x3090503070812100605090f060313150c030c0e0901050d3e0103021305090c04050409050d02010c021c182310030603230715230a210e010e0a020f0402 66
    0x142e4040d23a00401072282c0009101200b1580380d0024080041e4051440560305000c2c8403000c11501281d400180507070783c80002400800c40f4400e421002e580c0c07180300040c11941d096904170103c03021400d2083c80c1001c040a60340320001100b078542d012840b662003081042c01091020031a080034039004506030700c039031200c40454030a02740d4140540e141c4001059040200040c0310340c0707016a40e0000c2826165016002c0d500ba40146501034010354081c041c01c41e8001482c80600b803003081d02a82c03450800030142d500020071002c3c40504c200e040c40c650030800a03200007818481201c10200340106903081c082d413800c0c012240c1c80202d902942c0240149010327203510082c003100680100d2a010b0364444400c266581c2449110000a08556001e0360103100c1800d03552074050010b914060121486490340e842c1520800070449a41403d40c015080000c10410f042c0488110400200d50405844581c1c4801070b15440c10000c8407043c1c20004029030b0f154404e66100d100c0002203002c0100724012255940d0307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 810501654 1250 810500404 810500419
    0x3040b0f0c0903122a1e15090c031507020a03050702040212100f0b0901120b011106010f0e1b0403150f15030618080a0309050307081210060509 63
    0x9101140e000122680948003401c51400c0a00190001c0e00d0039045159440c0300701d0001590702407000c21085050041e004510b5507250a0000301c1d2695601d80302c01070301e078001444041081c07040c10030511020403440310b4140c51b410b2500b84481e0702d84e21000803040c2c0621034072884c640c100c1e103480d208040504c5001d0b950050302443d02d10381c82c1600d0a42c08140e0890340181d003002032095800800300620b010f0f003000c643e1038071040c0c00d000b55081195100d0700148607a40060040d20820307030b0700600d02d0048502085c40464042106001603c411460704141000b50041c2000414541a0412400102e424240d0400e6143d1601c01075600c0154404048041380340082106002103600089508280c0c04003043c0000d2140c00581f0030802c48060044c40165285c4044003001840903600403401041400c0522500c3c20603203079a014212300c50912548107150b114444001030020500546520a80003800107990b0388030300d45c246401c080b0498402586141d4103001140c41445402660185500a420074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 810502904 1250 810501654 810501661
    0x3020322020f0111120c01020403020109060e1c051c050a120506102f0a0b01050306071d03121b1e030a0827010510120c030210020c0613140603040b 65
    0x45480226003920069144644115180e850007004002c104c03401b614400180c07140e0440c80010003115660b4410020819414030182c040d545051b01e10900903c41c3d100000316030f805240442c1480c0a0b2981c680007004942c094136140741c0c0000c001c2050f01d034190785000c8556039175241242241c1040c1c99840d00080c00701c03a41440f9501615100d034070410b05070715054002441c5100e00090071071181d170a025980001d80140d04200e02d124919000d80412005044240740c421001405032043c20b100c823503c1c04017440300b001c0f9a101800034091260074401c060340e40f56040c000f00c0301e4170005070402e00501e10a00391051850040c000b501070001721840055440c00c000c0150844980e14050a14043c1c141032828400070350000c0c500d00005083c0b100008501031510010708000c0d209541d0018041103c103007840d000080c1c50019040070b41e03504403109282000c804100700d00e044100b105040c1c220900058000341a20044015012105901d00a100e140b0380d102c1848a80c0c0403e5070b00078154050070340807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 810504154 1250 810502904 810502907
    0x702010f0b1c02370f0f061e09050a0e060f04050f0a021e0a0f0e1215090c0409141209010c0f022e1d01051c06030209010603020322020f01 61
    0x4800c0150b8a413040502d54200c00c0249039a407045155200706204502c42c0c0030401e464100001da07000b012015480e00480c1c1ca0484c0c068003510790003401d401403084128940e00301c68060481c1101a101c0600900d105585801405151a00030380c4c1c0713513103e18030014020301c85d894903000705481030303181c0e0212003120b442d0303045444040c1d04144024601c0400599041c981c95824802130700d889111075845070788088176200003403c0c0e4003404020a00469140c0000c1400001c00903030400c0d512024010b102c001c0d40c502648030b00f00410701130210791107400d004d10302d01401914074408085513403207000c0d030b003492a0303501c0702650307600c1980b0010b40420000c08039180801c0607181080110750000e884040358608566072003501d070701e0981d191007100b10040c1000c5e141035403180c00c600252425108400d0aa000040080e029004100310507141d002c5400d918504900144c00800040d980a00f803440c00307503140c100160103500b00301c482100b04e8149191881c084c05800038880121900640070010b0301100500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 810505404 1250 810504154 810504169
    0x403020a02060c150a05070809071412070503030705030c060a0515060a1b1514010305060f09070f0b070303111201030b090a0f20090c040b0a090308030702010f0b1c02 73
    0x41c070b001d00810301a904e004000c898543e00c00d8226840001d22841d010401a02109001c1d0504040b1340c000641840000d40d5940d40040f48001140c108141c071070030982040c03a19607c0d4100e150103000201d0000100000080030305804c40002042c1c0780c146e5a8403040c5422200700f04c9007500681040c81d159032860901c000108003161062030112076525254030381c0095209000780c00c481148203460083c964811a01c0780100419030000e15075619403468503556601e50002d40301040031003c0c5004200c80003002c0100c140100b00442400001c03d5844103126804d4001040c241c000c42d0502403008845600c80d0100d82d0400d03041104480c41c0d03420764071402c0e04400010407403941440350718101c0001c00d01003c017071001c0611030380251103449140e89120610812a0b07010a0042c40c1e00c41c24841d40c0c0b491042a541a50001200244c5480081c90100e90000060344050000d403400014080880e40c19082070311402e603550f0003071203080c01b020140500220b0705201d15225101d1858641c006261088 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 810506654 1250 810505404 810505417
    0x40c171f03020429030106120b060a0513090510050112061104050a09020c12091e01170a1505061303021e09010b0a02060601030204030218090f030307050c0f060403020a0206 76
    0x40499441900e82c0c0c04201162103104c0c518000b0144082440104000303140102c1c1d0100c8140c009004c4c2e186085141c0b42c04e2107490750002c0c200504200091036035203d80d4404801072000400c500d5809803241c540c40c0c01003201a00513107181c05214140b0380101002e0040a040b504103040740f0780c540283d074480c4401022019500880401c3c2003000140c0c0c0d0b5921040d44014140220006079100d03100d0800ca403600035104055a042c003024400307108546d541180f112010070541c0001112001805e004032580318100c07003000c0b028030961042c442464602d6000c4d01c0e2103101c09030301030390040c0c0b00c07001c12000b0b0140008500c03070400a40801e00060420b036141031700c80c0b566044440ca841314100c0c00244ca01c1401d802519292401040b10614a0b5041000c5a0801c4003070030218909800c0d60081351350090f412440898218003180403030000e802c00c00c9400400b480c0c2c8010b4a8803414620304c010419442441003078502c0c4107002e2034200c149804150301d030080307901d6001081c43d18010b070f080c00240d0f000300c4d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 810507904 1250 810506654 810506701
    0xb04020d03020c0a180b0a060c0f14060c1b06011a18030a03080402090a1512080c01060303021605060c151b040303090504050c121f1211040c17 63
    0x104210342c2c80d10b446981307001038200e65015a8005007076450381000c441085c03681c184a4205104100308507504855640051504200d8003c01c0c00100d003000340304280d00c2d800020701840ad03070b01081790820640b03002e0038105d0710644600c01c23024450208070350f64520a00915800c448004102c44031364140000509a0811813040c81c4000e02e203d10019081c0848910250049103418080104515203585050703802905c07124200100e124449030a020788689000f41c5444803450681c140500000d0010340b17501c0c0f88610000c0c0401c42d1a85002502d40d07802d10306801c400ca80009002c14185402c07000e442e558100e0300e0040001c0d180d110082006d04001601c1c0c01858900341d0089030840f0407410051001c0e40c025140c046c0401c0c030b04000d110407200004c2610245e0f400c00d01071090f00814601c00142c0104c4000030b4070018a903070001e6404080b10550041108070800c2c0c0d122400c100d502c0410310180002182c0c00c0240744801c2c1e4003917600c2c800c03004001440c141c0d03410001e40382c4580e044032604286400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 810509154 1250 810507904 810507913
    0x20106050d140c031606050901120e0a0302010f0911040c05090307030503040602070b1c1a0a060201091b0f0b0d060e180c1009060302090d0803041a070201090b04020d0302 75
    0x6980224000d00c501d0300003565408038011840701d1160b42080510b2500605800511001d01440c41d1010041c1c8580178600400c40001200c0c44160300c1008002c41d8400100c00400056043d43c0302140d484048240490155080c0040c001c50040b807445490390302900100440413041c82d600c2000000c140d050801010300509000d0110561003c00c050005148070300002c5540345e082500107440c100107603109401e00001044885411820418000075080034034001051107668120714812290340071004603041011108001411541500051101d0b03009000e26aa405413000758a40c01100b280503504514403452400c12451590100038148080d15407000202151a201001400d20081d5182782d210707280310f5034810728010140900d103007a207001c45400904150001c409811201944510310900d5808603170555103491307400f03003030806603401641540e403483d10345003244416080b40c601c401c0c203030503280c0010807040c01441902c0105070041a10403041d540c030390800c580d000c06070008034210700a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 810510404 1250 810509154 810509159
    0xe10060b2505101103040b010506030601050a1803060e0d0305010f0821071208063d1404060314090102040b03010e0606091f11010b0f0d0f0c0603020702101d0f01020106 74
    0x490f00c1801c00c200381c1a1a0b085c0d59003001e080c070042c10729040c2c106921608040003445410780c1c104c4101e031000545802e10f0980c808141c50344802c08400c90344090420380c206480e094030540041900e071440c203417a8604000136600c0b040c4210401c0864050100d0580c80300d0fa4002c0380725444241c04102403517013120207191040c81d981c0c08003c0202882150045411581404000d140c034024101401603000c0c0703244140c2070580c640310704880d4050010f540e840c18000400a41500c544c220442cdc00b0100c528150b0368aa4901001b00240200b039284050305100f0004103c940070f040c001c4a04542015888605603401c0c240a410f4814004c0c1940d64044410802113107280c88031205810b9400801803403034240002108003030195000001100340380e0b45801000c2c000c5079038100700c0d07100c424410f42d5105000d400520f4844502c400c1c104000c1c00c0d18100c5040001c0086d490740003000e4841c4240c03208844201e0343c08080d1050a010a08104000081a88142a4205411a50b1590070140700102e070305075 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 810511654 1250 810510404 810510433
    0x5060d0c03060c0e010c03122304050708010b221a03010f0c02010c020307020307030b07090e0c0c0d0813171b03030a0605010f050417100e10060b2505 66
    0x26503903802228056101c0c0b081c100003d8220482864080382030034082c000001c9594018030000b082020004019654400119442401c2c9110180302285141601107400c060420380d42d100702510820f110b96003007010410840c01c000300742d51030391003000195000082e00500742401034440c03442e003c0490000850400341c1f5a409004500c00452800000250f07d50240d9000742514402d01004d02550300401c440700c01030f1000104c820840c4d82140801207a502c2300708040b00d568402d40e1260301800c512805200001c41454002d200c0011f000d0300322142c100d892401940c121500b202d1310421701c40f20031807001c0401c424481030041c000c40400200d2070b164010403101e034030804030264002c541c0d1000c41040b006007803d22581e0003605003401c01c802c030110820b200402c50f210314001c460100d00c80b0003100d0400c3c401089021080f0901c03017824007160030600c8246640c0e003403124184202d00d085c950300180c0b07483c1c61021580818200c03035503000001960300000311403065032031045590f8400c299803c0c2085 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 810512904 1250 810511654 810511673
    0x109060e0f041811010503061011030d020c07080c0109060f0509041104140f1503010302210a0f0203150106090902070c080d110609010c020a0f020d02181803071505060d 74
    0x111084880c6103190a0f440c02c1c40c5850380c20a08626051040030814056030303170303030b0603181101c00ca0082c40e01c21803006524842509501070354a00030030141c008101080d40030404512041036406207c211030380d41c948180110f4205030584241d0000c1070381d90a4a00c05240305100501070103030f0103072001c500c0d4481c500005040f40e000ba440140c4c8451001c1d04441d032490a840001c0d540c070001c80740701c944880302064580c1c2500c01848004c0c4140b003c0c3d50a83c000c44078122a00f940403240c801901c41c3c64441c2d0505c001d818100d050100c0c440d000715149200000340d00300900d4144c0d86580d890481e85400e100701103000390f1141c0400d44194400d49000a5407080c20003481c21098032564036502c030289214500d03803810501400303071000b07641005421700310141c0c001603800b0007a0308400c2d078280c82c40300e50001c542076003e0104081d4008540c40c80c5800841e1264000a010321803280f0800018100343c0c4e006074680c011114002c201090000f01c26000d401c05401c02604a6001400300c1038a58841c0da620911 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 810514154 1250 810512904 810512921
    0x131d0a0503041401051903051e0906011701020c072114030d060501111911031539030a060509010602010902040f02030c16052a04060b090109060e0f04 66
    0x768400a03007441070703658032103d40303c1607402802c1490504069800d1a1060085200100105540e42c80092121030b010702c4815140f2040c052600680d0502040c0c16031180c4003402089080e0045408440d030000051085403405000e1001411080d0b0508841c80c104514050191191340000484d500110318005244000145081c00540d96002105080004da59440c0c4c080741c144801d40c00d580000010101c0d10842500b00c1301c007a10451405440c0c8110345100740b08a264162107210408881c00100c01940c0b809007038900c08001400e8654128907240c0210003689440024540c110702601d207482201441c2c1001403401d0100b001502d40010600801d8240e06c0500141c0d15035902c042035080078800d5800081000700c06614614203c147c0719401e201d004000038409480c01200801c0c0302d400d211623207401d04a40001072008840c04030b00c1a280d901d005080d4459443c00400003a94a1280200c0725569010303101c1c1e0510038034142c4207541c4032045113101a0865220b90300b40c2c955980f6885001030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 810515404 1250 810514154 810514163
    0x30414121308060108010e0d0e0a0b1809160504050904060b0414040b0c090120010609110904060b1e070f171b0a150b010e06042909131d0a 61
    0x141d0701d1404655624000060740058101d924001c80c58550240c0400c01d50214002828810014a0104042403c0c02071691050130000e602048242484501d2600c00390002e4044843e0030050301d0300c0412040c28401601c034034010420801040201c0c1c142600000d5000d40030325000185604041c0c041426100d40d0700d0844e100303065280801040185200c1c0315500002e9603042c0d0340c1000c403100006800c000300b514014650700702c81007021000e510300f504218042c1080034801e02a00e001410704040310340201e5403452240f0b003032500100d4078250b0314041c0c40340c0b507049440f00c165801d08000c8980c090f40c800314080d0303508514a258440401d00c41000f521000760003101e10350f80c99220703c1400c05160141d8600c0c207800c1d04006103010102c1d1110a002c611940507c40001e160045100141c2d070f0f042414480c2504141c0100340001d90141d41c6410303020803081c0315440703114603100c102150700d0391040520080d402004812552011182540702502403400368100145840700251158600145008202d170f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 810516654 1250 810515404 810515437
    0x1a16030804380a0e010c03050106020f031806090310020304082109060105040e25050306060907080c03040c0506070606060e220b01090f030602250803041412 69
    0x810403074a000309455000c00040c0754440c030b90780310041e00c10180c40c1125400418200300080350340c0c080700d0340c0071000201500000f001507411410028001d000240f0448016004000c0440200d15010045501c520850600240891004d5007000069081019015018403e02c842e1001c2d000d010703c01580518000e012540e241c0c0203602c400f50300300c0c201c0d005540d0030035035a41c140928844005901c0d419500103d03000304980c000b40c902c0030320b00501c102200f80030a8616808404010140c400107007a1a41a000d644283d0b03a1407040c091800025921100040e09000000e9000c200f2503000e540c20078490b07249a118541c2c3c4400241c0c01d81c00c054410f446060b6600d40030051140c101106050390302c2d00792908a000740441c021512078650a1046030103168840724008502e1780b1807112076010340328400189605c6030b200c3c10f020300250000b100c8401004104280181054011004500e135158810a418a990b640b66540080c0c0c0e402401440d10b50b1090107040a900c6c1015005488011f1034a090700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 810517904 1250 810516654 810516661
    0xb090a061805030d0e031303030c120e1c0203161409060405010803090d1b1814330402030c0d0501050d0f20100314100f1a160308 57
    0x1110001c8aa290403995480341c404005180070003503550200d014000040d000001902190640c03094400c040d2140002d5138000c0200b5401c9001d03003400b58003851001074104c1110200361805121800c80d0740c0d01030401011034103030b0f00ea10400960b00a1001e8162a1035041c000c0c0e008610658a401c40e020030035480c3c1a00b00130703080c00103046503c103404403001d116030b524055155460344a1105000d00943d00c0311020418000924180b0070840c1c5004640c0c1d0f1425940c1c40200c900780000500c040f596410510030b68902c880c0412158011000704120b4203044a50000c0d0700000c1102807550340071010940d02c0d2881035540e5201440c424509520b506960f0f03202c0e00d4201c0111441600410700c100c03044202c000116821064240c2c1e0a41c1c0301c401c0000705401d0141c850100344d0145107013644800d46007954221990b054005400c100031020214030350780c54810341c900d180c400f103018000300f500300000c08015035003090301080c1d51078900c0c1808601c0d040c03005130005284480da074000d502044500c820b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 810519154 1250 810517904 810517913
    0x62d0d111c05061513050904110a17030406080a0e160f1a18180405030d0606081b160203070f05010807050f12180105070201090506070309030504120f0b090a 69
    0x240320442080c4104814900480003c4d00101041006554074101103400c0d04141c00c040060005090010302c0071690740f030b01d86800d020010b503041c13116000300203504000880014960401541302c602001440c00d0030f0400108449809000b00014241915202151440401803000b184080100180c12004904002140c1140341040c0d0004030080010200d0900010340d00d01941c180701c4481550b201c06190500004600384441c2180340e101c20755000c244400c10000200404810714040c60071300c030080d80c440f4143e40060341103d5149880806044038808585044000c150140200c1000d0300c0050141d0042445d110301500300f1002000301c032506110f5980c00c2620a6448011032408070700d44111803005100c0d50140300304000001d401800418502c0073710a03020072650541d000200154030b04044000e019100c0c0c41416912409a02d001c5520a03200b030203031440c0160591510741c5010318156005900c04103084081c0c4054000c542008002404040307054000e0015100420300078245050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 810520404 1250 810519154 810519187
    0xe0a1a1510202d03070f0303091a150d030e010e0118180605030a030c0605060609040e0d090e06010c020f030309031203070305130309030308070e0406150806062d0d11 73
    0x101d10304441c10100b030380301c40e4000201c5c1e040c0c0e513000782130815035902c03860260080c04030040300626140500b55001c124927030388050305225104441034585640e103224184441c00c1070a100183c006003442031076080950045000c110160018500840000c1c0b065110b00b1154134035800c000b0280c40b1405411200345081d01540010708403c030b028140c101c07915600900442e0100380000c0a5544802c0060340c40d6480c4000c0ea030003054040c2041c0600051042240d0300c4842c180c001001090302018046000c2c5103150740e5611400741a101c02c0c50704501d603000c002d907450042ca40d059045c4020040c122031514284064000b51410101140d101d0520201c00381c2610001070000440c10f000c560a103010030341c4411000110707905030400401070f4544000488443d610142055007050412000151582c0f103804080d522110355611007450762a00e9040005504c620103c840070a100360906252200a80c82300d6140c82141c640a10715062040d02000d060780c1e4903d0100341900d0340401d00f000009003100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 810521654 1250 810520404 810520453
    0x130b060319170d0c030906150e1305011d0604020126041401090c1811030405032a010e210712030b040603060e0a1a151020 54
    0x40151405002402070896a4084628080d240d6829a6181034050b1652000c940d08101164418000141c00d0342d006000b80507041d0b42103c60a01d0700b4036601480041ca890341081d203010202119403034941481392010021035980a85195580f001030400440c030000b0024040c140342405407001e4503050001401c00c500ca0344441103107404150242d1034448000c0c001542c025441803198459002c281038140c0180000300c0018402001020045078400c1c00c0c007951420207551010500441c4088a4004100c0c0001d54000702568800e03c40e00e00c42880441c01e042c240094000c81c80c4e04003c035640280c0c2920508910000c03c0d80ac007107105509441040d01c210010704600750401e01c0d0801c607540f0300c640d419581d01e0010805030303500c84050882da102d4000c1402950404411f00c1092003242403951102111001200c81c03480152080340079840c90300d5014458018070014030301d1039032041d06002c080c641d0b8004003810840d0302d4075444070079100030101d003110303180e80c1c0c00a0003031820002000705d5003510403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 810522904 1250 810521654 810521659
    0x70c0504060b03040503090d140a0b1b27030109170a030506040c050315190b031009090f08180603040f021e0d022106190c050301150521130b06 63
    0x10804c20010803000012290410700507100500448030600f050101e0501c1846047c06501030754000c0c1d004d21400b283e9180c01920400020030241c1040c40d00e0300b59600c00d64107241784201c51032258484140c1c01d19402c074079091000d0004152103006949400d544440b10103041001c0d100400d103003a541d6032510400d0f51040c3c09890030440007114920180a03404010401d1900e002c41d0200c520f00c43e1600160400301c9004140500840d5413141d00744d640070780049a480c0e40c021642e22303000505040c1406507105050300400341d020400a070740c451102d10792005482c06080c1e040f001c0b0740692911900300030740c462805101911440c40e00e5204000d0420010740d20030004400c03642b0003040c6591004007005030160704642665122000e00d40036103104501c001400000d0044004011803091b0364280300d07003d18402d101c1041100c0c8960010b842501007030146249a0b001200c1c1c00b000c450064005042020040d09800044941c412600985100413075a603033201030192203407030030000003460058200c00d04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 810524154 1250 810522904 810522907
    0x60604030803010b030402010201090b101415042112030f0506220e0a0b15121f021b06040305180d3801030507030b0a0516050d0b0303070c0504060b 65
    0x80da2289641030206000f100f10b5840700001150071a8000d60100d1007241d400448040c00b441e041032108400095817040012000c1e07403200c4041c071032a000454030b80080b0a803111506160030408a1410855007107c0e4541c2c442c0f002e50309001007000231200740b000404641c0c0104020810310b444000751070024118601440c24689410b1000300c0e0041c2e09007002c1d0244200003000c00301c40c680c0502e000c450701c0001d00300da045001440702509841c00703d1a6107400644445039607034000384403195100c9400ca034204500c001845805500d050075001000025100700c0c034111441c0019006608101c0169812400314400040340368222100c004800e442c0caa04480341880d20f90b00d0745594403407a240800441031844221010704241c01120503102c048c00103404144034560316450055034440f005d00082e1034540506000440006031070046134410481e80345103084103200d18405840c10741110f450382c40e00302d8440f018018107403410009082e01d50301440b01e40020b60b16040c1488102c5032143c10880326102d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 810525404 1250 810524154 810524159
    0x3010f240f12060302040609020306010e031515060f03090f010e03070309181103010602060403020610080c09060a090e01150602070305031b0a08030a09030909060f09051504180b060604 81
    0x4200c502600c41c0c0d807032818690b08800d0a451104002e00c443c2d04000d41c000d14104000c130381a1019809540700307203020703294100104009000c1543d13500100f81324a40c241d15140008035030500c521440d002c89080076005c1c0d810243e660310741142c6c50b08101e170144c1842c1d00c25061084504400d0045895020501c4082c605c2c084245e24002c000c01c000c0e020f44020781d0100c02403119040503a40c070900c180d41c01c3c50401c0d5281d58544100a4450400b501d0960051049102140d8000032046503401241c0e22407000f4040180801c0a102840308003c2c10301d60301015800001442c03800d10301401469444140001405a400c0f04021104981540011085611041003440010f1b0004101d84004814003180b01e40300251460b030030319108542500800041021003031044480558000e81c00302e0303202e511010078964880c10010122941803244004d2880240010001801280d0003280c10a11100d002c02c4a0000900402c064805842aa202c0b03520310340c18040a000d082c40300103401c010100c94403440d03d80f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 810526654 1250 810525404 810525407
    0x2a0b0c09060a11160e0f1023121e10021305060c0703060c03020409180c15050706050108070f150203040b250b0a0f050108062a03010f24 60
    0xd88142c60042c403254441c00082802c0411111034082c5090101c02d010f1900c070701c2035000d0744138141d07411000c00790024041a80c0ca150172212605403800b400d0300d5490790003003411401c02640840020340d040000030340c0060710b0400a001c188034010007980500c040300040b034180d601c0c0106c5440c0f050740c224170512003004854641070880c01164002c65405403200301c01d148181c100220340c0d000a02e1503140c244103082854064020300100c51910004104c1200d00d04801712000403903d800410454640300d050041c0b8031400082c1946030140d251982c20007141d560341b1000c07a8020b822401c0c1a600c000b00c100511008810400b025107540c5807941c0826a1414020b03549020317a000740055860003041405d0011060246040c403a003032055402a024814280180782c201c09032400e420f02410030f800c0310154499802402d04072803648005201e19a503007002c1025816100080c40280f00c0e0504644280403c0000a14040c01021941e6803000740b03000642d01a00c0e900c0341582c540201e02800e00840d69 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 810527904 1250 810526654 810526657
    0x280c170705060f0717190f09060c05060a020307030b0402030a0e0d020f06070e06190c05100b0a03020607080c071805011203020c010305100f24090e162a0b0c0906 71
    0x11940172021290b4900b0b0070308182400d014000340e43d00358414031000300171a143d005140322100c1e030280d2140a1682e458440444030110f82c00d4000d46070364001400f051a00b14568002c50f403241942c5400201c074528240040d007a40e1003660307039407107841d1075100307002064900b40884c8240e0a81c0303000034481c0d040728035003050315190014000018482024000021038036040c0032101c5440707221001015401c1e890a02508211107040181c0b041e2044441800340100c0902c520304c0c0106004041c0c5203094595030800c25540c1c48442c1c100c3d5100c2042c0100a504a010001c2d00090700401852010b005081c41c407110886105911081600030a82c1c020b0001c81c0e004550215071503000c0c1703000324155070340c040d41100064880d8018001c1500001c1c0c0083e0000089a149a40c0312140705d1030f030050340030131070116403010712402407243c0b00c2a03110100b11080300020f0a881242c1c29401c00702d2080c001e10300555041015205c500e083c00f800d0b1956101086000c10b8800d600044544d403150601c2c2008000c650a03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 810529154 1250 810527904 810527917
    0x40c09060e04150b060d1d030a210b102007050105040902160506090d140c0c0d0515240907080613110712080a05010305280c170705060f 60
    0x101000308102202c9030510313000115003240c003602207a0f844800d03500c914001d1018910100307649500c6040050224001700840d82c003041d01d0b588400004580307a0240001000d25600006055070302c1102c00740540740c0c03440e2802a030605842c6c40c0b41c0d00451003150402d80c010000072b5549500007050500c500d0f0707000340650b82580c207581d000580b078480d403078031000c000d04408201070710760300c608010040c411400207049201e240c5583c0d40d81403c0c100c00c8550183c140255031069401e40c10448000700c03603082c030380c036042d0865028404460442c03c40c01e044411111040e42c2202c00c606107240015141f41841107120f01e2a0000d64003040c40d86040710000b800050090002031040c2d41240000090041035040b40480103098038440e9501d202514124020003100c40300c030303c08220248009040c150b1140f18142c1240c0d041400342c418210008440c01d500e0110314242c800860114895102090850125501038072080c0701d0030408030a081c0001d45440040d50000d44106001c01c030204455000d503007079925 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 810530404 1250 810529154 810529163
    0x301091a10150c11090405010203091212070507080403080d0f0606171b0d050f06120d0c0b1b0c0f0708160504051b0a02010501410f06070302010203040c09060e04 71
    0x10945408a402ea400301ca0301c540c404801d0041c1b00c1404819802903010b00308080489aa46a5614050540303019807084580ea540c070f540009a0250300860041000b1441303207012501d45070b1242c0c2c4a40300782d0804c1c01069207059607081d244040b105c09110781790103803501d0300f403150005100500d498a41c0400411b0346800721105a038280123056420300342d40e071420f0802028080791800c1d013503541030711808841842c4030b003800158071100c02d030010884841381007155650030761403455502c84428000001e03202141d05c200b584100d4030184086800f40034441c0e405806004001d9004072400d04d800d00d603400402960700940d03c0003252000d290078107022228141c0300403800d42e4641d2507030641c100780d490042c0c094a000041b80c00703104e42e0643c407050513a40c400400380c410310012002c018040f4003136551070891203800a2036030901400c400c8000403400009049064091311440451060f070403a00c030403401350b074000c400d120400c19a017920034060710500004214903880c08582540d4030708058000780 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 810531654 1250 810530404 810530417
    0x60c0b0a0c0302091003050411121e030721090906081e010b1507060c05210a1d1509240a060e0c07110d0507060f020c0301091a1015 58
    0x307204900a0b0161285000c005107049407102500c41c1c050080d10702294211200000c1f0580c4c0050f91174141590406401800000d06900c004041000c9002d50020120709080c40140034046c00a4a14401043c10103041105503500a420b85000746c24488580c104079405402c005080c0301002000a0030002c6202c01074500c200c8180e81d8a6a0b4010b10a020201e908503049002c62007c0700c0c0d08000410604d8400c110402080300e040c0b074120307103900a4041280c152035100180c6140490701e07548154000110040020b03404d500301c0040f22070003038482a040d8084d00000c02c031130030403640070000b141d01034060b6014010030741501115040980c00340d182034940045040200f01209081d03070241d00a0b160304500981c007820152654604d80d08004070450345801d1003507000019040009803201d500ea44140200f1029042890940d50403500100702400c61007002a40c01090b03409000f04480035014144501c206003d4030800418150018a0102c210203c41400c000c01c02c01081040580003aa28000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 810532904 1250 810531654 810531671
    0xb09061501120207060204060c150b090c091f0210060e0402030304050d0c090c02010b0f03160302040c0c150509010b0a0308030a11072003010614030a06020a0203070f061401060c0b0a 80
    0x2400b07130f000041e2105102003030100c0c0c4550000f100803401d5004105015810b2092640c40e07056480400145400401d48800f0510b0040101c000e02030501005220459031003143c0340000e00d0140c603900c0040181d0241061100c0310901d1300c1107501031300308985801020300e00368005c01d136a8404c41c460140148079940d440e2080c17102401c9441c0160441700c1d1b0034040881c101100902900d20807004600c00d81c0020180b60162a000410070999001c610f500440c1e0703071841d0200b100030b12241c1a03440500c001c4505010024024952808640031070300305c00a02c1d8203100030210308591a0010041c0100e2018a0502c0858001000e0721b0317004c80d000d01d001c2044541c4c00102c03007860085420040405080f215070046841c20b080382d07041c01070005d4000300b2161f659000d14003080c20414a0880e0142c10550604000c14210740050003400c0007401202e18007403488d078404c0700094a250050390826a501403144503c001414218010106032911450b05001070712140e11402004d848592500e941d0140c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 810534154 1250 810532904 810532937
    0xb090102040510050a081e04060b031006060507060f0209010c060e12070302151b040306090f020901151205041505040c1a120901090c0608180304120b09061501 70
    0x126400340ca0080c0043c40d8074404500701900a801840855012607100e4000880220f018806819440100e0b001c16282e500c0703948030b44005106148006405024000c00200301042a004410082a079507903025502d02c040d0070030b00c00329050b1408a254043c010000003910b03030f910074034010b82e4541120300040c00540c1d0040d075503d807101c102512516150041040b4051640100700380d139021850070000005555802140c000344a40d20030305845000061000340085145540700c200024131840040c4080101c5400050040e0700036802504c03c8070080e0b220070103090348044001358500020005000714106a03071524004280040d48020050380e441c00101407001c0b01c08000d00174402914004c061004105500d841940082000c070006d24140d80404d085250503c0303480b50b400e801c026040c07256420100c003115030703010241030a030320320a590105400742401400100001c012143e120346d110703001441d201000107070003460301d03526421500c00c2008002d0704800c241c03842c0109207000351840403a803c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 810535404 1250 810534154 810534157
    0x3090321030e0604052509180b060a06080109020d0608030d2f070227070210060f0b0f031f0b1801210b120a0f031413060c0c08060f010609140105070b090102 69
    0x80b803071040c02d10070003004243d030f07001c500440c003401a24270152940d60282409025480ca100d14030001d1140c000410441440340d026000c00e645112000c14034940e200080e519640003200c00d42d001c40d0782e81c2410700980e07507250140140ca9400841a003410000800c80820b14011844042d00403400c2c2544000400301c003c04c90600b2078109040d181c594201010001d5507600800640c1c20424682100402d000d18494880411142030980c032a00e004400044400139800c09401da02102031017a41c100304414503000460080c0001c100d4a981703c81c0340700207500003240440a982d05005401107003060040403417501490f50480b801c00460b82001503004901c000c04041050358007409242111401c0140007000c502c4018000d5846d8843c8401d243c4d461101d600c2a040384042d03018012604000c0e0034020306103209a0703400781c407000190305d95402166003803160480c0c030364416000e4500140405904405018050207800b41c651103448245000038109200f00000500b40f8184040068807840c030940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 810536654 1250 810535404 810535409
    0x117010e070b0901200102030f1602070b0d09260d0b0f010c0f03090b0c010e060a0b091305071d06030d02010b03030909060409060603080301090b040b01170403090321030e06040525 79
    0x400031580c03454560740300349c00345e0000c1d1441c41c10800c2e41c0045940980c0b0001c2d2590517103901c40d14a9291200701c1000c400204001e5808881e04c2d0b03040180d084130700c10100c00b0a00c0c82000f18100940d5000700e00c1c4e400d01190750384480b40f13114280005005601ea40d10428888289a1100c0b1680180301541419a810f80030741e404145030304d070300040c02c0d6591135041d00b0400c001c540303034130840380151212081030081d01d038654002504010444005a450148419217029660048054030300310340e201c402c203800340031034a107003da00004050f0a04c000e508040002031007040803840204801426040002e45a02c100c1c0000340c411418131010841d03a541c0c4d940580d90300b40d4452402c0041c2543da240221503600f091080b00845441c00094046600b4580284d1b06208416914000100002d41001140c0e10000d00242e0420014000200000e1a14100c01c020349111091180d1110404e100040964500031134044d51504600180000520005280520100c03003400001400d881c00403980f19100701c5a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 810537904 1250 810536654 810536717
    0xb010e04060b1003060609081b090403050415030c1107050306161e080702062d093a0c1a1e10030b180a030e040f050117010e070b0901 59
    0xb00c42080354190154000401c40c4c255441b80d00000d9648d8040640b206960100862885250071b0140079600e864403419510074440c1c01d01c5e50815803107000340740c80740032440c0d802808a56141f4050040e103801410b41401b040004009211090918011903211400a0129451114112950481e840c01607071410440020804106014503e8440c0201010400d0344c10344098020341000c5540c1c421405111003070f0392030210622055100e0707040707584541c2d000100881114040c01c1c0b204155140c2214480541138580030450700e420701582c204140c444c0c0102404414010461b28050018080005145d154148514140d406598440924030792241007150ba642698042041028036800c203119001582c0c0103841c29071540c3d5981e03104502d00752381400c504400b54802069100000d1058134214a82c2d00080c0000c5611500d81c0e0500003551003e0304001c0c4e291031170000620342d130182440f030417030389600a40043c0030040c50215565890710074010098100540d400304c505070000211544807451510 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 810539154 1250 810537904 810537919
    0xb1809250b0f04060806010c1a040327030b0a0b0d061a060d050708060a23040605031e010c03061a070501020f0c010c02120c100b030a020307030f0312090b010e04060b 73
    0x14900d0035250f4420301607000820859400300b4810b522402c01c1c5800030b40e0041c3c00300120700d4840703032920388458000c104408100803c1c042802440c140080da404601d2580388424000b4258506071710700e40c0b801080c041c8101c0c501000e4030316956828400242d02600150001204403d050903140d0503111995003a13080800060301020140301640120303c100d00640d10304c4400e854030b10070445000824416101c4240c2030b40c4d5100702c1c00da030210500401035402800003518594510209061080d113508901c0b00d010750205020056600380604000c2c3c1c0d04900d41086414104030b4018004100c0844080b4401004140c003420000c00354100c540d0300c951040c01a4a035201290300710302070a0301181c0da400600582100c102c2c4141884141e82c0060b0356030010700b0184424056002c0200080c200641e4144502c002e00c8002da2010300070203001d0350194071401c0850722142000b41c010f90081c541454007900c1c2c850b100020071841b1103001c0c10346120314042882c0f40c03030724108240580280e540d5994030030f95 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 810540404 1250 810539154 810539167
    0x605040f120e01050a0e22060e0f0609010315020f180f010f12090206040911090108011202010f0e030c10050c0d020723060d0f0b1809250b 61
    0x909000040203071062070382900d00c00041078201c4103240042c90481c0828003c0c8401c0c4802c50180756a6244020068803d807428107002c014030700c200841c0c0710f45440141e503a503018808804c4101d0469406508074004c90410b0400402280700c4400c14880501a03408442000c0700b401c070b0540459901085084480f030300c0c0c4200c6100543ca0125080450380720360342c441c040c0015035000700840c4c1c1907035089444000c42d2000c009000300141804c001c003260b00182c1004081480103003072042011700005c031450140c890035414005001c550041e040444c102006490602c0140c0e4000044070000029140c42104207450301d012074505509003203107075480440003442c0d072141507003d0081c14882c40410300722424002001d900380d89a4013140038160b060240b82030261501c0a254681003155107020704804e00d000c441070380410403241042c203092203554481001420a00d01318950703a418019601580700c041c24403054840d80c420f04101c40100100390b034030326a5240088100d8aa00810200e4051941c2d0300303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 810541654 1250 810540404 810540413
    0x304052a0103271202030c060c0301060e030708190c0b070f020906010c0f0b040807050d09080c0a050f090c1b0f010e0a0803010b07110406180b0603060a05041107060504 74
    0x4030300946040c00079280548030f182d4401901d02d41d4464040041110910441c075844408418652081800031341c8010004101e001004110861058904901164403541451320092001c5040003046210b0352210200b0301c151140800c1141450104107003900e216605440c00e8141030940f9441552000390109000081c44945016415203c1c03084607822610b984108c0152280440c00030054004105500b210703000803440c460345a04a406001100c1c201700c010781d2154584014001d5030070020340c10717036010000080c0421203c07450388011140020310b2800c090224200d00d5403501031a102e44008070100c3c03822518982110f90f41a1691503180c01e19031055400307551003800d40c1581100f13600c1c0152541c0b50780400b040b074605180e0302003152841c5034a004410096074100031001d032001c54684039051840c0e40c942c80342400428200100714204c1d4904458a42103461840840e4046c1e9010400c00150390ba0b02114641640d008450000c0e0180196800c4800e50040071001003c2a103044288070501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 810542904 1250 810541654 810541723
    0x2b020309070603050114120a14070e0a1406010e0a0f0b0a110307021f0203040e1303020d0201060e0a15090c11070801110d0506011b12090506090303040605030405 71
    0x10003101040741e03071856803140d049045034024440d40741c2a152001042007145445443c2600f542c041e501120004040c644841800b12040c2e0207050560384559010040076030312140f901c0c2c0c00712080d5000c002420f0401917418030108010007483c100692481c0c107045503070368030f83e071000508142e461098019843c1ca051a0840c1e2081d6040c1020500c4800101113a483c00011070315900d9000d0032480002d03400a00b100c0c010340c0c200b400d00c01503001c2400b010502803588505c06225410024904c001c41c1da107400c01a04102c0000d040004690500405002500480b034500e500603240324400210b007012800708040c050300d139800005229090230403d100c943d50003803803d2408801d4000303455040350748100803400c03510721460031704064105000002d440e00c256801581c2c00803060400174900304880c44001c0c20300300f07940d400316125071200385c480041c658000c491402600301915240c0c50500c2901c0080c0d500d0046104190800c60008002400c0201c01e114001d4582c040130b0b84416500079207408151030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 810544154 1250 810542904 810542911
    0x20f060408040603200a2a0803010311010201150b030a090c090501080c03190314040909031d0a0b07081b0a03020c011d09150102010605060a020a020307140105030c2b0203 75
    0x2174141200b02000b03138010703080780c2541034250030100e1a005036480140c50421512030241d035580c00540c001c064150048a1101354140305807649a039a604615103200e90203c040a070604580c900718103804080e040d0b0705001d09513548000d20039241d030354200c1d01c40060040540010b10b5622038090010710a900744d0800ba0684240000f501c0d01000f404090640d1000510507820f201d045400c60500400c0c003407055044c440d02d803601c5d19880c15480e4a60f01041d0f480388002100003a0303c0100894040c2c900d004507145548040b90015800740c0b030302d0000807441c0105440a8140703d4002103d0309901c07501895940c403170074804207854448101c3e04010b502c1d941c2040d41c06000c5081c08415030401c2c58200c0106440080007400e80c0c1e502e8450348411618001200c006074195940c88801152070360b00e6002a0501007da540145000c090300c0c81490b080529580c030498815000d0406680542c0c0c11409803940b00400080b06900c1d041c0000003060445c115107032005120200509000716001c103a0019480f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 810545404 1250 810544154 810544157
    0x4020f0621160807080c090d1104050603030f041403010e1e010609020f040314010b060313051c0e0d030c0c0f03060b030604031b0602090402040b040f06050c07060f020f0604080406 79
    0x182540c5100b800c81c004a42c400e46070000442c0000080c400c1c5001d000c200760004584299203050026440c04a90030811301c03074089e54280d442d110f01010a240034000c0c541d009100340d01940c00c00d04d120540e43c406024070b0080c040d03d00048030070b40b412502c00b50b02503043c00544034101c8101c0031140c1ca000c505029010640c03800d43d420400c01090352502030003180c00b035000f0284a07518084c0345807541880301c4000c0103043c1e269529000c4e0080e655640034095800340d07a908085011069191911a1420364600044030295141d0360300d40d18a540c00c9001c540d03007a0020303240c190204205180854490320340140c01840a28a400085007084446400000742c034440c0200b0031a40303001504242d80d46404481c000d001820085d1003241d0250706201c00c03a2151302c94a000350a142045001074203030b030020b0708110344802001c0341c100000c0c0c060b849050b000300007906003180f80007500d08420352a40940e020344d50a100d000c10500241500c00c00c10b40c4404010307142603031030904181c580901d496000380300d500c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 810546654 1250 810545404 810545467
    0x20d0f0f050f010c1403062d040b090402060d090c030c06020d09090b10050c0f0601080c01080121060b0d06050a14010b0901020a061d1204181404030804020f06 70
    0xb030031588144503140c0403000d59203952a081c2e07080c00444c2101d601c010f0426400c0140c54414220709403550a4501d000203040109040d00e4039504180011281d070003000e07600c590f076440e00b0300c00540c9075031080300c0810f0520040420400791500700070706040783c0d41c0d1009003600410000001c3c042d07804200003054850940e03a19180907900d11900c0180c901c1c002141d54000f41d4004c0340e82003140036030000d08028018801342c5815000c0a28a5824481c090740540856000714074100100d40e8031082c2d8501402c8100c03082940503451a15902c208012070328014442c2d560b0340d46048560307807003840c01c4808a511000c148824030300b02c1700d90006806a003040304d400304201c000114140b107042c801d48609000603030040c0301c0c0c40419259900681119040c02c4200c40d004206907084003c240400b1070703030035181c0b500d00d0740e100c1c68408040248664164280c44482c5000c05491420000001d0300e508260140f401000e90344030385c00000d1400b2070040c006c0764018000111040c00024100c919941c08002c100142c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 810547904 1250 810546654 810546673
    0x403170d02161b1502030313030908070f0e0f0106120f06030c0b090307050406060203070b061906021b09010302010c0f05070f0f14040213150c05060c09130b060313020d0f0f05 77
    0xa41040320440c0c131000140c1c10a00c001a1454025078080f041c2d14000c0c5800034820baa2038464070b0070f010194103e190300040080b01888551782d8210080d03004006151202407661505da802800407020086031604d690302e40e507140f0f403c0807090700400050350300b00b50314020f0280d9844113070b0f1a0303610440040c0d0007805460000101482c05224500c101d03982074024618090090340c40c242a810003c1c50382d81d020005404a910441c1710240d83c1014040503001818240703080c0f0b110103901101c06060341d20850070340c030041c40140d034020340030f5030305541c402d080040001052401608100036500000b07000b500d02c140006003021070f0501c20007281c0e00004a040542103040600040c0d20961100340c1e400a0301c0b400030409a08002031a04200b0f04a207040301400e50a9a80c0900700b00c01602c01c1d40300c030800498010b650b807038040c80c44004442150303401c01c1641010404122503010082c001c503107030401034490100303548030344418419407a80403510645652461600759005e5002c032006aa0320f00c03401c0f244 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 810549154 1250 810547904 810547919
    0x1f0903030f090507050d060609051531230709061202030c090f0310020a030f0b1210020c0111040806070e0a0e220f030806030606060403170d02161b 65
    0xd078450190400f0142c24a05d052005205a00d40d045804851403541e480000802d010340d40310f0f103409000710580400c03060a155040004114507800c410001c6a00c0f94840d4044204051385401c01300400040428141665990f5070826500410003080c0d50020001300f02c48207074002280001c0c0e851039210038080309500d42e0304038101d0004444040305100100204025440d1882e81070b500c070140102101c551804c12444c840c280d80204030386c0b10100f9107070b0000d2513043d4104e000e0703d418000c0076588009441c0b0750b07460450359404841c000c40d058aa0000d140b510501c420340000b26005102c26085e90750781d590300c00d0b00b9aa5002140c00f4000103810006955092520032018411602d01e005901e155841d42d2640c039000e0030140e0542c1224484940021000402c009003e05c1c00d00d01980b142c0c12940383c030f0010702d400e090303004090340c0c42503000300070520016941c81d00840700c900d880000146c90b5803000b2500d900030b06c90300c00810140f151070003403002003040303800e43c03140020b8103042405821707540c5445 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 810550404 1250 810549154 810549161
    0xf11150708090316020d06090c0b13060c03020a02090411030706090f080c01210207290115021018020612010f080a08190905060a0f0e0d0209040b0403021f0903030f 72
    0x40c1602d0f4402042c40c07030130252030003001c2d03203084600483d80001c2c040d220f0b9503034850f180341350703030100c2c40c1403002003a140d07440b143d040e003948000c1c482030030030590241003a9002501c601503000002d12802090002c5070500c011031a49090010014046031201030f255000034100d44450311400504100d0040e0108800c5000701c1c5002070300d401a1034400c3c400700d40b41d941800500c0c0d4900000340b015802d0010340080f03a0280c1305444216541a00100c5200e9010102180c00ca4160004500b0080740705503031262642c0012010303c0140520740004920707016556528101341074520103540004040350100f0002c9407441074904940300c5c00000075007603584540040c0c82e1209080080e0103a030703017400345409210300210800c401c16a1894403000c2030307803070b500090020340202c0710001c00140140200711046170001d540408610080b02c9400d252540c41d4000b403002d9200400050000c0c50300da000c102018001c12031400c190f241e14131407101c01c04c2080c1d1010000c0c059400b054002a0510100c484131030704510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 810551654 1250 810550404 810550417
    0x1704092901080402092a0c0f0d050d0c020708010e0309090f0c18030313091b030e0c0103020919060f320a0207050a090209040b1503070f111507080903 66
    0x1c482d400c0642e030380c3c1c00b00301072000c0c0102181c40095a082e0617155003803500035461703030020b40804404c1e01c8042111844d864003035032803240071048d4045950485407680083c152165074082603c04244a40450cd0803400c001c8107602240c0558201400c61440d203070044054100d107442601c4451456451022004240c5010758544094032420001c035030311350545c90406000c5440280c00c9030301d00398400c80c08181000441d4800400b09640b00516160450119001000150341e844e060000201a0100340d4840c159041c3c881e050507800241c0c1d40309074440c100c007401c9000d00d0003079a005003582d130040075094048140d603800002d1000c0540a000c00403a0314003030b00c501007054840003140c449a00d10b0300542c2c0003100b02c409602c681c0100140315038640030784001801d08240c016072140c0d80541030006640700c818649100c0d110490741c0e100019103620550b980400c284c80e085142c680300d03080c00d9812403101c417140000341c004d04060b40490107000c241ca40c085c849070b90701c4082c5a03840c00d80b49501c0f0b00074a03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 810552904 1250 810551654 810551657
    0x606010f0e19050d0606080609032b180503041d07120e0c060403210f1205130f0809130203070c02060304151b030b0105030103110405041704092901 65
    0x70a481c0c401c6040081c960b21032000154440941151160700058850384444400c864182d04c840c400e2020707420521445401640c170b0301c0254141904403800ca0072441002d0705108110003403409040903002c85412440500a52002c1105c0c6803065003003058030780c1d010780204039011255055400b50f400c0c5501d000351040c485a615a101c01c0c0c6c44409a9000d0038442480060500c200200c0f80320716a201030017840107511070f02002900c00c4424000104a08802d410355003802034044c1d00c10f0b0300ca50080140c01115600c04000140d0359142210162441c2c50140c001d060303640b920f14644100060000248050300040740e0b210240c28101b2034940507480115030140024540000100060820300041c0d5001072140f803007403002865140d0300a003183d1000d84210060104034401491440d010b1044504a00d003c1c60500d28540c15922380124126240c101c0d54040c1d44e07517900207010701160080041020007920a013650b034545d82c200510180403e5400c0101c0c015074a0001d1448010702208040e0b540d41c113 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 810554154 1250 810552904 810552917
    0x309080c0105070b15040f0e030a02160e01031202010f0f0209040506040e03090607030309051b0a0914060616021518040e0c010c0219031b0602030a090506180616050606010f 76
    0x400f125817444405001a550300700e40c9446804028110901940708200c0c0f20700b000795140c40d11080002c2c40c00c584982c030380d007180382d5060007881325058182405d410341e0b03007200c80c00b0298201d4440881c0140a5143d44603c2140b404020b10400c411a400034200310300304440610203a02c6845c108003c88020421062850b44100042007403400c4c07280203801c00c6030083c1070014844525494003400d00840c07103c2940c100101e60306003115450002c22880c0548940d81d800c21100c2a11383c0c1495201c80c015080da803080070003181101001c40004070500032030354058452118010140c8080420350404401c060070001c004403644180e040a00c1851034550702c440003041c86504c20310042d2151940501d047c1c0c0c224500c1e00207a421141041c0d0f07001b0041d4402d2119010700d100c51448003250702e03880e801403821900104145a503540d48540c0080c00d032107003112925070310510030905e158031440d22303410385400c910302140c0801c2c01d95802030352071007450042e02919000e90f2200c004540e01c200040185004c205d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 810555404 1250 810554154 810554161
    0xb09060d030806210115080d0813020a090c0215060612010e0408070209010f18050708060f0406090e0109170f0315180a0c020f16060302030c0f070309080c0105070b 72
    0xc03681c0000c3e080f46001c2d091420b075600a09198141004110701c030403580c0c1d11000f03510809102c2180034030043c80741d43d01901c080080c04e8001400c805010b0101d10b04101840420002c0d95540081d9100901d0300755002c000020001c04080d407125250862007218100303840004126007456812162114240c9418036680d80c20880e48042c3c05601910030b07900601c09101500c010b88882400358080d01150801c21402442c05103d42d4070019445040c52102e41440140103a8640115901d42c126000702c170303606042d10703030180800d0007000c0070b0780710000e000d06080851100362019401a030f48113004078080c2c08000c0301e1000b00011351188407541c103140030301080020308080000c141d100102d000180032084824552034254202c1ea8155154804550755204004130140c042081c03002c0040b103240078001c4580c601c0c55400a420321032290b50b0516400200051004110b00d04440070a0869144240c0303450300750500416010540c06248281d124104900c030b143d41c018025150307010303404500c0c2c00d0384d030340e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 810556654 1250 810555404 810555407
    0x7080a031107082b091410020109080a030e10020c03030601050307030603170a081608010b090619020f1b130c050d0f0e191104020304020109180204090b09060d03 71
    0x31024501e100d800703500008030b9a00400d101c520074003d10b0011001d0310406844410740c62441000c161802e200d8030310010491080c0700280c0c6020541d0844243c80c0791500030320103a007d000d1104004142c60400106034603259016441703210b184903001c0440b4543c80341c0c81440c500302e03c070b41e03100d41400d03078414400280c0640c03250005580c082c0140c9000f040c0195280e56035000c80200a03070340c0c0748600c008a0b403040c1c0700d80d20040a50b444000300f10702c8031100942601c0680707041018064141100c400140003550354440100316a1109500c500c0c500460340c12810094580c01e10980b69001ea0007485560811600e13460510310510800901104107000407017810402460380d0b0040d001403010a2201d043d5100c513600c200d01300c0b8010f05101084a031515004903050050700480703050100b84c0400300e6000300b40304090200c08000290740040e529103030341c00140c4035025581d00080c8080d0303800302c255120300c009802030412070740c50020520400f8106410401440c104807a05500701d0340e401c16140210303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 810557904 1250 810556654 810556667
    0x406020708010e210c0105040c150e0906010f090e1005180906010501051e030708070909060806130f020607120f030c0819270506010807030f0b060a0902070b1807080a03 74
    0x84c100e40700c1c0c149460803004445080d40d00448043d108009518401c2211940074149145000e0983ca002c288040c60b810029001380c5015101604008400401c0c170045d0740a00351000c041d0450b14581c02461034203a2100d0100e100901038680640300d2440340104110401040ca8029910080949010fa080000440b15074020850509000e00d032031340a03400c0040144021030242d803140c0e4400d40c1901d0118405400401e80364024400c143ca000b000b0412400b010802c907820001110f9070402d000700ca414540030004c0301e104007960080c80040c88500b0050b559140101c040d00b41c1e00d0701c0a940a0f10601a800c0352000403200011481c1c180000e005054110440303584014910400104045654a55952680030f220325507080407030106401c0a001c0204080d60050071520010000d040c10750b0381d00080c10707044040c010008503a035004a01c00e5903580d40148080c00490604544403011410051000007041c0ca0040400c4002c0d0519240420041042c000341c0700c00c080281035003122a138044411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 810559154 1250 810557904 810557953
    0xa0510120f02040602210a0f0509040207120206040b090303060901030b040f1e0308010902042103020304210b090105010317090d0f0b070f0c020d03030509100608030406020708010e 79
    0x1140e0320341e5092501c1c449880030380064101640100143e40e807101c6005146d00071442030301842c00d021300150481e0340c0c0c00748109a0041c601e15003280c0f14564080030030040d004000000741190b280d1900d804819600084007807107a4000c85c41d40b9242e480e9070780c0035501c9120580e582030300407581d4001400855194807102d50070a03c2080e5000710503000341c5519040720529082144001c01104031002890351140f80d9038058145000708500d41450010288a183c0c481000d00561421022409081c14024000d0b00d0007004002c10a0b40c01750300702d800e109840c92400008448200d101000f182440d0414841e03d410b0303a50090b140700411600d03a2804910781c225084e8581e000c0d9a00861000158074030181d508120311074005400107007811240a407400100b1203829007001b412048040241c2c3d02d03004c000342a5601410f0000e00d60702c4000070741c2d0034140c140d2003025020f82030800c00940a00d00200810486089509903141c05490725407003400da60580429000581c401a0b500c1044041340350748009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 810560404 1250 810559154 810559187
    0xa08031503060c0912060108190309031407030312020901020601051c0f0f03082d0a18110405010501090608040611040519030b060607051e070b07110f0a0510 69
    0x341101100080c03420800302c4010183c0080420310001904103031900c00c1240c407800014004940c10214140d580d10b084035070b180000d110603070b0348009040c003502009000e1908030b44500008805001c0f59a81d80e6128403085000801c945c05009144203d0f2095840c0c1000580c054003543c0d107040300304404c140e403004985601c21400d01005001030450300e407a4010521541501c11b0447e05820080c0c06500c0040028015100008120040011501142f0918813040d403c0c5201c907129800306d030004105220115a0305d014032480c590030f0007114080c80c0400d4400301d4040c02107a03200d5004581c0320711940310303500c003040b00c4001240c00654039030045241005140ca0150400d51b03a04009035078410318442c1c0020040310000107200384000c441820764080c005450f01307498521580d031030580c2e600100c0e2600d1300c00f84070006034544c0d282007440700c4001031070b0155600747c8801042c2010000d2108124013a48913242d0400c401d18242400b02c10781045407801080301c00071200001701660302d000035400601 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 810561654 1250 810560404 810560431
    0x190b0a08180a030305061306080a031103131403061b0a0c1e080408013903110a17090c030a2409060506030f1c03180203070806100f080a0803 62
    0x1c1601208204000c5194000d07a0046010b080c80d005000648901141440803641054010300200b6000a86181c460780e00d464000c1c1c0c2d8441c0350200504601038024030303d0303e040d102c407000202e85900e405c0200580004400b503400310380310031b841c10403003001a0410a660b040300b841a028158040c102d150400340c0903c80d451a0507292450400c3c000981100494662601007018014a88240704500c41050500c540003800c10300790f544142e8030314410714076070140401c146064158901c03c1c0c000044a0404016454466442030000b50465245448403016205c2040c0061503054001505221360360001d4040d05940c0601d4660602c0c400301c411945650700d410400740000d60300c60384a4401d555014660005090825178200b5080540100c01e40300c035039000680c1c6100401c081c6030246d120503d9800c000626103400d81d075001c1d00100e410401703503040c024000001034a050210b161482b54020020401501b40c8443c0361042c01c020131300030143c540d4002c140810004030058001c0d6045001843d00c0d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 810562904 1250 810561654 810561691
    0x614040801050106230a0c0b150901170f160605071b060e0405011e0509090a02030f070e090f070b1303020301090f051029040207080711190b0a08 64
    0x500b5210280c0c00240003d100016000000c240000150070914160210360f10b040ca20040013414250b0100000d4000001c841c040391003c40400c01c000310400014241e00155a5100b40c40300c200e0819420142e52401040d1030303800f6103000420b0190004800e24000c4103101e0624a0881d9181c00c5548100d0b0305030b070f030100411038010380301214100405c0165550741980702d0b010103000c10f490041e40030b03824000041140c0c1c1000c10160b64440c0a44509407203a035026981c01249070b160034840440a505802081d009800a030004140d2800b6960012034829190702d446900d80d82c1c400000c040000e03c1d8000301c100b8130000d600403000b0440c040904125407206622600003a003120341e901000c0302c2c0c80c0d854407028001c201081c090b1102c00c280c142c20420214a82803c481e10781017200803008c501c3e001003220901142d0725036060316140c40e00202030503200c1640c1e1402d59904500e0149052040103204400c004024240341e0b0700090720210700080f4107000343c4d0315044d42c2e011303001340c00746140c14440e5880 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 810564154 1250 810562904 810562919
    0xf0318070302030610090f0e0c0f0310020708090909070303050d150b040806070810080d0c080f070b010819020d060c020a050d120605100c2a171506030601061404 71
    0x1018041e43c1504504001e05c0c0ca030030040c0b0b00b200c0e42102c0060031241002400340700e24101181c1454040b5090741c500300b283e014000040d041c01c07072048094513414404511001409070b13a801a103100c0700150b40054440d215801003540c2c0d28a94440203000400c200080501e054468002c0c070b1000e4071420848041948a00b04141a60000d41200c0316541c042c0302003050180c0e000c440c058100b034084900d071a4030303800c14400ca501e0b10b105401b03000c00d10000070a0301080150500c00c41e0340f003c07816019143c81d01d000d8039080b810907200b8450400a4070690202c0e500d545401c81c1d0038186940d005100e422403e41c555240405070105600903001c0d40a02e08120740130410521407036440c00211b6907007100b0000d00d011004126103190308a036008a1000708030340c0c42c0f160060050380e941074000039802602d002141e49803100814240c0e10b81c2c0c2103003072680001b0b000c0400380001030088502c07009451015402e2400c0d00b2101c1c07802c40701c655050f03008400401266000700395007086400050942ca15040d152440b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 810565404 1250 810564154 810564163
    0x7081804020d0e010f060506030c0a140c16060206100330020c0301060b03161110231f05100e04051f061809022a01090303110f031807030203 62
    0x3038080b80381d4a901e52400c4081c028401c0303042103211381904018803402c3c00b01088443c0130040c0302c92060200043c1d080a0b01d40114461f454216400ca2403541d11072001c0e01caa91280017111a1510420180001041c50ba00100c0c3d02e40c418150040301c012400d1541d02d031070103451085130511a0582c204000f04a0040048205500e400d100d0740003014524400d40070306003101c907103602c603000d101010b20a0120320800890748001c4000c840c980210344c00705a01a841c100011030110050140c035100407503122041c80920391240580036004219142d40703060b6070560752003003020f16084420315604140690303e09100d514800c60842c2c034108210341c0d17120303000c1000c50300300703071489009c00b0500601c1c500c0c5408031112000142c50b2070300e0041481440281d031036000700d10b01c3c0540a2130340d8000c0780b0b0201602c20900c911400c8011001440c07410b054005181b0300030141d0b5081a03001a09110319100104201c50840d40102d1007510300c60324650b40c50500c883c82800505442c4d0726409241400000750f80c0412 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 810566654 1250 810565404 810565417
    0xd0617190327030c0b0702060306040b0a05030d030906060603060b0d050a020409020c03041403032104151b110102041422090b070f030504170307210603021509060708180402 76
    0x5186101c1181507003403c030410130160f884044a444108140001130f240d07002a82d401c4441074a0100310304004c0c400046150525812503501440780c0d21907502071990640089041c580118010006030b51240390480076130b0054040c41880d60020800200c90030519400503a12810a0b10014101602c400001007640e003c3c00c041c0160f94000705052214100100071124822000c400641c50511480100030403c0e00322680305141c4610900040d00740403400c40c00881d1800102800c101f4607100201e042c0b40306038882c10074000a10032101c000e035541814421141a6040c61804c002c400341040700704012085a1601c803040120103003038002d00e101280c040d00202d07512405003008030781380c00c03100140404000b00003241098205014800412008400300040707904d5000007039602d542c0c3d203105a4818007000010551082c2100708500b20245541c44103041e00e03c222451b03001c0401c1101e120f06140110200700da400f14040082c8000160040c0c010141c6041c00403600e80c9078066100098100e80140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 810567904 1250 810566654 810566717
    0xb0906010c15110c1b030a170c07090213090e0c09150103091a1905060a060507020303130e0114030a0c0603091e03080f060409052104030f080d06171903 67
    0x1060b2038900e405048130104200c0d00750000d00d44120291030b040c500004046108c0c1034a100089c0d00a40c401c1c0c2800024043c0001420642d038034098003400c100d0080c0780c0e1103042505460250662801800807032030303140352400201a603207075481e0b41042d884003000007520701e418150b490b1000e0000035004c0700303075001d000c00442d050681c510b00490b0889604040ca1070310742d500303803408080020941d00c004448050300c10a00c0e0043d159203072480828a144034041c1a00079101c58644005122101c0c0030142e8140c44460111045420b2501c4c1450341d0340c9071060004003400c9400105000780d6119038400c0b000e290141c0c00552554035074150719085d0111105090300001e0854040200d1000c00c440c03000d40024003981d04100444107a21055100d09260340908103240d10a9007079040b00c8851b00668000d1500311303001c13070b40030041464501d960313501118014031220704003680011102010100305940c41700b40b601030074941c044080d5a0074481c030103880c22000e00c5811200c884e1a1a4035020f00b61603441d01c0b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 810569154 1250 810567904 810567913
    0x6030717030c010c0903081204020f0d0b04171c05060102150108060f060d02030a032106060c1205030105010c08030a02120a0c120e0c0613050603190b0906010c15110c 73
    0x41d10243d096401443c60302e400c0c031010354010000a40c00c40d0072148100141681c01007142c883d440041c0c100d0500d9102c0d180c0c00360071052600280501c030b240140c040d42c414200e42d0900613444501d0030280c024902c80807091030852500c101c5c2e0300c085401c070b00d0340800c1c1481a5002d2004201083c00780c03c0080c0c000301e44640c030441c108900600c440409613080754003110104402d61140d0300013595081c072180010100803002d0044080200c00d001205101f40c0074200500110361500c1d40144145411503007074590541c4420313204c11160140e0101c905a51040c1d55284800e03554bd1600d0f001c036840074000340889982009803902c99109400d0150164802070400300c3c40d0702105000a202c107a801015404081c605184c8255440c3d00080721010540c040d5a82501e400104030340c1c6030400034540c800e5400507000010004000c419112200c404d4503407602c01c001d07000305441481041e07641221142d003c6684090341c140813402d0141d00610313842c070705e070400302c0d1110341c00c42070503440e4000400e1030300d15510 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 810570404 1250 810569154 810569167
    0x712081902120a0e03120c0a0c05060c030909090a020a0f060f09150c02040209090408030708010e010501080601050714070602060105040e1603031b05010216151a0103050603071703 79
    0x2840d03000403030482894070003400d04503a560851080c0d403145000c1081130200d208180f40c01610244000000400d6a41c40715032107112400800341c5900c04607001b02c0e9110070451000c11076190042c195400c00704c0a41c01107042c0201041801001e40c1c4c0a40100c5551045e128510016540c000300000a0032500d0a46503600e1700e0701d0340203000039144109510500003e80c1c0240503c10700b40b107008218644c2c507c0c001900f40801e0000c940244103100c031075030300140904200000c1c004484000e5009040c1560b49410070303030307a07106100800c480a00401e80090f6014011810300d600c544090700d0101d0081c01c84c41002041c0401207450400b060303018001581050300104075a250500c00c104607544c52502a00081c941e541c0c0310788041000703010040611550040c8020214000340303964030302c141d0140007150b582d40c90607034860f80c41380604021148100100c401495240c400c3c0220107900d24401c2c05101c99070762160064004e0000203100c190035121301140040c030b2802ca0b030f00a111080483d40619941c52 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 810571654 1250 810570404 810570427
    0x5031305010302030f04020f0a050901031b17030a03020a0e0d05150a09030c140f12090a05010c0b041502210a0c03090302060f0a18060c0e01090f0b0c071208 69
    0x4560340000d05142c818401c00c4100350302c070901e00b40d10079411070306600c07640c3c240e200240c21106030b5002540c00c00402c41c004002c0009000c4004404150070310200b441c2642c1e41d275a4070b0907000d8044c60060941007400304201150080d009000c800c203e1342040340f6120003403004203031364034142001968240c0c4010400070411903130451031904101c0361041800504156200a040c04905100c000c6c400000030021881d0800103114903047d90101c0c2c42907824400141e0740c0d42000790852488a84100a080c2c3d00040a43c09a608810101c2d480740900b4130039034468903041c0b00491021110000c0711b808000c44040703001086080507280542c10106074081c10000c0c08201102e000035241d50030701d490580d000012a0b00040c08552010301080c02c104259100030000c40508000041e2107000d140754803003001041201c2c0c0107642c03441e02c0c544e9001d0041c102c4000454141c4100c1c0310b070740e03504d4035484400e014481800c0003d04084089104840100b55508114040d0b62002c4405881440c0040344091440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 810572904 1250 810571654 810571687
    0x150a0e0102390604080c0906030a0b040b0114013b04060b0417030408031b0f061003021e010f030225030804050d0e0f040b040e0607090f060809031b0a0804030503 71
    0x36000740c1d2644d00b000d042103c401d545801e024a100e00c15400000001c0c3d25550810609945e0b56200c40c82c00c42c68101440e00d404110020700954402c1090030700719114652203110400c100030990701d94094814018406501402c0c51a1400340040240d5801000d95480d140500740040101d2070003140e4072703458180f40c0140c860a000500f4420380041000b040700c1d080000646d552002c80702d01d1040c008400c581ca461900100b908003104074051801048609065607822000722802980c580410103039407440c00d0412142c988089000c244001c16072142c99101e0750151290f096200c101405000000000650018100b101140000c180c08104004c0040510241301078010704d0400040c101e001d2800604400c100070302c4c00d03001e5692402a56160307925078110345c540d402c04006442a5044c440c03001041010300740500c000c440000c400014250b0b220707a4945100e0110300015500f426030a02289540c07001e40c0c480582c8611402c808140484c5800e001080198428401959900d0580e0070300e0900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 810574154 1250 810572904 810573013
    0xc0a09060b0d0209060720040b0103140f1e0a0f110304080d0522140d0c02030a0b1e0a0e01231603020d29150a0e0102 52
    0x4080c14240c041114030001d00c25100c003802401000744c1c40e103c00001150b01c82c01040c10180030303c8182002c03c02262a015003030b00401c00d0664082c88010305a00c01501600c0d00340e10b0f000210821200000c860108646103940c2048410b80202d02c03001000d091802d0244095441280140e030b61144001e131002144100c2000000c03404849003145480e485150180c042d0000880b03026459800007040c28521813144003500303d8000c12039131102c85038104407880070b4040c16041040e118007010032031001d016240390095503a0003401841691b40583e2000aa030401501c83d8032601400302c0d400c0b40c075600040b901c5108000800c0002062504ca005907400e580c1f034410b604000f461002080c62401e4407800300a5413000e07840048001c0d965008004500030b00c80d482203118007a1a108a0640840302139100d6600c11a484442078001c0146404000321a0721942460030004020000900b4950243c00c1c90102c0050500503210391130a21400c006402004421212404006a0b405c18041c080b04004040c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 810575404 1250 810574154 810574169
    0x20d0914150709171c050306240702040b04140c1e0f0a031e02030112140106080c010804050a021906110d0e01030b030309280e0f07032c0c0a 62
    0x6682400040505410301c1d03400b070040a040c004201c04c503210000c0118101220044074882071550b0b180d0001080c0303030020344210344509250b98052514403502000d0a1181c880181018640001c42d400c05c002001300318141d0350050f40f40c02c40d45403924544410203114207540903240c0d90364401d4070300074001d190359010071040f010307818088200e40d07070003040070744124103a2800e0001d01c4100f0314441c0156a104200c83c800030b81e00010022506a101c1d0b0703000b83c000e52150301c1900480e0b00045810b401d13035900740211a007aa000018280d41503206081eaa13400c14000d030b0684034036580c2a008503203083e180072040340009424540030007426902c0036400344105c25481c007800d100d1040540081410900071100b07410141c442040c00c14030b079000d100311a40000000d1185050b040d2070350110301c040280d080012184041c040d00001c01d80c03d001d045074421074005070803122655a040b4154010131409101620b141460250400b1000c445501c214600b19610000c20300c10007201c1c00c00c960012180c002c0c15 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 810576654 1250 810575404 810575443
    0xf03150106080f1021120f02010b06070b0a05061c080702011d0109030b1e16020729030a1103091e0a0209191e14070c0f0b0406020d0914 60
    0xb0010304a9650020340303c40c0e0b808810356510103500005d40b1403c01c04003803c00d5440300160250703075400c070104902180184d0004d101404106c07041124034062880064101421800011071101003540101c3c1c0c81200101070317480f41c2d840710703000d40d400c003118101c11926964001101000c0d9a000707616100200c0ca11244a00d10b0000080001c01040e2180b0006080009410101c1c1405800c00e400440c901c1c04401c2000c002d142c040030b8400c40c42c0c050ba0300d50015000c0d840010a6106c114492980444256601e140f00361102c1710448010354401440307a68060366884284461010050045029209070001404040b01c03c5800c3c110703c6840483c43d041e19480307850200b0050326603142131507200d180d0880d803500a0303640c410700c4006000340e28002d412451450141e002040969400310b94000030300c030300785440340e55044401d589070b400200010b40f106c040f050307190300003a03042504140d0052144a01504094041c0003500135140307410340480d0401c1041c40b0740c0307001e034000300f000270a9440c01010302e6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 810577904 1250 810576654 810576661
    0x510060e15030c09070519020304030b0c030f0103080c120f0d0c030501081203090c0603160f0807050f0c070e010914060405040f0b15030a0b061c050c010e0f03150106080f 75
    0x103a41d82c0708400256001e200013600007a609401001910305904809540b80314a010b4510020b4990b03002e404201c60014100f0049041c1203990300c1600e21589500035800440d0342140c407040c001c1d0700082c012840b0b51160030071403820769140700041c16104019045889e2103400d03034040081903480301f002010400d480e240042004203400510921400e24280704695281c03244001d050410030f900860980040d40041800f12003038245c074100ca000d1200350f072100d104895200e811500c840c02070f244500054418080560581680380042007070b054064101d5980d00d0b5155007402c0055426440782c02c0c05a80d510848806000d10445581d2000b403c480810191034665140001c4400c40000500085007420020350902e840260b902403000c801811103640309030a2405032280b00040714207502818140c40f095080a6041034006c1d0141ea0203001787c06980164001164540150324201d44d201603000130110306034030144484480a101607400196641c1002c0c0c0207001c6200181c801100243e121081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 810579154 1250 810577904 810577909
    0x150c050322021302070204110705030909010815060120010c031d0a080706050402120a0803041e0203150a1d03031614070b1306051e07110304140604030510060e15 71
    0x4003c43c008005070010b0f218800c0d0b0001c03c004100c180a40c22100b8000a01c100c03d01c5000805004d04441c1118404102e0b0b03242c50342e0a445d07030711041c0c45034083c00580e0085000c41d80200303140c00407182000d14819503c080150500e00b521551048070010030b41d14180c0411041123009174846115003400288140e6003141d0f62010a445000f20140c082a51000450215030b503d4440070011203040003160040310240c02d017018550310688080300d980c8244441200c0088402c061200380c240c000303028014a81c1c121500c0d0b9000b0f580208540e00d00c40d616a003085610b0715400452a604043d080150b49920781100024981c1003140d0701c000501c249480307005555a103100445a00310b90040e07010304030fa1184500f9001074458258024505814802004206181c2801001b031070300c0312003014160b540300c01005950360040c0804941540e0002c00c01400b07100c443c00301006101102a14080c64165203407201410290042c60700f10340951682c40412080c845040c03219003090803a5100250311604100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 810580404 1250 810579154 810579169
    0xc060f141b160f1a1804110f030a0f05100308070317150103140705091513150207060e010f12090602131805130f150c05032202 56
    0x40d0394660490005003180c070035884141e2401d60201c0401250b40c403680611805044000d24080d920340036294007070001d103100c002042c10742c4480c54491040e181054030840461a41c9418140790381041c0c0341e40c02503034002e81160052503603214810000340c40e824500d0303821080d5030400340507507003d6007400117004d201a40b50440c0341c00c41e0b5100e0f811729601d0110381b0f4151000c3c803201c0201c0ea84c2030201c104000642803001d0001c41c0d2100240e80410a000303501c403d810306200309462040c0000c6050205807054141440b02086403441d01d54610706080c80b001c0c80da2074940e0030340c0003001001c51440c5401140ca4041100402420180c20450300c1c1403550700008201200c0e007a030103404c100900512900381e40035607208902480c0c100a065540c1e094408000130702c00707918401c80c203a884640303022a0101c0c48620805000346091074405001c50f07410b4031451a401410714040c2c1e0641180481100308803841d200700741c00344249031142910b92a0000c0c184001044d07078444800780783c1d441e0340807000607034851340c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 810581654 1250 810580404 810580427
    0x80f0601021c02120f071101030603110415031e021008190507030f0903020f10060f0303050a050f03010f0e0619090c17270a050a17160c030c060f 64
    0x21603211202c05401e004034a041c003181c4522261440c00600c80c481200c000e001041c1243c001c0181ca1060319040c40114207c805c00c2c480a44001d0541180105038501130700a01c10381d94048550542c800d403a0f03115205e52114031410729480030f5400b07620030304600b0403820001000000f42401840741c034240d0039941c2080d2280d00742c00c440c660f5880c0000e04460280d03100c8070140b801d4490801c844280d80c40c010350350f03107100040b0f16080d102c4c1554600d84802140a031030f0607115034100b1107071180e01c1d543d0103072565001100e005080c024140a00004000040c000d1402840e014094041e00d078070304200700c0390111000d800b00e8003c0701110103100c2c40c1035400e9004411610116000121043c3d8400221015105140443c01c43c1e0103200502c1008111841c00360030a4442c070901707d8860b4031710b00102d0791f81c03d0703c584014141d0300319440e503c010804100c2a510304204007007145103000c0e003503008401d00d0940b412040312001000700040c0180042956031101504580c105007a0229a00c48061705190500c2e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 810582904 1250 810581654 810581683
    0x13060c050318150318120a020c060f0403020d06061a09010813110a030302060f10030c1a0405100f0e0316180f0e0a060f061d090f0304080c01080f060102 67
    0x211480b44081e01c40d8080c10000d0400314000355144d00f07201a40005110882c0c0d43c00b0301920034000c000e1030b010444030494407501502d4004210070f0b1650301c10710607240c000b502c558842120500c400800f50700c0d0380c110806510f20420700003403010705090000a001c4118002c4800c842001d0100c00d1050340c00008982e000700348071800d480c05905a1030143c2d550f0006502082d041a1101c00000c101900010554003680450420300c0c680c3d55400c010381e0f59521944000b401002c845030301040707121840481144a90041e44103030b46048c0d100c2011600caa80c03c2015800080d05000d25001c0c05a888801004068411405003c030030113007802d40c120646450240080204009000a0141800b540321030040180610140114034080d50869201c440b8010b0503123aa07070070064011448030281c483d440c1540c000412005a01318102d00090084100403c058154401e812030b5844d40c3d4400c0028000809021000b01081041c280005054040162006005401e20f10901c411681c0100d800d80c07440d12132 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 810584154 1250 810582904 810582937
    0x1c0f020601141905060f040602060f1e2d0105011d060306060904180c150f0f0f020f0a062c0a0303020c070e0115030501081501060e15040b13060c0503 66
    0x390143c1c400c480411341c00540d029a000640b101003006080107041182c42c0c507000e951542e42e810480c207403000030842d6070080008040301c406414078880c03200c80b40c106405a036401710341d01c04c1810ba1100803000c0902c00d9035440425004000569000403911904c48420b15880100200d500100300180000f40190340704044c0413030480c8540d1211f5218a404c0f900b00a204076401c600e40c01c2c400f0f1800440e001c0c01d401c1890031845056114042c00e010041c0f60000d40e9901000114a103086410700211002801103005079141002081000c0090003099801840c000821207660854203880c200c840100100302075042d00e40303907220000402c1c0920075540509026a954064a0b015030500d42580c1149981e049070721300101b203a03100d2070000d03100c0d89126201004540d8958544c20ba039900c11190760f40551805a0050085902c02c410202251101070300c0c0024820b80302034204456001074000f8025240d0105102100030200707010b48000784803a05000d0300417041034a0725612441076402003080c2084 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 810585404 1250 810584154 810584179
    0x11a04050c120a020a090e07300c0206090c030a0803010e0604020c0a050303040605070804200a0b043203060a05061f020109061419090804081c0f02060114 68
    0x1a401c200e070211600b25140746042d1410001600c000d40001100100080c02d2407004220b01a922400c68001d100c1341e1505091240029104110801e0000a440c0744080c1007000c0092441d16028004442e0195000382001c0d2a00c03034011490700110403500c0c0e100e03610410000c404030f41544102da05442400704880301c55610070300810082d104404209100e032180442d0717902400b0020002c1c42c0500e11035035040c0f1a680b1440c05c111551401070350003034540c010b000340c4d9040d12503000c04201c008800c080d00700c1d9002552289460181e802c2944038000a03882400e0050015100c0000500d01e812811002d9985c02112004640d0b0f44034010010981c5903a0380d40441c050340e03503288004002c41102c9103100d1007a600190001e01804541c5002c55480703040c0b60030701503c0064450110b1141c0e2840f000e4031501000c1022034000b40a0350002079804800400002c83c0d169030500c2042114000c2800600c0070b0007203003034010410b00209585504542291005002c031000880610000c4041202e80c0200c506 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 810586654 1250 810585404 810585421
    0x3190806060c0f060f010623160b011d1e0c0d0e06010906260d1b050a030c051c1b030513060e040b010806150a0c0f0b0a0509011a0405 59
    0xc212624000c80744203c0300110040880001c0e243c2c86999121000100741c0d9803104191929121a944000c110310001c44d00e10745022814081c01e001105140c040706080e0513510b508840d060283c20001000084800d0010720509500b005a00301e14200d450a4407100c1c10b00b0202e09003480a803075012441c40000700203212821a42218035605003a20a0303883e55603540c1d141100800c1584528400040d182040c41405403040306000c441410150140282417042542251016140380040c0da03c0000401001c001c00c0c01000352030314441c8a40c82c2c8260700c1c1360b241007036440c010590f04408054040f656035901101d502a030b00d2003100c110208100c01400c12450169000d01441101d4003030941004000524240d001d40048000c110541c2c041282400c0341d00119100201142d001da04000c01400380c185803070447c03009001000c59403400241007003095545201e900110b00303084d68030150700000d10003501c64070300c5400d8004882e48020441b030309101922100c01030050b02c0b814892a60b9100061014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 810587904 1250 810586654 810586657
    0xb0f07020108040213060f09052a250606081207050a1509060f0c090b04030b240a080303060a09050103030806011d100323040b0f280912020319080606 66
    0x101c0c001d00600c5100d440e003041d80c00d47c4d04540300e503000740c5040c071011805500043e422205003c00a01d260380442c51503403c480300a40c0f001d00c05c02d003034550700c804003401e0011501001814612680300840d03500d28050895241103082400e21400300010031244000500000d40070140300d0b4440210f41e43d03c4c1c02d0a1040c4018002e0f400040c1109080c02d502402c00c61040e400100311200756103500090545818104451b030196000007005603440001095190030101c4c165008e40005094000391000401d0200f203500001ea0701c881241c6c0d0000c4140440d510380012038202a2260aa00b00500e40c0740d600c00a24081c4c018024a0500c42c6190811200e407165184490450a001c0c00c11070b81000b080780001c000702801c410580342c1c0d00422440008000b0910101070050360840c610740e846445020000c1410030001c0d150307200d40c0322a200f0244010307402c0102080c8982007000000343d0f503270030750400c05403509213001484110b401c1004041038116848141854000081c50b180301241e5600c80421440d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 810589154 1250 810587904 810587929
    0x1902040c2118060e0c010f030e0c090c0d0612150504080a0f0201060807080703050f0705060a18150518090f1302010207180905071418090c12160b0f070201080402 71
    0x21a0a1404c1c8900c5500009207220280000381d0302c4001612410b00c00300c080710300c4061041c101e40c2080070004218a040d44c841c64100720380e1444680390840d01c20341e11044a4060b0b0103c04440d5683c01c07400144008000d40d0051410845424401d92030b01d503603982a144641080c5605000f100e8012560144c800d503c0750001d403a51100b20356843d03440d0303070341241da5882901c0700712034610a07680f1030440d0082c0400c141e0308a07600078020a0401140c81402d907a40e1030030240c0e022081d04640000182944c000074546054080740d03c5190b600c0e0020012044600c0320720701254000d41801017800740c500540b20409a0041004901c00d1543d011b9100407400c0c8103865004034000303440b594041c0d0700d100699001110b82c5220380100d520703946d5204414104004040000ca500401c2100d030601d840130700504c4550302c60014030940d05007002944c0050a0440c16030b07010507090780a1030404511400e800c0401c5d001e00220000c3e58100703010005c3e072440c503119205000703041048200106d011034423208a0280c6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 810590404 1250 810589154 810589163
    0x1c060501080606030c06090a0302060307180906051804030903060203090f0a05010209040507110304030605180d170c040b0415030e0a050a05010605060306032d1902040c2118 76
    0x1550796040140d944010594a030b5210307016492900c1d1040c50318400b140c0e001350020700000f05151031a000c02c00c0e00c1c3c100601d1f200c140841100c03c0e19000c110818101c010f4850340310000740d142d0a00061001c003501007441c1c0c1038010316881c14040860740000811003205d5102034096907070769540c6696414403550303451101491152144203001c00c031041d0094408c6c0881601c08000301c2d9250141220807420b1507507600707030070340041005201280280d0807a56010b810078003001b01c540400600303103140104032040034001410141320740701c12a451889140e003101d5403014060030035041440105076441070307100b002109100008107200c030740e000b500140842400c5e041a070b450403145080039610750f500c1100480c0c2c19403810102041c60300d04a07040e40d00034880600140030581800c0901e02d42c0141c050441d0f20490341c1060354540070079040125000e5201040c40c00756507050035105001c251000a5004401d0144034140c03040068070080082c0080700c00d184003c6024240c2944a1000c103030244000b40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 810591654 1250 810590404 810590411
    0x61d06090a09050a0b061c0c0306031a04050f0102130b090310020f0d050108150c28030c08010e04111009120c15080f0a0b1804110310020a0e1c06 64
    0x41142c500c2d8000ca105100d0941c013840644820401c10202e81b081c3c0701d00b81600044c030395460b40b03005401d901a4030045441d0800249064882d103070f482c8205103a0320394440341d8404d1410441006000e101d60300110401ca0002d5040a00303d00d0700104000d0280151098190049080d2040d80d88c1040480205200f41350119511031a484903004203a1180d134500220509101c000030b802000010b00c8401d45442940c0c06401d500e0f84007010039150b1102ca03881000c0c12041441c1d101500186210000d081402e403070001d41500d0390000a4820381e0164810b082c1d504c10790007000040381d48400b21901c1ea0100305c3d901d42d00c6105249080c1d80e00c905c00d82140c007285076008040e0301000104050038045e00c800445407880e00070002c038100c4030b2240459030a640581d00300003146658101c0d400c280268a0020103d02e15000c00e5170385091003c80494041d203243c5131130714108540d414184001174820300b8251302589080105034024003803054400009008490f4400c170103c00380c2c0504440854140e01000a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 810592904 1250 810591654 810591659
    0x6020a090305160b09060d15060f02010c081b070c08100606030605060715021c05090709110a0504180623040c05120a050402011106070c0b01090204061d06090a 70
    0x508a4546000482d003510464210f02c0301552045040c03c111804400b40d00d1614203610240716039504074280501c4015102c0140800041070f500e0000701604081e601d40810010f4440c3c002d0944510107030400600c1402d0081c0202d0000b06404503007004c1c503103085075035100300d54509500d50789015400300405c1c0c0212489a2645d00054000300201c40042d5400d200b4540c541e401c10030b503031140181c020102c1c0b2045400041034400b5401900002a00c00c0c048502c1902d2100341d401900c0d0300b26001d0b00c039604200310034404407055100711104542c2200300d90341061003074000078010784650b0041001e800b070b198012025441c07550b0400c4016081d03030218850314211151032a00034040c5400310612850401c0d2840030103501ca10140c41008022851303864203503e0b140a4100100000b0704141d040100c40c0d2810480c0d0002082218002c5d03070550344044580300c00d81050100da110603009440c0c021f004020030001c0b030b5440541c2e010030440e180354010901d4071650005442d84205120581c00c00c4480b40c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 810594154 1250 810592904 810592907
    0x302030c0604111905010804060905010f09060e0f03040303020a1e0c09020a08010812070807060b060304080c07050d0b04140c03010f0f0522080d0b130f0b0a0e06060a030906020a 78
    0xc25221000381c0301350140b048590340104902109005480c0091010800a40411180c0d08000f24131800740c000081e055094124200a8516640c07064034030940300c440003600c0d290100008120041540055420541565402900c0d0849024003a00160111110203440302c41034000450881c3c1c4900750325015596014504040c0d00701c0d54401c00454012400000c00042c089120240a00da0704490303403801c1e2540d0741d101e4064101c460252000790b5200d40c1003003140c8401d00118050f50059028586800710840031a00c1d1200d0b9401940c085c00c8103500e00c00003d16500c4406400941c8480c45140f002a201d42d10361406a410368010fa06600303044049a080565a02c54058401c483c54140625698001e4404d030f0702109180c01009000003000c141c002c20341c07080180150b582c4c1c25202080142c3e809000411001480c4141440d00760780b00c0702c0d448000c5042c464401c20100c00d83d0401301d054504240108032200003094a406000b0029080b49480c1c030961012880c90362081c0115150141c5060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 810595404 1250 810594154 810594173
    0x180b06030103060905010c0e1003150503031803060a0b090c0702060d0c09060e03062e09020703020606010305010e06130506060f0304060e0c0a03080306221b08010504060612090302030c0604 83
    0x13010f50f0039502e040341406400b48140140e244c981c82c003401f1a0034004040008070003d010090110241c881a1a03006c11265418001003060040d030140d601100b410102c101410a000a01407006691518444450039290500c965500000d951038068851055002040052003000308040c140c82c900802c0c0c0d05010b070000050f13800e442030380c0c1c0e82d140720042510506540344025102541c11a0540f03a0030b100803103240506c40c078560a040a811041c0e07695501820a98208040c203c000d40c004000300f01465078141300301030042c20741d00c064181d6800e0410128204080480c440144541c0f40c00c0014040c1d1a031038100d4840824170700c11103649162a041080050003515103501143c05841c3c3c0804031803504403010740030349410680d194510748a1508000d43c85820515801140c00c1c0c0c204003840c561114810701c2c050000c16a40480c41c500304080003000d00d0740582140d0f0ac500d140250601c00c041c0d0001500e40c40c0021a20b0005441d5040c1c201070703107103001e0702d68118200c0c4140001c200421a9910 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 810596654 1250 810595404 810595421
    0x1009030b1e070f02060a090c080304060201050106030c0f0e090c161506091b030b0a0302090f072a151b05040305010e0703031e110d090611011401180b0603010306 71
    0x71403070007690300c400c00c08850803a25034a83d00016485032012032424540d0b5404183d40521566001e608250b5610b01181590019840038000d40d540300c2c0104100e9405004e1040b03665010329000b0548580b890014001c0c5000c802e07010b010b0002240012120103034502110190010104d8054500c800c0e0701d428a001c42e85001d4460700349040041c0001d1900c11806142c4522040500c07070541d80c0d601d40c400301d008028113003416510021031140003015803a4843c03000d00501240051074018038005802070541804018601b0020351420910442070f004404140c40584d400001c01c0030441c0c000c10300c070010703141c021007003c00910700c0380c0900c1c043c541000c01081100c0c4a0b100a001c5d9002c1d2000c00c1340c0360f5055100190110b034442c41501700c90078004018440320803590411140d003c0901030310718941400e40c2d8540c800308003800801c0c00666003100420001d0311240d40240421031032400050b0744001c06201d2002c10211401ca500c0c0410102d420a403400c900245c2000d88a6941e400c00c0c5020b0301e01003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 810597904 1250 810596654 810596701
    0x503010e0a0201030e07061b2103020405040b010e0a09020f0403020a06170a02040b0336010c2d030b01270f09050403140307090806250206010609051009030b 69
    0x1c500d070045001041c544210703001c546071411141080004c005680070066400c0b03d12001d000d64030039414142027131410b03c880803030340c005840d5400d145c00c1c0003ca689102116040c040c03800c00f000380594449a18009541c0c0050000d0b0b210240402000082e01464000039805038403c3c4004c42d62680c4003503c15010719504100c000075807184030011040f403082d1b001d0489a042e0420000c0ca00440071068168441444030030046045402c1606289032408201d02404e00e03515803d01d46403107903000700c07040c8003440943c0e242907822480082c0c103400c180c0c0c1c1004072018141c450002400d9680074003c819200c2c0707282c40008014281030440702e144d0701854050600c000d484044042011001d0784581441645c0c96103c04000401300c3c110b40d030302c64200801050812103070007004103070a1014030610317000b0403c04080480001880e10507200152410315a03000719400400108240d90f0300c800604100c82c0180e41c11546031107138410456021190783c2020b45203244503c1480b841c03003c1ca03480003103045070f036 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 810599154 1250 810597904 810597911
    0x70b010b0c0705060a0e060c102d0507090f03050105061c0b0a050a0e03071103010e03071e02040f0e1605010513030b131a04051b280503010e0a020103 66
    0x2940340c403aa0314054142a0900740c2d1010780c0074440f03818490010241e100d4182495199911100d001500c25449546090190342160420b10041d80050189a0500360b2954444800d0420140503103004040030310155602c5880f02c0101d101c0a008bc10300e400600f8500000c0c0c11041e80340e0030624043e1a050b907500b40601e04010790440703800b00c5880d84055807a48102d074030320030391200075141010b000d01401040580d0b540d038601405c041d01c00c2006054541c40b031805042c100c1481c104040c2159041031400002c0d400401c8032400003107000070f0711a0900708045000d80445464004100245071203040b06403114035112241d81d02a40005050f04900b50a40300c01c6e20703160b250001181d01d8020010724665200d0302520600000301004c442541c0840811075214012032240c0341d46101d420150110441d01346005c007030000340b0000340100341d0b102c10703610480850b4400340008203c000d24212001c041d00c8901d10b0088501d0f50305000d4940c010400180248034041c08010b82a0712417002c00c2c0100d0100e441c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 810600404 1250 810599154 810599159
    0x904080301060f09060f0509040b03010e211602061e03070816210c02030c15040b01170a0609050f010e03030618011202100215071206060206091c020c1203070b01 71
    0x314055030b03002e403240d03a61071b031861941076141510f068100404071070703201e40c68400f42803058409101e80401d400c04100100200304241c40d243c201d49916080103050345504000b43c1c0885559200a600196410740e481a03072000f04495603201550301c8081118107070300020610050a910000f154000e2088400c001081d1070341000a4461442c030341d0b1170a003c9104c0d518400e0aa5425038459a42c940c002e00540707181c002d400c0301090400a0445894585804410901080c0805050080d0251026150b085103074200103111682d80c400758200107012a07200c0c10741d0030030080207203d011f00b4442c20784000d011482107410b030b19843c1e800490f61240240c403112000d100e00455140c0c41412200b0712110032a038001117409000500b001c88444009501c242e01c038641d03101c1020100140f04d0790440e1380d1004441c12041d0240291546603028004550282050040c1c018000c140d50300c0366202d2260b02101e800e0044c505a0410380c1d100714099202e60030351505949542d000c0001c24075180b143e000c8401680cac = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 810601654 1250 810600404 810600407
    0xc0a0308150a06030e03070f14070518040b04230d080703092003070e010603050a18050d081008010903030b03100618150e090a050c1e0f0402090904080301060f 70
    0x600d03078041603801901e280301000380901aa00603c2c041c4000c50940c2d150002c0c0e501c40790320b0f422440004844448542e5800d041d011002d0201c40081d0108440440f2400c0418040e00080c031009071003d410004010045010000d070129801481100050041c6454120340d2074151108811446038003c0380b580700c00141c859100b442080741013a07001a04401091006003641990040e1061f4a50540f140e064045004c0120030319150007021350796804106464440304640540c2e28031420f03a44c000c0aa44e000750001078012607504000000d51402142c0b035550042d400e0711750f48255010342400c1d40b0b089000717000d050703064201c0f41011380302b07408031494040b0722046401124001e1140e180e655600d0300780089120910b4004480d2000b0346030180581c01d0302c2c0c0c1103080c3c00e80701c16140301c0c40c50303407000c0c00000400c03005008901c00c036441240c000031042c44808254504a241d10030b254422100d6103000d030300b10340d5070b54140e030007540e40034140c0c10440c5484e2400700031a41c0280100b002284240d1609840c19 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 810602904 1250 810601654 810601681
    0x100e1f03290604030b06061216170f06090703060905090d03110c072105070e090d140a03020f041a04170105070e0105090f03250b07110d050a06020c0a0308 68
    0x40000d4085843e042c03450f110000a02009070a072075201030108100400803400d8040c0501804040c240b00400d0014500d024005440074460f06e03980380303445001c00480038000b0707112980c050016610401315a48047d0101c00500c215004031880c145400140f001d0020005215680e120194404108013400546030303801501900748900040d6024076028401c1e000704000b16000e032a0b02c100300524100c0c555a071142014501c2c0c01c100b01c000c030303c0010007410041c200098841032107181055100c0080240000c410344c0300e01d172034810600d0380000e02e003082c88000508680003844604c0311680070408640151805a209214102080c0d0608030b000b05040c81c1032040c2809203e40b80c95407920221028015070342c5400c21039005a1003484a040c603c0d0f0b41d203003400388601c082490044a40c40001c0c0c2862850307050200d400110500308103221010014410300810301d045207040b02d10080401540ca030462514101000040c4042c4c004641c2d5210380d640010b0320318540c2d00c40d80720003035907903944069030418 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 810604154 1250 810602904 810602981
    0x209090102040513060b18150a0206071b050607180b04080303150306011424070303052202011209140a0f030305070c030512040804080a080403060b0d02100e1f03 71
    0x10008004590483d80c1101c1d88040925000c0c5c442025140230101c100581c1e000007940c100942c02c8001000f0509500c5060b22025042103000401400c0007610303070710f0f070300c44004040000303000303116007101d080c0c1a00810060041072100300c0c01c3d0f500e60f01c42640c941c8a42082d5a5903a105442102c00440c038980401e9250681c2c0107950b121003195a06000c000d40b80000d5080e24000c002c0c010700380340c441c1120300010701405010b51408191401d0000030101c3e41c000d4040e1011036917545045500c0181e900090055800c4002000403e42c3c2e215800c2c4900198005003110343c01d44141a0b00700100b01a8880c03040c0364500070f0302c0410460796030404c117607540058200f0090000700200a0f10034240207011045400a0240c081d20741850b880754149450854044800e80b00038074042010000c000b124021003511100540320002e8440b070b00ea01003030701113030341841c41c40601440c420003403507a03102c211403502c0c5c418000e1100b0812007a0914040c0050403d02c40316501c1c01300c80460040d0b14400c0c2c1d00040103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 810605404 1250 810604154 810604169
    0x10203030915280515040516030911190305010609060e010611070f060c0b15010c02091f060906020c0301151503021b01020a1d010504030b13020909010204051306 71
    0x40314540100801015140100741060649a000d24203003110f565011034000400350038070008150528000718107050800700d28107413081d400c000c1008002c450f4100c011410034800e0802042c0081c2625254813074264410806400c031b4502c0421515254040c0314140131a40503400030040d1701c0d01c40601d603041e580d09000b08800b212000c0010080d06204170441c182c245607000640e041c03248c031030764404012000c2d6408640003901078900f5400b071261079081150410a505080d2001214110019044095441019118800090024500724003040340c0e8116030200c1c0c0c50400c0c0036a05c4800107442880c06003c1e01d0018440c103c003540c210b0405110350b13410280b80400ba0310351540340a2a000003d1074070108241003503000d00c10b1303601e140d80c12890313a180c0300781000002d6103271580d1304401031a03180101480400d0200413150442a80d03004401c0300c007500e03003028a03c0c4240d0350300180c41648040c8490300035001100a02004070095066014005462084440ca103070441007010130415104680181311 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 810606654 1250 810605404 810605413
    0x603020a1206020d0e06150d1208041e0510060806040b04081803030409020a171e040c0312110c010f02030d0e0c0a1d220b0a02090a06090e01050102030309 68
    0x40800e00d010300072800c1902c01d0074094a01101c0c040103600740c401515010380c140e071090092000e075089450300381a0441c41510008104d40d545d4031252041a43c00b1183e00038421101c1c00700301400f030199a11078802085c908081940501441c2159440510011011201d4500b441c0410072010102d201800ba0760030050b029880d848035210a405a4807404a10340106002c2091049a07101400a0705c003c11003d280141c07120b04203800500410b03400e20380304540302d041d4070812403400180208010f10100c1c103501107100d17135124034080382d100845800c060016011802d0904070580d1201c2545004d180303080c00d842c180c40c0e1060040da103950f0180210030268000340820b10556400750b102032110310182c41200e0a1207100c20103d00410b8945e044001d030306d81c140ca401c0070090700440c0c0080c0c1110b11200c80741d000420000c500d00120602000040800351410301051144115405890171541d00416815900ea5100405022401c0a1041c58560fa00c4074000288940c00403040c1d900c01e00e81c00c030142 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 810607904 1250 810606654 810606659
    0x3020f01030b06160803190c02030412020406030c03060f0f06140108040606050604060c0501060b03060a09020717030c04080106080a020108010611030d02031608060d080f0a030e060405030901120603020a 89
    0x15800361104190700ba400c804180075a0104021140900e4102402182c3c61039032030800b02d0080004040c0060306100c400d09208480310650f50001c03c032000c4070507070351010101506030710005015000c03036480500700510081010042c07143d1640a640d60924000c010041403040d440b05405071102031040c04900319030640e1004880d400b91101d50350041c4a00000500e4940340c400042d20303904079810020000b403a80d100a03080080c244904005002205140c506500d803801c00112248868020300c042030740c0200c0c0001c100010040b801c1c2500c80b065007810340324a410a9a0045c42e0800d03c40d4905660030154006003610f8089501030110350103949186141c2e00708202500c3c42c580e2003402c2031462000f040072101d2640688065400f0300718550030080c40c0c10000500820703c1001038103451040711010700e50400100c110048600e8108240e1500780c481c42942ca0030f40003001c500d50240c0c11401010200820490044001c20b02c1040980b0b0f00c120151020325080102c03629800000c0d0406201c400030b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 810609154 1250 810607904 810607907
    0xa0f0309120c020a05091f0f0e01151b080c1b1503060a15020601090e1606030507090513051e01140d210305040c0b1c050901090506160e0a03020f01 65
    0x442c056001030a91280660340718003180425100300e07100d0000940300300800054280800003800140394001d040c951143c1010350144e040700062094030b803d100d0440e0b00071b5003607019124100c6040d00200d6005044011401c00e41e031240d0254400c100c1900490070240d6140c418201c07003207500340e0040c02141c10722103030005015241d40b014000640c06400303908005000c1c2a158080b505d040c40f941d000c3c11065140001007001d0350011000c10b12250001c0c0741078080c0e80040c0845c00200c2c1c88510b008030751500d62090644029000f600505d401c00c20318060420b5189042c1c00c0b843c0503920301140401c400c1044444081c1030b4400307008007084428411114100361401c0c4005100c2140140590007407055801004110903522500a401007505c0754200018800c1200c030500c010042c0008140c940003402492203071440b0300002c600c0d171055440300490414842503000c51021079206083300c007541040304011a100000c540580006070701d440142003039080060b841d0b4222640a081d03460041c50382c000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 810610404 1250 810609154 810609167
    0x705030f15060d020d1e1205030c1c0b2d0a082104121104061707030b042102071e1d070c21020606060c070506031305010c03020a0f030912 61
    0xf010b0364000c0c58880d19802146080d40380c3c0450020240642000201920304040070300c4040c80c0200a01c8402c0c410040320211140886455070060b402c0e4a091300c85d03650107100242650709526411010f01e242c40200c401d8400d0220608500c00070080081500040801c10540690300810b101900311445294142d4125412000400c0c0250901c60900391141c40503200941503060030340769240b01c580302d20000d0829110f1800030300150403041d10b810740f0f880780442c0e0701c007414031008003c805a00002814450b220400324814403500100e88410054608025914902ca0159101400503d09071141162952110804175011045000c462100103d0f88483c07172403004040e4428496404d8451000078602082158a081d4010304098a1701c856031700240f8081c03000745920300688040290380b001039400502002219401c440140d40c030f68803a50600d045c001c100b000100030398200482a0391132034154000e003885810583d101c41021940c0071044042e110314000c090507550020740246c501c0391080c3d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 810611510 1106 810610404 810610429
    0x70510050c010c05183a05011d15090a140a0f050d02100603080304140f06130311061005100903020a0902031008070b030106050a030902040504050705030f1506 70
    0x54045500d42d06030207100422102c1d0500780394911071030020398000c880d8024002d000c10004132401c2c2064540300c600c2c080c0580039248844140c10a03402b00188600800002021100c0c40340c1c552071802122441c0d00360840c000d41051f00e02044076541c0c034411280c841d20080800d04030509000381000b10945503000041e00345030003000070911030000d480d00282c101c200c03450220702e91180c1920b00f00c50608074100c680a500100702001e9814060031403040d000c0d4580000c40d02e030b803a082c0c98450000311400981032203458030921503411b21005c0001c8990450800c02c05940c2c0740e400080300280603503c412000f903000802c100c01e40783c0202c0024010a407010041031554200b00c0c3d01c180c82e000c140030700b40402c000401c4220145e4420340010900d2500a4070400044c1014107003a5240d002600441c1d000e4420507105508032200004c00426102a49994801035114030781082014506503 = true := by decide +kernel

theorem cover : BRFrame.Cov 810431654 810611510 := by
  have h0 := BRFrame.cov_init 810431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 810431654 ≤ n) (h2 : n < 810611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
