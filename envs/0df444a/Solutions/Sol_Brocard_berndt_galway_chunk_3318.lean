-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3318
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:18:44.121238+00:00
-- url     : https://prove2.me/submissions/3593ebc2-f43c-4ccd-8a9f-e6285cbf1324

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 596582733 ≤ n < 596762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 596583983 1250 596582733 596582741
    0x6091406041a010f0e0411030c0306040b0303042d0b0a260112060207052b230909150405100501020f0f031801050d05040c060f1706060706140a 63
    0x94054800307012546400c00c0c429142d441c50220140440c542c0110146038511603013250a030b00001070400144903100039a586100d404c00c4545e0742d0440000400c20040d400c141c02140c2c0107590541c021402c0034182b04440c07051841074000c510828408070b258204901125020400400d942110503564441c2d882008000b080c41d40240380c221200c26440006100c0c103528100e040310310488a0348180315155803440c0180d804400c058807117104207500e0f1720415080300d0072584d04421051096081158050020f008041810344854a449110b00b5440781009104101c840f440400c41e031446440d55a02c1d4552488008401c82c0e5402c1440c2c0000c00c050340c0c102030315140a0302c109800700d0f00030000141040e540c40b511009202e2454006109070b5980c01040f201100c29503405040140c02d008140742840c04540048030259214001c0d80010410f441d0807680c0c0340b803005064942014520590481446901000381c0694010000094070301c0901145901840c410882c03e2088012400e182100308054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 596585233 1250 596583983 596583991
    0x30109051806070c39080d090b1206030a120503100503210d0e03070602180646090812120610021203072c06120a060914 53
    0x7021015142141450004031144a203089560368110340d803c942c2d0b0707030010200d21061800e019428150380041c00e035101a880c0341905540e542e00c000145022003075864810b017244440305000074020240140100002113841d044c6c0e0300e03d900c0035162290404a850301155280281000009032607540b4078950290085008078500318030f1308440350b268030406480740c1c202c1c00310501401e4620007040e03640e018000039140c020700300c050000c0c9140d100180c103411030b4425001254825070005a182a21007901d007501c40e040c800340c68040c01c06076001000038491102c801756440903001c4a56070b00c82c000a1070450071120804802e140d10179201004094860035031405900030a018511100c1d0240d5104c105445d031751200780c0352010040d02c80e44240464400c42d4480780302140a00c0c1c00590709404c5410055008850950340c490000e46103488195448001a0280c1812540c82c20324104a42d91102602c044005c81540b01845490b0044058001c290540c80546980d040132840c1c0041100c10001c1071103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 596586483 1250 596585233 596585251
    0x112e02161b0807062c031213030611030108030417101a04050106050f12090a0b0103030f0207080a020d060c0c170730050a05040902040e04050d020604080a0c05070b03010905 76
    0x4081d8840741d069804a01d4500c0035400741c603017880450204102d50700000300c0d503c00a0152064041e1416060074158061414002c851a80c0d000400070440c1520504605d03801301d004450641d410308243c25200c1c03055220344199088044170801501c901132000702c00b004513a50003004001212282c2d280c1d00203181302681d02c600d10f007800020b50680a80102d0701019040110549080d55002250007810405004070b01188a14010b90340050006c44545002c0c6020f901e5244000659010081c079000841d0011800c6800ca0307580440140c40d48407101602c10743c800408214115403c10071280346031501c1d0050701d40c1e440007070307543d031144000c80050607614001c1c9080301c03240000d0301c00900d03034281d85011100030311001c22150390010300c50400307071044005c40d180603494607a88119000130b903001b980210003211403a4044c03108000c4d00304882000e0a5050014081e5490561581c03001801451450420b024204039100c04000060020350013400203031102d19246d50f11a05502c00411003250300c408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 596587733 1250 596586483 596586493
    0x403060e010c0e1c0c08010e01020903060907060915020102090a15120b090402010302220e010509090a03081b04081b010e0303070b0c0702041803112e02161b08 70
    0x10307141c8210f403812201a40904421000d0031039040c1101941682801611102c2c104c4c000810980802e001d0201669010750001d83c031058403604160510001522081c2260710440080040301c0e0031603082ea048590103e00d51485020b070300c1c0164013901c9840b04582c0d01640103600403ca025681c446448111555584c9440e014449102d01381240e80400d10103600003984c3d00024010340c480e030002d01601004800c4481c0454800304240703c2081a90030005051000030018001c6d0b0400341038055100000703c0040c10001c103683c8015001c0302d005811880c52143c1c808540d88540848030845e8000c1c01e0003400c990203802202d21a0103581c1d42034a4003130028901c141250200d190000079103d03442c0e04482e00349825143e00e4043e0130603074025038003286c0180d19500124071a9220000d00c01780f150080e265800004200801c0038203001c0300d03c0d01e411030200c004a400701550890906503104d510542d400598502c1900c580c8171030001800e80050500f010782e0b001640c2039003026a403d085480110403a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 596588983 1250 596587733 596587751
    0xa020708010b040605061c09020604030c0e0c030403050307030b010509031e010f060b040608071704050a020103050a020c0a080c28050f060606031f151701050f0319060b03030403060e01 81
    0x4021390ba81072050650000d024130000584145a04e8051200704a03540000f501141545c0400c3e2260090f510503590800382c01c070100001100980c40e550300c031200d01003c0780f0714075140c2c0d400f4106001c007038121400c06a0324410905980d00882c100d03401c101c00101102e002c048007403031204800d603903281210015420010304512540c541c2c041c400644420b81542414142400d03402c4540300740040c00003040203540d9520125441d4050600340c0244d0049000d0040d03800e0302d0002600759074000e401d0b0030381c0e548100841940e440001c00e404202940c803400007a0340300c80c2d01601c1e5280011040d0318030700744428000c0d01940d811070b20780380440c4a4032585c203072222038001905254950404652464000300200b001a207084400380c80b524140324180340711808240c503550000711790504070110700c001c13070000351500304d0848400302694010501116442c1008078008046500c0e080c240e03d40c02010700104200208200c5550084294090040d040b0f035141c41e1780c1e050090141502240c186042e51821840c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 596590233 1250 596588983 596588989
    0x180a020705010e2b03021e030105100914040216050609010504170c030406050a11010f0234020105031009110a0f0206150621010e1005030a050c01080a110a020708010b 73
    0x30040b8200010300d0b240044040e00440b04c2d0100c0d8a8808800c00d40d00300000489080b1019120b452410343c80c0e0159204d6040105002d5040b03c103107280740a0001c003110401903030f55200e6500d0002d100a440c00341e2142140003850315640c2a4000c01842030080b9001c202c49035105510a621450250701c800380065002410101e0314880c40081c011540c20812050003002d0103078008296140303a034605040902d10004505084504080b003c070005500001d4502c00503007148551103a07200c000400c481c00d25003610b5100c5030b0004030200203050000c0403001900070000450b0b5240142641e01040c0301c14600b0801946a5603c071080100200311003450060840b440010380701d00c41d902d5821402217290440007009405d40012012240340b181c1c144105d02a11400310481d40240001446280c0a04240301222808034070b9421031070207580301ea880e02000c11350010b0240b10841e800c0c20104126199402d841005e402c00110300042e80600040140c5440d600007181030480c1d4000c4001c1000a503000c1c20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 596591483 1250 596590233 596590243
    0xa0c12030206240607030905030705040b1c020a050d0803160e0d0308180f0a0c12150509011808180a1a0c0f0610080c0103150306020702180a020705010e 67
    0xd80180c0c045000110414681c494400d0b214010420b000207050700d590002d41d1507442408102c001905403501001141810410500a007204560a00c060076480300860b045000c61100741300d80035100d030803040c155160301e500740014180142075a003d103091070618034260790042c1c034905805a00e450b099094144914421040c82c43c3c006c1500212034042c2c2c808540584000d0401454445503050742c040300002000f000004c3d041e0711000d8541c1c48801d041c042802d00c4103500656900d800c0d0701a0b00f0010b400720a40c2001d65003071a200042c3c5840780c802c4030340181010140041e0741510304a5000510142d0000b610302681c0d82e4010302e200341d4094042c003443e407545105544602c8203806182c8002031200020341214030740c4908440740500280d0b12146406070a4801401000404805010f0548180104031000e0003e00b07040c8064069a00c8103120025140300281000340d01294a02c219516031800381d1500c0a00d0751740c1c04003800c100c0e81b810002d51182d40c00b115250300e0040390116140010030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 596592733 1250 596591483 596591519
    0x507021507030e0429090714160b040602030a0513020102060105010e18130c08030f090f010c05100e0c0103060e073212010501020c0a170a0c080a0c 65
    0x503081900010001000a40d000004201c003030194803c40182d0a441d5803107249281d00e280503d80742d841d011000101101083c03558141d0140240703208000c1102d4204c019200014031a40c080755aa01954401645466510700e005000c3c4078000e0600c828024603402039806880e02e11010840e0380c41c0e4142224021001542c000d016801030740041040d5801603c06407030440000e407000410400a0041c030781c800104980b005101c2c1000c0362000c0c280b00c01ca17414003000e0300c1898015840c000100c050308126016250b040d034422003803d41000a5a481220400d6407180d021044540b8500322007035200180c440d58608005603c55238501000b15803090080c00d08860403075802d4010707030f21080001c03182e4604441410710f000c405004000000c0c81d1144181266421486100341c03150141520388101c9007040c0c2c001411540500341c05012075030391035000400c55042e12a42001c14090703103074981c106140c89101030311805141d40001040c0d00e020030708000407403041c603182e041140c94070400e540c4030781c04072 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 596593983 1250 596592733 596592739
    0x50618011a07080c01020c1204032406091805160e0a050a0615030212010609080c091503030703020705030106060203131401140a020d020d111b0a030606080303070f050702 75
    0x12004110000c10036416290501800d40d1142c0b0300b60407500e8049032940500c0900c041c41e940001c3c6c0c1c00151070140511815400883c030007900c2d2070700c0c54980440d400c0c801148070305504240d215030350894180390b00580060680035401e0081350228014045c0101c2c00070400d598070300a40d0008403c0c0d074aa484d078541a1001180a624580c656401c07400080c140101910242a40e6040104081071170308552114001c5a039000350b503404103482805100d050680c40071051100b0341d041400315100208940345c2c444030640d003405860b42d4409810240c0c0ba0500c11550f054000000d0710130505d9404a041000c0c0e80064000f440b083d81d9a2504a07600d00c64190408100c151502042c0a228282607040103c3d5105250440d9180c0c0c0440341c0300301d660700500c08200540e1042e801000782680501c50007c6110041c107141c041d403049400e0154480e45032140d031824800200c061b0b038085956081508014580043d810002280c031045801c0c0da9500c190f0704a00030404008050001c24031580c100c0341019405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 596595233 1250 596593983 596594029
    0x1b0818030a0806060f1603120504020f04180c120506090d0527130b040e280204090b010b1c090c0306112217030309150402060d0c080a0506 61
    0x14410440b00030728054107142d444407040160701aa40d4011000d0300440c0410060440c3c00c40161401034000c16162084a0540e401c210400015030b4540a100c6924881038401044c0700c0d06030800c0c5402c140b00600001c001303110165001c108822044001040c0702c0c85541150016142c0340b90640d51107600307401e403200040c4204a0404508220707148000c00251145000d100c243c0c954001502c00c5015001d141c1d607440c3d0720b0021242138681800b40c4002c3d0031000e0302a24965440046d07040e500794248003141e201d150030311400303411502d43d40e000e490000d80110300040c0c0c40d40c41e20380030742003617000807419407240084a00d8011001c0b0f0500c035001d48aa4800f0701c0c1001113245170f46007000b408000b0420811484180006400c0d9500503401d010020725811032111030781d0800001404480301240e40c0780c21a441403040003190b00780015002e040340044900d00d00f841d42c90307100042140c840c04ca10b140003141401041708281d9007185403640250750f408420301480d0f40e24014007050105094400100d0300348 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 596596483 1250 596595233 596595247
    0xb03030c06061c05030307030f0b01050901020c12030d0e0a02010e0306010803091504050d05010c0909140112050715080106030c05070b151c0305030105030106050d08071709041b081803 81
    0x1800c1c0c81c00c06842c0c07010b40f14640d152035840d544c0c1190022609800071a848035218516140144100c0460301000d081c19424a040c3c500003c0d81c410300032032301c10700841c03002d0351060303411208200360b40071000c03010130502002001c5a403890329070284410403400305500444003242490045a024182c0d894180118104003100003001a03a450f0400c00300f04c440700401c400b1a2035240c58201c0b030340e043d000d03030b0000c80c042407003d1000780b100d043e80e0301c425204d078035003840b554060114100302030440e03040c0301c0d10651a45460500c14240142c50b4862407008488031141001d690704940200d04031215034800b004901e00800e0203480740d11038120001e0415041d840056142500159651802c20307010304103501c0301c03201401c8011001343c2c0e40c1c070944c007044020004000c5450240141e001070b0105860301200c2c03240c80d940c1c0c4c0d01076000b4078000a20300084449401011300110003503075a0b03414010014841c81c02022030031140082001040030001d00d0090002c1c0780d41c081004002d9603100058010752030280c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 596597733 1250 596596483 596596489
    0x1060f21030311040e0f0f0f0105220f02070b1503070303050a050d20130f0609030816020d06060e06090402010207140303040b0307031418060c030601120e010f0b03030c0606 76
    0xc6510242d00d0fa80d8820301020070351101c0c40e0b01d5107101e00c0414410034a603007001c071408000b0700c0c1c00500d00c10070500c04000521554403980001040741d81d481a8014041e0007045640300688298012801c8691021070303a80280600a025240030b04a404a101b003440302607414581c594216010190201e00304006c1d00031444d100380010100d0400100700040c081c030f1f0071030314401c200c01c1d2200b1712210180301140c0f5200750900589403100524a40320780c00200ca180c01000303089681c0c0762001401151004c10002128841c1d0502040916030003010450740d47d00601d000402070126011781c204500324000040c5450030300d07c60690144e07805800901c0d09516041c6001c141505120781d442e0540424040060010601406140690815100800c030300004004034404100010240300b203104280e40c081400f83c402180e03094118204010703403560b0740e4804005880c004000407010f5045442d080c80e0f211040010750254410300d6103c41c041c410340301080d04240e13a030300840c80100d000e60400030100e11149 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 596598983 1250 596597733 596597741
    0x5030603030a140904091b06020708122101150305071719020c01021201030302120a0f030f0e0a11040c0c020f0d02010c0b09070509100303051e041701060f210303 71
    0x8403c00d081a0300d040f448501050079a0007088080f5503440e0b6071640c2d41c5000c1e10120603440074095030700c014403496152401d51507a5810903403292100c0746000035003001002a16401038480c91040d44c060542c0d581d118802450620459600e000080c0341034082910144600320780e903001540e000f090f80b2184c45488101c0b8000510079507821000e9420015101044020f001509100c81e40c202030300034540c514240a4102542c1c4043c00d5681c03102000300c0760450f60441c0a0120189140c42d00154140005601d00000e0040c985a030f4028850103c10300d0801c44a1207039801d0804054906108070142a80251190700180900950080315070f0b120550345e0a01e41c1350001740b50300524000c40d1801483e00c800f209690141c0b44d06004e030b0002141031009040ca5403e081d081010302e003c40450070301c0e540703009225000c0c085042e403031076140035150030580421070155030180115442c80c98080610028280c000c182610503410290982040000c800486140070108181e42c554104040c5007143d038110020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 596600233 1250 596598983 596599007
    0x406020319030e0a150c08060306040605060d0f050124140108090c0d3f03050601020f0615040f060b030c1b0105100306050a1a0d020409080a03150605030603030a 71
    0x50f520310356144a14000c02407440d000f070150549000012031103440d4020788064175500410b000707408040c8003e5880002c2c115520540002c0c000480c0d4030344900245070b030080306502521030b40c0c0b2a01490244001903108c200c2c100c00d00d845c408007a540119041190105030300c2a42489200e04e40b081c00303194051082141d000e864030041d14601001c080c0090301007000041c040e03031803081402d441c2c510f440100804170781200540c1880c2c00c01d00040b041a0502c464005520010162a00c0c045229640204540508282c41005540e11460800000804a0250075000c1d01c603604100340c03180d00380381520030f000c04c1c0c41c1d800c80040d20310341d06d40d008068154800303000504160740b8031006107a181c50038401c00c0d0080014205d60b4150341d1841c1002030035160044c00703101d0f0702482c2c040e2040740001c4200210141c40f0055440314114202c41c00041d00411340141c01422140e80000d41005040d85a4131020714100c0c002c50304c0ca04c003520398100b01d45501049550541541c0204107002c1079600866841c400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 596601483 1250 596600233 596600237
    0x16020f0d2001020d060f1802120103021c0204090305031b0913050c04150306031101032a110106030f0506010f03050709020702040603150504020f060f16050703020306040c090507050406020319 84
    0x40e042444c11404101c49441e4000481018445814000c0001500301032060f80e041c01015400d1001290180340b00c0201848000e101d91000d084040310703034510107200220940c004104000910303080c203002d030080d07004641c03a04e20004a101c0c5a03445418030710640751403d0000d0001039000204900d64402007001811203100e04409210000301c0e0354805410310305c00d05850340c1c00b00d6003516601d4250040100d0441460515040c0201c5002108504014828800c8640807443c1c1e600c480c090191220468505080c0a80d401c1000c08030510000400e46441544200c00312402d41e0b98071003c08100d0010380c04003c0680d0020001049400025005002c1e558001080040c400d5929a20003921545200d40c0c00122610b8400300402c0d4688101c00518003c8140d510916101d135240213443e8038800c580c4000790202c011100351080c0501001071030003550b40a0100e5640c2d08040c24200d0710041d240c419103021508250014402500c02c2060310100c40c0180c00841c02c08013072503480704a625808000b001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 596602733 1250 596601483 596601487
    0x15271c0306052106101202010804110a091a0f180c0912010b04050106030b030706140c1f0b040b0a181401060e010315030b01030b0c0705010516020f0d200102 69
    0x242503036403403105000000002828040440ca26015241040001400b40c00c1050b0b40c80b004100d1b45007088490f01c3e803103a0920300101c0994642c5041e00d0701741c01c00922710350032044240c008103800800744d21049440108a0741c081b295186101040041e041300c440c03040e08065aa514044a100c40c0c0200c1600711105400d0541403030420b4001c0f4501c804c0c09042030041d41c0d100c0420120f1410248207481c090003207072030b060040035441c80201e03a0f101710b039203e11000c00032039842006e400c08420b010b032591205440241c41840c240d01c044450782052a124a4001e546004c1c070070940c41c5045d1007070420502d406081003443c0c070700c0d00e0a0b180c1d0460704040c480e4802500c1d030ad031144243c000c19074000d01801503a21002d803600310050004044424036030750b95001701408142030012078001c03c0e005044941c071071403001b49903039444002441c0b0f000b1050001e000d50300780800c1c000c03080024100701c040788a0030380c00c03243c0650b011001c0a40c1d07080d05049004c0410400611862110f85c840c942840041503540098 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 596603983 1250 596602733 596602739
    0x15090405011e0507110d0f0e010c060f0c12020c0703060207031e0807090504051b0a091203020c040b04050402011403060406120f061112010b0d090515271c0306 70
    0x80920000c1c503402c1d580303203949400b0891825082500e440f070b1042d60034010b16007050642d40140c43c0941c0c03414a202448070300d2200c201c8682c800e40c600e5500301d90040040c07010741ca004019030040d10035a41208081020b40d003a9038402c1086100342c1c3d0703000000400411f1514a180c4591009520203803040c0e04009508010342025a0828094000300e2811f40e6250b16510300030030002e19404945d0011032155040100703000200301a42d11421020822001040e41c800e14888181c7d01c011440c1e100100300d00d000d443d00c200f0302d600811021001082070710107103c019818000c0000311541128000d000c10002a282ca0320351000f0406194422405400081c10380c0d100c00b0140700030301501200300d034850302c40781942003000803e004244c0344849000c1d000e4100710081900b42100d800c1401a02114a00460b00401d40590350708403400054020040d03500c0e981560b60402c2010a08807215208503402c032168005000004401780200344603d4080d2460311108460504150720000b08001050b40361132000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 596605233 1250 596603983 596604011
    0x1203071407050f1009030e1903050d03060801180f0b10050a03080711090423070b030c1810090b03060301061502030a020714091303090806100e0c031509040501 70
    0xa010a5000b42c1c000c2040c8219585004d241681d80070a10220303500302a825800a0340000384140d41c000119407201c0704010544072806425250340c0054041e109505c0129411900756000b0410b48404c1c40003403180c0180c0008400360700d400400c00918946400e862503000c14004481150024a602c0c01002046d03511000240006d1040d0010384920070002a050104200490801869a0217542d0a41c443c54140c842450070090910903d140b01d03a0010070800d1030b10f0506c4603034090104500b181e902c0e4100710309000d0b4a50009143c59030f070201121201a0306190100c0705d45250179095803011803650a04280d01d41b5500050100c941540d01c0360b0340440e180048200c0346a1111031a80155114007602000901c1d14038194412103940c11080b0b00d414550700d0780d03100c0d1a408002481d02c201c4903c0700c1e140c11204056144d210200e1806031006104001c0e54404108041303d04040488450f1340750740003050316130310094401d90704405c0a00c3d01e0141d1410274221455000d40502c0c0001034519011480d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 596606483 1250 596605233 596605237
    0xa02160c09060609050405091905191a100e06040b01030f060329091c020f060f09010e061006180b16020a170c040e0c191401020f12030714 61
    0xc0c09000d40c4442043c004640d200907800b0080c04100c03414000c0d030508460007620766182c00c0c20030101045007000c034006e200c2c003006844c00c0001c0f0384410401800e05402d00107804061901d00014800140000c140000d0968203003800fa03a907583d45080b1a510782c0c1d0100302c0101a0804031074103058542c00c01c0c0040520500c0f40400030f6008088000350510030014804240e0005107551500f11030030710078050340f80400256080c0c9003031200007403a450500b074035060b07180c80c890249408107446104100b16031241500c1c4214010043d800007403001d002c000f441d6946412040300c403e40c4010903e082000828482d451520500b55600410103101382c60344950300845e032054503c40040d02103103000791700b181841c0c02c44c0710080c124103c3c07c604002c0c0081c41c840c2c031618401c0035144625110101c000181406014540444034028840103909030560a03030703a0807041500c40e0f071801501600d0121078550021503800900040710000e41000340d00110312440f590405882ca20410400401842c907521580300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 596607733 1250 596606483 596606489
    0x60f03011505090910150f0609080a0816060c0909050c040501080c0703031112040c0b090609090c0f0c061603060602030a08070203090402040308090906010306051c0f060908030a0c090e0a02160c 85
    0x106c003030083c20718032003003580f1035103070722201c20030000c0c15081202007000700d4158207441d403120701c0d00d60701c042c441c81e0001170329181700c07020706070600c0c1143c01c1c03440381d03007102c0d51398100e4240b002c051109984001c80c00d021400b80340b280d20b0104040d4400030711061400310042243c64440e003000074a4545445000c4110703084007602c100314040c040207200c06c1c0449035040400030b10b00c0c4d2200030b02d040402c20104803c1e018030099a801000710402046038a11440f0580780d800704421401d03034441c40440900703582c8100aa45101e03502c90f0881c001e1201b14864025001640d40c16001103140004558040b50f000300001c0c00307034003180010710100340c0d143d4443c00108001d5001d20802c035241c64001080110145c0040c1820f0705061038103d04003c00c0d118024070816103c0200700b400d825800031301b08070059920300769004000b946011508020003000c03202450190451031810021035007520420344581170140a480b580010680000f46c4000054004015404024000414041c21507580c134244940a030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 596608983 1250 596607733 596607761
    0x301050d111504260d0906030507020a02061606060503120403030f03020720030d08012426160903020f090a180302030307020f030720060f070803060f03011505090910 73
    0x2042000c0c1c142182c0c1d00138010080307201c0240841035403404000c0c00188052145c0814151108002004e050091000b0882960007a01f01e540c4c82c05c4001c1c22814040d070544088940c4c1e0301d0000c01084038280003451084454040f0400c514150071501c0580f05a2041038881d000c0607020088000051354038090103181c3d0f11302103014100e0000c0f480c105802c00122013200c40030400340c240100003120742d44621041c02c0c0b008401042240d820b5000880703200c000c0c204003600d0902000604480900c80740209441000380d99000c99980f4600c4070121560b200c2488080e5010f170a0324242805031078540040c40d00240c40c45000504008203807540c880a0b9210f05007600542c1010040220320398043c4818100242b804004e10315010541d903d0a801b5207851301c490781c4001e40720045079201e807181000c46501910103c00c00303881d04040c0c500400d6980c405c541c82c500901082007602d14908050141040c0b0040880038100b1036030411040c80b00b10710004122410f00d214906002c0e064040f18428400240c01036 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 596610233 1250 596608983 596609009
    0xd140421020d1e170304020f100212030c031e131b0314010e0f0a02091602070806090102090f102102040b0c0609070b070f24020a05030a050106050301050d111504 71
    0x3030b084c0500c8010001000824240c03040007040010303a902d04508820a00483c0c500882030310104c012841c05486801c02900c020000050264508030b81c0061880740c1070740c1e500700c00000446801030f00c4071401036400803480c040e4161044002108840004028038592000214644d2b8030303200c10301480b881e8000d109080e5074a2440440f481014400840450510030081c0110100d59000c1000380c1c500526000b4210b1440780540303501803080c131085000b8141c4900300e46031410301d000b50900075030144001070311900a40403440a51300b0b250240512840903501e5503183c5125600810201030715030410407081560800010035000d440d0390182c03041d5030743c0c44010f0903240b41c41c1001614040c4160001c10100c0028804600000c014407128041e203940088121100c3c0011540c582c10f129220b103000041900110f080100c20303510030091840b4090401040c0444e90f079071a010344c0c80f48828050700390088007130f408000100781d4140f201e0402c0b41c3c01034420980120040e00481c42508030b504094041204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 596611483 1250 596610233 596610293
    0x7260a090311010b061c0e0109030207090c0f0c02400e0601210c080303010e04030f11032b110703020706030c051e1303050d140421020d 60
    0x100a2280c060b002d0448020060340d103000c0002581405040b403074043c2a2001c83c070340c2e800f96100e9041040c403840b001c40240b00c0d0583c2454040e440310501e0061201c0765152040e140944c3d44240c0c0800c000000301d4440c020150502d4003801044a01103500d0604800b04000000c207451080034448141e0340040c2044d101d51078541c41c09426118075204084d220342c0154014040544286000205500d4552100046a0031840c2c901225038441c5d00c200345074000071000081c0c000443d4002403081c2e11a654041d408845c09800351440000820220b034554010303c00c49c1e10781c1110b0006d0500b880001800141151070440c04d040645250304080209282c000c00c000c820540c0401c41d0b030000c0c141d1401c0c20310034008031410041050060485000030034a042c407112060100080484089245908013442c10a85034200141e070303010098180c5001554002a100c0100f1444044d00d00b560f0702c0c80f030000181d00f065a001040c620000d002a40c0c0300983c14458030004880c0d80008852003100e142000c0c454007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 596612733 1250 596611483 596611487
    0x16051507030b12120306030709020406050a090501080f0f091f0e010b150304080307030f1a0909160b03060a0513050a05070804230c0d21110607260a0903 67
    0xc00b980700c560040f04409a01c60201c803011403500701010841c0c5201c0c1c0c07645d44050002c0d00e440b043e07030701c050000b40c03001501041c00d07548007008020400c902d843c1c003014950741d0801124503480c104c0c0c081004440f00f1020601a0402c2004a41c00c1070042003240c0000380c0001c00b100d02505021003201d040e1b651110f180c80e140a00703001d4483c2d0150125038007005d1802240c03400301ca510000340700030010900000092300e0700b4020340c000c40702204041c0341000800c8082141941c6404540f805911403003085001807402c3c3c0002603010310084480150300fa42e1440c0c1244602d158201814840e48280140c80c00b1410743c5580b00b1a0091540c0e401003c1920304090407035004030b0710003a01c501d08114280c01008040340b0040c1c0d02010903403004040d4400d8080e07036200d0504100400d148150b11440f2041d0203400c0c03201c0d030450b00b411a20105075841e00094200700603a00800076000014190300f285002840d210f0103100001403c1600703c1c00c800060208603ca80c1c41c03641e0860f40700a203256502c0116050603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 596613983 1250 596612733 596612741
    0x91b022d070e10150813030212121005060f09011d0303120103030e041107020f040603150f0b091501180503010908040e0a0605061c02040302060409091509020f061605150703 76
    0x4540b1084220036008201d500400017100109030301c0813000c0d5144070030205403003003000314034501941d01c00031b880f54482168010719200030f5802c8106091104030105443c41c004d011140012600e2075801c0c0340140500c019154140c1080200c43c001e00094182c064036181400100390010341d4034584082507065180c042c00c1c8601000c07909014901d00546404850070701000c4910441c1c044600c06854400c01780058050311480d04014a0000c1c4801c1c2c150b4080c1c400e8020540c070b080501c0050200c88001c4d0240b0034041e408035100c00449880d50311051580d40542da51783e45c1001c1500c1d400e15441d4881020a00b500c0c404c081c100d03582d10300080c080100c6180100d80c0b9401c92105907050050070310f060300003080f90042070401c840b0641d54049420b1125203a9040314010b41d1702800203070700d5035a030303484c2c08008041ca00415200307500000f0284504d441300f481381d08071980c0c6c02005121800c0030182408141e8108007025090745940036000c00c0400c00400005d02c026040f02d2110542c1c0c03902c140000d09807 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 596615233 1250 596613983 596613989
    0x90308090a020906040f020c010608030c0f1b040203101e0302040606050901020715050d2a05042114100b0109090c170a060e0907091b022d070e10 64
    0x190492900c14005944102105070440d030304550201e01b0403510745011000740304801100110b50700e0101c0009800c4c0000c000ba22480c1001801d41d1038070000200d0b8180c0700c003d410051022071007a0309140040d403920754043c58200754403c0303201460945904840c07501403140f4401d011944c900710420021032416024200140000b071402d142807084120000c0c0d40ea140c3c600810100304404290200381d9407190086d01d2029010f90300c1031000314468503a1550741c480520b40c0796000003140421180c144c1c09442200d007202d840b81d048104403204803010300c040c2200395034100e4544160381d4018800150410107a0200310700c06000107802c0d0340020000d8541d800c2c81e80b2948071181400c101d1442c081d01301c05c103000b0381d441c60001c04101d651034145010042c05580c10420407606018240014a80002406410341d103403c0743c10021189013a0210950b060103a008900591000ad03a034148204c50042c100c1441103651540d1103081c0e52540d4550400f041c94201414a0700110f080256048540700d2030001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 596616483 1250 596615233 596615251
    0x308090106140906040e012301030b01090902030304060804020112050103080310151209050a02030f0d0201051f14010905060a03020a0305060409170a050d0c03060305012306010e15040801090308 85
    0x59048801082455600030204d0384250b59548103580c035a034081d00402a580c411941021014580b1485c01e02014006e02050717500c01c400c2400890802c9191184504807a00100194203103072804000310341c03400009000300d040143d034000c0d410b20483c16025007800b951103500450788070700c0c05590407140700b0340355802040c49108807030a5070360203500407408a003001e026a10200b170040703060404900e0103045610080d00352140004c8a90810000b041c010000000d5500030b111030784645106100c0741100e84031281442908032010404041e08400d200320003103041c1020b85600c1c0d82d035000a0b040381c1003030365a540401d400080034003200e03906206071070703005a044600700030031000c0792a040c801c482e94200401a140d000100c240005000f5016550030b00c4202c5014003002210f03981c001c018200d10700c8212000c2d800c1641700003203641d200b6400c08140c0d00081c2200d00654415004482040b14910301c02d030410f41104034141c01f2381001c0b0060000d03045c900b0000c0398034406890003c005200080080780307 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 596617733 1250 596616483 596616509
    0x12020127050d0503040308030c190206040206030f07030b040f02210c07020d0f050d0c11040e0d0e011133010305030403020f0105191112130918020d0308090106 70
    0x1600c410036020541962400d0740c1e0450300e15500d140c9035140d40b141d85c0028080d480080104402001c0c00b400408c100c9403800b00860020011301d2080c0d94841301601c000354001000c0c00080c007510b80940c1c406500642901e00440d000c074425012400f2141080120418507400003604402c10461035200301a544800812019529280c103c03803459000b80d0030b00911580307112550000f40641700000c2c10b100e5400c403054078052003046030f010b803140705582c004503480089990100754901d000e105010074010100e024212b51250140b00710380c072103c4c0484003814412000f21040103d0010410200000207800000b40c1180702c05116180690610034841688121480107200048011041e201143d50684400c0403203612540161000d02802d9091540030124108080a450741300078031810294105040e680e4a10003101015018441c5482151000c00a2182004800d600d544040004908000b00c0040a00781d6400a4207914110701d0580005c1c0d14102404100300c0b00b8030074140140b400f460485 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 596618983 1250 596617733 596617787
    0x70f050c0c0616150606020106120218190f0b1f1b0f0614193e0c030c12190c1b08150604050c0f031807120201 49
    0x107a85112482032640209400b003055896880807441c0700d40d860340d000520381c06014003050382c0401020030f80329100056081100000c3d8111182405044254010f080001c16400030b0340c105030410800b03820b2210720007604602001e107030398900c55a40d41a44022010505083c28010888640c0e00c410803202c06102c010305881405400181c00040c2e43e80380100301d8918030260400b40540700c000c0f84007501c0c5d41c1c201001032401081e03e204480c03040c02c50713804140380700b140f0103816421035200000981c2c00c00c40e0000d5a0a490202844048102d5607640c46801d007101403904052150b0084c00914420f9403001c14810a0f0090501c40e144080d09002c220500305042e040d0703034800040840c0c00b10018030003034030000c40600001226407a107031011aa070420496561700d5210743d41d4945040510950001f450100f1a546404e001d074900401c2008207160030542081e0b00d07405c85c3c1d4000f601002d4402650b18400500349001c0c044070b401032064141a0040710210300024217204581d03141006071241c8840c000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 596620233 1250 596618983 596619007
    0x6040501091701060b0406170a0b130209030a02030109030806152d0c0a15110306180601270e0c1c2004030f05120a0816170906070f05 59
    0x4200d40481ea00842c0120040d003a0742d00501081d00104001c080020300841c51980210198100104400304d940c0c0b165142e03c0c80e0302c116043c03800344541c003611050403c1904446500544581500102910b0b100030240e030009084448049048003c41c0c022410010540350488070b0101094803e02800e03d440782c482c5000f122080d11300d605800031107101002d03a2601a523031060301c080301c0c17828080724450a83d034103061945410b007801c2e00c2030f000d060218615030050070030140c9016407400f40030000e104061100c240c081800081889040108103011107040301c400b410010400a20403041d11440c90901d0144800c0318070080a603000d0500400901001c1c01d05101c01c1e114450384540001204240d003211250700740800140d40d8120786000c200401401415841c568849114104440010907003e000200324051440044c02007841000001c0807440f1400b00c0d140540404c1c680802c610f01000d0403410000425145064268040806c01a501d03030030815866407129a41042e40c102440c040078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 596621483 1250 596620233 596620247
    0x605071103070b040c0e07090f0501020727090209071d010318020112020c010e060118050f07110a1202030c0105010608150d060b030a051c0302030f24060c0c0a0506040501 75
    0x100410b00300003d0000b40521055244880103040a13150b03544540c00d00c550000c00c4010240104000e900c81100005510b41c00003501c14202c40040042c140180d040301e00c0707061030390001d000c1140446d4031141820010383e40d10a42d28400c040f6621820250380170003030010300181c0280d60311410b16181c421000c0c400155042c0c102d550766424038001400100742d03022a000ba001d80c950800ca10f40c00c01d5a0100105c80129915042c1d0f845c81e203619144407110422007041e6482511b03100941d029010200da0b0040c170506200e8520a00c45045070752800f0190340e240d05e8000c0c41152840145c0000c00e0908581c00c080c051140144a9031802804604100241c0701804049007400c1d4802d84115039440100303c1d858000c03030780c0c515005003030b20400d40395810100c1c0c8480000c0d030001d41000c14404600512400391080c0c80c0503050300c03400340c04150784061150008910300354214074541c0001d54480c03020340d901c00c000d10113a140000a0600440300c0c00034400c0d6003030320f5040b07240b01d4882800107100e1641c0c071800b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 596622733 1250 596621483 596621497
    0x60a0b030a0c020c091303020f0a03410304020108060a03020109181803110f01060b0a1412040c1d0c09192c010e06152a0a0605071103 59
    0x20700020a041030120507442d0000c504201ca80101c80c48041060145c2202940c1c15164040c2d02512800100388811a031a0511080010003245548080300041807001f00c118150555030649400210030b01003210418440031004021500c00000c20401196481010103407c1340707040d41c5940312107045a00180c6040c8142c06000c070120705007098111183c0060700640c0454081c00311032900c14600d424001c000a80f40c20440313146125201541c02483d005200700d00894003a030010b903080c0281c101044651207890002042d200f403043c416504034141e00c60289009502c926070020786586080b01100c540e0f034141d800e2000e90b1200108000440080d00d0444000082c111640703c1c030740382d110480d00603900030340d000740070002c0201031000b1100b0002400e4031b50501c0030f000040816030761000c025181c0c1204944854212240c03024004a5101036006070901d5600b181d8046a0812043e515544d40f0b014440480794503440300e0212002e022041c401c46400071807514040540d202810541a40c0e8442d4a03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 596623983 1250 596622733 596622751
    0x90213090f0e1c030204030c0b1b1c0503100e10080d0203091806060708030705030f0a0504030c0201030f06210b0c2502040b0d08030403090e01060903030e041113030308060a0b03 78
    0x41040c6411078441d40c1214003540d4055088c1081030b40340e044c108520b400000070f904000c505110107040281c40010548600307140d070b50340c1814002d448030040310540c001400d000c0f204402e0420104003541c4a84c0721a1140409001d010040f625089035030b864070220303020400541d0001c000001103070b02c0300c521607810581d01400c0300702541c444070b01240c0d01e407103182d1006d0102d030000720500c00c815600c44001c0d030041d41010754000c60b80c0c41c1c1d0104c0c01d040b11819280200442d0b09240ea03040154001d401c4400500300344400004c10603941c40004142c001015507041c903240207540301c08200401491141e403c068a41c140d5410a002c0350407103002030206810200c24826203207200350465032107801549550b14042e001100c0e00403185040c0196400907501200400ea10020124580f103611080368101d821503500d299030030b440c54405848200385001d405411070746450702c641030b02828000521354440c080d02000f400c5484c50900a041ca00050100d51154511840800031a0442d00507681c1191100d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 596625233 1250 596623983 596624023
    0x60727060c05070e0408121b09130e1b12010203070219050705030a081b0606060910111c0906050901050414130510090f02070c0e10090213090f0e 64
    0x103041c0b440c54031079a5840385202580c40c1040204018940d8050320002e0b41013800d0703030307040c0e220301c030500c620042841c11820600506110045003890006448001c401d1900c4000940c022242da0b402c0c10100034804007480031400b951440418189a034103031140a03e00d10086095041400d0000e41311401651203082c0031410103100c5003481000d0110304014080181242c188200d1392600c2a915088031071108440041400140da844a0101e14240710b007000601e01c61034201d6050410400c20813031010030381000244518110030803410486030340d900e05211851108031a070510010300500703854014104000c001d010b00401030740c0120959040c3c98006000c40703469445a0017040d480415081003500050502c014885041c00702036034602070310302c900700c1800780100c00039402080c0d2099200041c1a1402c4c000d00f0402e0113810009aa00101036481e4900710702d41d104204000d1ba0407203a40c068004454a200700104440c920840c40c100c16000001d000d400614561075488108066007e5600b24030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 596626483 1250 596625233 596625257
    0x11202040f140a08070f0609150c03140403050106090209190b0703081509130c12030921120e01081003080316140a0203030f0109060312050706020d02040806072706 72
    0x743c101c4442c040c09407682101d411666a050b06104101c051207903c2c08900724420120741346940300080014410103131100844401150340460303070800401c503c00c180040600020001440a00510000f40800030016841c0c4103544104000d242000c8042820309002e20020400c0d02e80007001c5d60807071509428103402a1380d178489144803030458450160707404071075001041301a40b509030041010780d004100c203218958a441c1c0609a4550041014022075040e000401aa9900c00c2c80381d00401400200840c0305c007000d030f075440002c1140c15044030201c0d03500c1d8050089560f0064209034041400a0868411850354407403d402d4400901103900e00010001d000d4000c502071013540c10b200c0c40c01080255900040500251250003d8601d00c01c40c0c00c1d01000002d03901c1090240760160317900410390741003590140300103031000e80c45a0411552550240a284440d10302440940000e01c044009030181c4e00c1c091100074204000358014030203a074000303864421403844048044040ea00d035030901c95a0f9100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 596627733 1250 596626483 596626489
    0x40e2211010c020411070314090303070f1502031003050c0906061821070806011a09090a090606120b07020604120309140102040306140108070e0a0c03020c0708030306011202040f14 79
    0x2d18000083d4001e418041044540041c14000301900c502a42d504080029960110b00b42c51244011417a490f13841803158138046055440300001451250865071408006100d00100b80d070022580b03419010410340040082c402e00340494001d08201311543c6403030b40341c0480021281c0c05007542e4100800039224a018040d2101100c45844000200c680c824402208640a0b80c810282c0102a5180901d40000600840e01000000c515201c0d244880c01c0c41900c0d0280651030000a00d1b00c0c3c0d00b00e0b111580301e4042103161243d0340260038602001d0908500301e00340301ca81c5141c003030f0641c002c550140c420032000c1a0105d02d0041e5900c220314001c00c80c0e0780d03a41403490704030704410002161544001000400c00140d540903038200d44030b445241003140c2c3d9500710103443e04c0e03843c4180c080d0f0f9811140007600c50b14095110810903200e5044c01410140d600c10440d203010f070740f5000301e0030560001003030080c01c2d1303000580c0c6500c90b0250041507180c90b040c0420030401c183e5500c1000b141c00c0050400d1071071aa = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 596628983 1250 596627733 596627747
    0x5071202180d0623040203030910090e01030f03030e0a0213021c050a150b1c0c031b0905030615061602010201230f161e0e1005040e221101 61
    0x100300040102407810640000c10414124403912022007480c00158132444002a206540080c05182449205424442e0045000034060b041114801d000301380ea000044006002c1c1d4024003030140c4500d22403a0260444000c02c280401d103610030464000141d80b0fa5100580300c0040c50030160300d03040407803000c085d41d032403081c3c0410855080c5410015500c1032603021104010b90300200950065031070a81865038800d21151284183c000320400146070296004510442214038000a2032046c03110b00c41c0031080c201c4411400130301c28560402c46450308000242e00400101e0034a00340c540100c000600a12840d40185250400d040c0c41c038065a0007036001d00c01034601099107522078254030841c900021800c0700e5011008010002080c05214100d040e4180080103480b13840c001c0b1042841080000030720b5030345004114680f1205082600c035074480b9014585552200d6899604102d001402160005e100c0c4040100c00b03601300c07201b03d40c03122081c0e49541d041584004038a400c2c0300100c070aa = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 596630233 1250 596628983 596629027
    0xf0f03010c03020706051b0a27030b0406051b1b19050304031401140f040f12030605011d030a0206210f07020c0306070f0f1e02030702100305071202 65
    0x40d481e0038141e00c0e6054254000744600b41c8200350410076a03603240300f070020341000040000314418081c0b00044a840c028480e044062814190f110388240c0301d42c140d41d00c9403c2a0b04115103244419041c4410400030303001d4241c0280390954000201c1d46c0c0301140d891140038100a02d01012114030400d00c19020510041c2c10181e01c2000300005210941440c680e240c2c0310744003c85000810b01c01850144d281031040980400402880400700c8c3c07a15070169010040160041d0f52804407403045800154601980700441c0400f600c01244040c03900380090071180d000040c88800d02c5907000c84200640d0b000c109900c0c001d904a9540d5101d6840541500849900e070400c4010405290b05200c0b030f10a0900b132851240d102682100d0910180301c05042d2600f905554102c0881c20303480e00c005a550089081019118581c684420034000906030901c00000d000350110150308001500410341c03c040e0600a40514982018002d40c24402c8004000003100340065041035408189105c2d543e204031182c080d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 596631483 1250 596630233 596630239
    0x3210e09010909030809030306060414010e1807020f0f03030c031b040801090c14031216052d03120c0306060c010507080a0501091109040e030c160302150301080c0f0f 73
    0x155a107400418000304080f802c294040703038403040000c0080c0400001c0f648584005440241014a0241202d03a82c0100c102c00f241030056400e48001c10703482e034040c1e80e00c280c81700550041040c182804046d0030440c80400c0002d55402c02111816501f5000044070f40008410b82c5ca01d0340d9a4501d1000606c0f01403501665501c00000100083c040a0540100031080e0050010840a6130b03034500d4190f5100000e03e0f80fa0f0903030413079452003485500c214003802d4180303000f52406e030a014007640d942d420040040340f017210080071841c0e203042c03001186800f181d40f041140000c40c5800c2d0451940018181c008111138170345180000081c070940c58070400d860301d241102d0004c0c000c1c0e042060002e42942c80407904441c05501c0c1c900001518003150041c11020a10520400d1603c1e814000b0300004d0a5858102002d91000b00b0000e0342e800b10421181c81d0101c20b205001c00201d04520401807408007402001450710300900041c41103ca0100750300e023417410212140e00b40c042d80703500420380610254042583c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 596632733 1250 596631483 596631499
    0x6050607150b2101050c090d020904020415260610030b100302060d0b030d0e0a0506030a1407050304060c03021213050f030a090807210f050102090901240903210e 71
    0x2611948003c1d00f4600c510303480c1d00a00165940417001c0065000e01151194408101c840d07520145c101428201d412031b0002d0000b10300d01840d1820001141203030703844845100f0221401c032488080d07072203c0c0c0f504641100d014003440c0c189000314071082c04080c08003900007840a40826502507082d007155009650140c10300d0f49421040414100404c010584039000e4007e0304000703102c041c403a01012081800c014000d00982e0b060070103002007600000d021045155641502d921015540c40740d0a2203a01d080d42c403980e0381e02d020f03d000c40039104858188014540148500700c400500e810051b50300000c035602ca11a10180d9041480c82c1a0300024003642602000170000304090380507000d6419203c3d100104c42c2c1044c2d0740c244410407000307a00f444c001d101d01014100c400051264030001101401000054100540c1c0800124050001ea012840d020b000c101c0140342004030b01d240344200b03001802c00e040054034503101d5018001e4000041d41c507021800014000c0d07240a85e480820104019254803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 596633983 1250 596632733 596632759
    0x1801050903070804030b2d0105010e0a06140a21090201021209060403110d061a0f0306010e0c030402010c06140118020a0f0806030a061a0301111314130c17060406050607150b 76
    0x100c07d07401e004150008074040c41090141c200959040f08491055481e03105e04a00030351540400d410450144040111440400c1c080908850380310160040c11403002a1358600c5100192819010f40050301c0b45003800c0c8110000c075038406003a0380860740c10080c0b082d4090060b10006030f0032031512600401c00c6290503501059803000031031200c5e80650948441400300010320406940e24002d2017043c0100248400041d10012048055038200d48181040c0301521b440390b85110544144140c1c84d10820061001000b4144540001150019115204524000c0800402810001050b014101780010301020803a00d44040180f0b01105030820030030000c000d881000c801d4605507401c0303418400d6091111000784034034114112851a000c00c141c0e24142d901d480c4041c096420203202c1d85038403243c80300c25010503400e940500c1c688004c09650740c41d50325010701a09030300c0c10800342c2018015407401000384810348662084800c0c864001e004900e0107500d1300c001c90041c2440c1a40d007604140c1ea52200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 596635233 1250 596633983 596634061
    0xb070507090b040908090f0a08030301090c0206150f1504092f1908040c090606021606142a0d1d010c0c0513060801051801050903070804030b 62
    0x381035610300003052104440540800c41600c00289020700040790402419080386003d100492134120042c1c07543c1c003016580c180300c5017103401c2680001895504c84915120055041c0f02c0326600a0381000b0079001f001c803040220724441e07109040c00b130091400391805406040c041c010f46004000b0110203111600780c03100103001001072100d01156810700e001c009021195940c0035280c0700000d8017a43c0760a0300c241d5008480030040a44240c904007154100407541a00ea030013104098001900200380c03c01c00c0307940741c061300031003580207c0c20010002c10030851060f0620407680c3c404908083c00c80d690341c8036003940d00001c0908411104907c22541111240b6030030150b11010000100400c5406008107001920302460b41c41c0000e09822040e44244850315000480041e40841c0c00c10000e4a551140003050131613030161703050b1030701a20050424000c103200340a000e074041040d03000745043c014a5034810b642400365000080480e82520700040d00c11801003000801505c0c6100c42d029002d10004203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 596636483 1250 596635233 596635243
    0x906111e0a0203150105030c100c060c030501050f0103060308030604021b03070302060f09010603030206010b07140109050309190e01050d080d0606031a04020309060a2c030a0201060f031115040b0705 87
    0x1c100e01070301881c248540e88440d001d00c030f5412541c0c05030180804004d104c04004884421806071414010303450303101c0001c9a0b10b032040d1060310320280c40005a42d4100b0b4204030f42070703040704100c034100350618505000081000085e00c2d0407001c00e0b60056254440060b001d182071180701c50301c881d01d100119011003810b40c001903550142c8a025120b40050701c0710300c9409e090b03c402d4000900940e00c003c0040250188240051032481c3c0181c54610b52640200402c034256102c0790b00503500c2d9030000c80c90301c02c06d140c1107148001c1c0d07a0340342d050303150130398509441c100c844501449070302c3c0328007501c2c86804203002d0510704950701d171080040200202d40c4c036040080c0c01019180d00d09419a102010614a50305251088074040e180400040402c2d179038580e920b0001d0220940c1c410403003030100d80500003440724011840107050340400615110350b80654001d0844010b81c0c8542040c0325407900420101c1c00e41985080548000d5407001c804180907000b0402d60700c680d5204445d58040020386c0c0c4144640403030707 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 596637733 1250 596636483 596636503
    0x705041a03060a050a0305030403020918010e0a02010305060d1a04030212030c031909030c02210f03030a18030c17090a0306200a050d0f061a0705010c050a0906111e 72
    0x22207600c41c94482c03040c400405d8260000400c9680700b0007041c40546450100c0c0d0b503005511040d54140c0c2000c51031403c0c00d40d80c200d451644640c0c031180008045603014010303d5400107058812800c4204036840300840310f0f020090091001d14000d0100702070520902c2490605c00c0042210740d5603040003862888694801c0b940c0c0b040303554000c441480074200c06d015112000d45c050b6540300c082055602080b0b1520364500505007118410400000d03080d2050160020000040b4040c40c1c407890001204000e9a801c0c05010030f070703d480d548100001039040f811180d0132a03005019a6650300050007160854440c8a1581d07520080e00702c07000042043c540c01003055602c0e2070030004209544103510031030901802d041000072800510240043d0000ba03841a40c1e03145548801140180d95600d100340780d40e00d10500801700c000e0024800341405400d01807485410344500c0c08a03e00910504000c1c0051740b2800b0346001c0000701c40030181b00c01d400300003841ca0701d503841802c051580345d040f1066a031229001c2d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 596638983 1250 596637733 596637739
    0x60a180e071508010801020307080f0601031508010603020103060503012a0c0c0b030718180f061503020c160e07110a050d091514070b1e0a05060f1002150705041a0306 73
    0x3d400072846210600039a4054041500c0b0380c0b00545a800301203081130300c010006810140d4403000d000c41d800c00524280018629040005001b905500006041d00e540b030300498001c2e13040c82d09030341d603071410000480100790702c41020034520360810070100c0c0c46103c40c1501801940c0005804100404100d000718010702d640d49a80078000c1d4000310101c1e06015910800d5a8043e28545481803100b050704007614200300b040703000400c16111145800798000c2504117800203a4082201040341c5000c001d0543c8007080341c01241031582c0381c80508120003c0080800d030030043c0d19031ba00c4090b564100031440b0303850380c06026039000701c1c0c92140c01001b4401c02c1c4030b842400d20b221650142d085000707a040c01409280e9490552804c0c085444d00f00c43d00e4400f601500c3c0c40604402030030000400c00102174007030400c030320011405051501c00c00c40070709100050b41c1e11414660031220146a00014400d45d1341103600d444052036964000203031428020b9074030007649200e060000300410701e6032030010352103100b0403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 596640233 1250 596638983 596638997
    0x30901031803081f0b0309030304020a08150c070206072f0a030c0b0a141305011416110111010e10140c0706020f0409060b0a0f0503060a180e0715 64
    0x241c052480304004040018010903182c5001c50800c03c030900c40d42140c900304060440d00259a8000107010390300807501c0000035007022051100714a00040003000a245001c014480100c90002064039240c2c00f9001d034040200000700f510071501c400e401e881d40d49820118045004103802100c0441c12184010000520b81070f2908034500c0c0303045580131054a80205498500a0800c7c41d0445954070524483c418405030703054000036409000010585491114502c040451510001400d0301da0b0f81080072441400900041140021649604d0003054101052404180b104801a11040c3c1800342082895090954500074410001420041c9000c0700c42c04224030340d05080d5880c2c40c840250303a030311611a0100a464081401c1d42c01401e290f140c90940d00d0f2034541d441260104844495108011446c00810010031680e0440d180c1c0f42044190700b050380c1745d8500a0700140c100c0409008078200c070051a41001d1020700c003075001d031503042449400c07202c5480d290000810401d100f100c0300030010b030b44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 596641483 1250 596640233 596640251
    0x8030a0b3604051006031b090c0e060d0f1508070503030c0a0206031f030b07020f06041e080906130806070c050a0b04020303090415060e190302012f03090103 69
    0x140016101d0780584030700da6014595004204007401400500290340c1445441d401d6aa6007400303200d084015441aa40900c142a90325092442d40c4080e502111801f8039010402e900190001a00c8030141400c60b821907540400c000d14800070030200c00000c1c003040c548a20b80500c1c1c0815401c1c03605648d00c00c022681c82039620341c00c2682c0c81c441c13940c4216280e0010051a0014204a0007030b41e00840c2c1202d05410404081e0305020480149a005607489030085080c4540590140590300040d030480003e0030032454940c440740e105486080c0121401c51800d501c0314144401d01094560128005202596980c4550410420701406004640c241d0043d14013154031a8000e0b00016003041d030040250081070000c0c0c032241c2c1548401030087e03815000c10407030180550f5a91040002e840b40750080e01d41c1d030303d0420078020015485001124000e2224521150f01d40200b00002d00c122076091a100e03e580d0317072034410407400d0201c006580380b5250848081c4280e0140100c09040d403010280e90030008414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 596642733 1250 596641483 596641519
    0x1e01080c12010614210a11010815010c0201050c0f030f071209061409040e0303070c12020f1b0418211707080a320601080906010611070308030a0b 64
    0x4528824481d401c240c041c042c5016017007080c42031140743e10a0000d00940307001444040c0c02d18200e08001c0ba00c05848402094644d03030808403103070300b20f0807414050305089110b60029090019114010f030511001007010001c2400c200025110064084242c2c4e4985041e410301c0c4900740c10403402102c01d10903d5200d030070fa507403280c000d4404442c61545c1310401d04880c0e000c44030b401d40c03094030481e4200381c590450050720300701040154051071903582d5008106503030341001c0001c181c1c107081050864100d4640d81d4001a8006801008290114140001c2030541c00005005003011800c4000311a0041001c0082c0300d1580b40003121460000f60090740d900c52007108449404200c42c030216450164004070300960721803000507900c650641000141c0b0f000c294100800a2700d007c0030804645080c0c8860100c1c107503144801c80c2c021401782800c000c1401d00c1c14060352511414050101000348090110140a0040100900a54010701455500d0808843c00d40207400380101d402c1c003503140407400c000000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 596643983 1250 596642733 596642741
    0x6211e060c09010c1b03020a030819021f0e150424050402060f03060102121c0f0b011b03090b0a030605091602030301150e041a0306090106030506010506031e01080c1201 74
    0x1603488203051401944c1d0005410007039a992170541104c4074020005858160141003d0b60041c0e400945442e01d61514a00c08200d990003039046401c03031501c0c4d2900b5801e4842c0031018883c075001c045080d0154104403031400000c849072100c4501540140400e00c0140b600514005107000d0080c3c420035484000750056840507680290080010450000500c08050145810a00502c151086082c1480000b020343d00010343c841107001c0e42e9503842c41e03002d140d40320741441440da59505000305096800041d01d5441c0c43c0442d4000da0503508503203003c1601c02e0440342e0281800200c10741d00c4900341200240280f2440c0903680c0a1000c11002c80ca0502c0c0041d440903980c41140d005510f540c0c2000d100009480d0500905400d101041802541980d0b0300d0045c419181075644040d000718580c1030803d440c00703202810580305a4500642840410008500a1705413101078410503544e4070b03900340340e001e0b600040a464004483e03050000c905c2e044041120021003004171446c038402064640b0403402c03a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 596645233 1250 596643983 596643997
    0x607020106060f081503060414070e060f040b01052203030807080912090604120b070201140f0109020f0c0a0c0609050a21020319150f0204080606211e060c 68
    0x3003003d424569a02504c20004103511030102510f003403107003030307100c010915007501507404854031541134289060303121003040040d00501402e244103409041c43c0c000301d5002030005008030700070740c3ca0f44460140350340240121100f001c90300c4407401429040411040c6884541c0c0021800110300c0b0b408602d910384541c4250740034020040191058200e02e04510030550b10403000b06030850801e010001e2100f80710720717400062500402d5011074501d0710303401c001d01f160080d441c1e0b1104400180140240d07181000000382c152602d1000060747d444218109100500407207014058030f20600741d0840810500c00421000c5903041c3e1610100706456004018464651340600250304400c00d9400c20460048602d4002e42f50011341176400d82180141061480f52002c6801d95440c44d00318250840101a44203e60040124140450034a0700f0048031686a102c0645401c1c8500b400d40d4402e00c116818410300c44503910b443c0d040b05c4044400c540410030a0402000903d40341c0105000504d1b035803030340000c0b1104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 596646483 1250 596645233 596645237
    0x1030b03121c09150b1c0c080708010903020d120f020c0d0e010206090c040b0d08040f150306060e0105070303060506031003051605090105010804050a17030402030f1506120c130b0102060702010606 86
    0x13034500005010303001040042079490b4003030311181c892010f084c1c205202000c40ba00a0420522030303810107100350714140ca0b80d4001900b580c540305020004c81e9003c18040120f10942c944030400c003c1190244000d0604880c0c01c070031151000a205802d00030009104000d0501502d852462969180041e62a6181190000c045410120103401c3e540340607441042d40400040801d5811045900d03110b6194000b600a0500720500d800c2c28088006001c15000103400189400d1051700e052220080481452800850501802144480c10140281c003c000904005000b45840385441a01e01d40451590300c800d0b00d03030b402140180e410b030303000b00031025060342c40144c03006220fa4030700801145d0080009000792500c0c0a04080d8400103042d102c048201d0b40c401018042d181c1c1403600405090540d040c011702c081d0303071080348007590294500d401c895100c50122010f03000b41b500b444840c6d0030b000d00010055400400b28803541d13102480380c0c3c03000000000c00c1e400c03a1050398401b5010780c2203500c98020100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 596647733 1250 596646483 596646503
    0x27103302010c1409010c0f2f13021c0905060a0b0a030506150102031603091401020f0c0405060d0f0506010911040308030c0d0f09262701030b03121c09 66
    0xc081e401100030004040c2c18506961106c1494483c04000d4154000440c1c1c010311030500a02da00220000e01820000720884401200c82400009006900c1740d1655803007841d00130505c0c40c018103840f100940e4071032100b001401000845c0c6082c60b1914400c440100c03029107400351194660408150031005d5035400740c000c1c1003d41b03642e041401560031491449045100812480304646040000941c0c5544261204108541004419a03500700403018442c11980b02c5650541c80075000903044c01e01c09400e8400040319150100031445003090000050460800e001200040000004010b4100c40c0d850908100120951050142030710881c80040c0072507000f800070800d100d00000061050041d10f01c0000b80d48210140c2d4801a40d110aa054034400b65080c1550550602c16000c0b0a0400d09840802d1030080341d07965150307400403251b031780f448020303020280c0d01d040381d000c0d0744000700400000b0f00312283c0e1040b84d40c02c4800d0f40e01001500d0070a254240c06400311841c2e601844296590108842c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 596648983 1250 596647733 596647757
    0x906030c090b03031c0f0f0b060d24170613050304030b0a0b040c030b011806021e010e0613030311070b06010804021504060e01090527103302010c 64
    0x80a003501d81d651a43c940000c02520704081e910392201d4010060008002c60304e0040184164101d4a00707404c1c05603024103014605446507503a01c12545107403200000040d0708400c19841a4070300e800e00207601d50b40b0f00004004104442a4044401d03c02c48840480c0d80325500c0414101c004100d881c0b004016600a120070f000040402d42c00350f6000a0f00d448c0020082d50040025042d61400d02e100400310745d075403031401407659000c0b410106082605001080882ca802c0001b941c2d50f201070b0103403010b00000c10500c41c0061080d0002003d03940124121340481c2000c0381d140089882544003140403a14000000304010040801c5d190101d0304280186181e40c1c2d9a0019942c48000030006c0364810b04402e181c8185102c554044e001409056a030500010710505c0090300e2060550040351240010f0800c0550b08829907815003400000b21070380d52425141d5208000301500c0c00c0c1c0015000769a0f000c04010388a4803081e00c502c0d0140c03580b03800d00d00ca0001043c164200c450711208540064081d40f0a0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 596650233 1250 596648983 596648999
    0x170309070f150807051806181309051902040b041406100309080d0903021c050409060e06130207051e03090924010f1202030a090507050102120a0c0314030a0e070906030c 74
    0x7415038025006c00030380c0f0980140000411a600240d1300503075156900041d44400d00304480403c5c0c113030411280412602881d5150301d9034078451000da541e5080541e509100444d101c9c8e8202c40e5003680041c00510080c00009001c5800c100100c0303d05010700300c0d4105000040f44280650103181e07800407031b2245064904803c90001d404003120a40a40c421641c01e014200a0840030742c1c158040b0303030345007921541407200c0c0350280c485a40c40500c1d00d0490f5400d100e40c03696034441e0585403214000e00140d40318054035009080c01c0d80c9030301a1013200c0460b0b604800300100071008000d040412a11000203550701ea1060342d12a4500104003070f0b00c110800d000c540d950081c180310660300c0a50070098110907490f04002c05982c0300715030b08a0f0054480417650200f003400c108080c040e142c240042c01c0b04420b060141001c2e8001c3e40350035801c00a50b49a000f0034940980c1c0c000390051a00e0049540d2440c04020307107400b030101d1991459036881340001c00507a601c0c1c20302c05d500c00d59070300442e900c052520340285 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 596651483 1250 596650233 596650237
    0x11b0801061b0819110a080d020a17010b0a0e1e0d1506060203040807090605090a050a060306050408031f082a041e0605100804080304170309070f15080705 68
    0x20908142d02003032012000c52105405013910b44040080006240030b4560001c00795040c042400340710f580301050660024000c103040e500c0d0328a46800040c0c8826440c0c0c3c0440311680d045c045500001818000401c048032007030000d0100094035102c6003195000c0b00c1c103000d2001c2d10358070380c0307010f007070001510401c9880d046c0d000c1c03203100f801081e01c091480c0c00c5800c904102e070669031124015910008003004540c005202400081220b03401c101300c05880c010210b518a00c008180001c200d07610b60004040d01015480744000d9504694108003c0c0742c58601038120340d1054490360260300b066288403d100c200801c03540181e41d004409456032103c1500c42d6403018689009103140204242c1c0a007145071103510580450104901c10f041841034954511011180c498000034000e180d00300300e420309260030596541e04a94001d98203960303641d03a400c08444400140086003c010f4000003484452040010300340f0a0750b0150b48a00401a91060407184c00203648059801080300b80f00040c112a0280300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 596652733 1250 596651483 596651507
    0xc1c201003050612030a0306060e0a0e0601110304030b04060209040e0f101d060f040b070f080415090c03080301050a0501020a020d061518020301060e01020309010c24050406050603011b080106 84
    0x120011203107503001c3d034070b03400c507001b1100020000c2d50b00e6804100c601e80c0034001c0887d5800644103004001e04011030a002924001e103050b044c00611580403c9010302002114001c540060424010b07091514040000e94015001688030b40d050a400030001d40010410250845c09180200b205408a0364800041d2a9411080c980b502456482c8142d002c4103002c111310910203080d071030031140342500d041075041401074000001c000740c103490b1519841c4c10087d1160455003107101c49046030406240900505420360303004051305e090150001c10030060030040c50580d90101e03080500e250b203e4004a07642c001070364020758400000d0040f0000714180d0360140404040149400b0000c1d91200c0340014824084c1800c222110350000040262030f5004002d001e26400c2403000d076140070000030000f0700100e00d1141c05001c2400c0171003c0100f03c01120118945503100c480184400d1805007812001030504075003440c000e5003000981e03000203c1d00605143c101d00140c03a0368031503034240700044174800c107551 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 596653983 1250 596652733 596652739
    0x11d040b0d05030705060f0c0a0912142b0507020a030b1503070e090d0305071719060f08160b0711030a080c1006050603010b07140c1c2010030506 64
    0x28807284007050080c401005420300400c01003541d420480210300304120000d0081d015400c003408018800b952041c2080200c9248550841e19520182403039862000100d0240b01e040c850f082000503c9080c01c03c100b40003484040008100f1548580d05607214400d140d402940803501c40c00910000342011400c81c0c2110301220262201260000443e10f4044550030841440100c20200000c01c0000c0211782114400303498140280d00b040390001d408130b00401119803550304880c0014a140c2c440c6803003010080300ea084244000e030b559207100f0214241c28058980e40e80550310103103062800202c3c14000700c41c48031200e5450410305488036400c80011041d21649401501c881070045200e40e0007600301d04400c1c0001d010303544084000107040f241c8550100d40180b0042c03004000300e2900d4021b40d6070547e00300c1c00c0b03440b4440d94004110b003884105e07a12154000034404004042c0c0030341070003030806284511030360744440708411645a8400f01d240007241e40300c20400040700310188282c0010ba04141c001d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 596655233 1250 596653983 596653999
    0x6030709062001020703050403150207150f0e010c050a03050a02040608180c0d15051003200a150309030f020a0f020103020a0203120c09010f0c0804030b0603070906030303020414011d040b 82
    0x901e900d0f03003a07034020802540050000701d024030a11820640004180307084540443c5440c03807a580e07920741500702001c802119980c6880010307100796160840c01d0344280344002049100300c000409411500300701700b4000041d242c03800181c2c6081040c42104d09540903925113460540c0d81d5221092405103071101c4a006000b6a070544840d070711a81018001030344102c1c3c0080c4e00720000c0011904a504c000c01c0380c0310038035038414100f000c2203840d0400703c1c6603040440400c005480700808121050010303402500902d003414000c038045585584070301c8245129680300300304c03014801000c981c1c031403e000740035003203680c0002d80740c0c0198040e50042140381c54900550b070500310a00310028541c64111800f0001440000340c1041569000403054000300c030030700f004d0482200d41d40721500d490081d4080140507002200102b2401d940030441349001b0544640d0a01c951900ca2030001e0113500b043c811808808010540854158092007840541c07803500c1081c0a15061a1020413002e89100001c00360801c2c45 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 596656483 1250 596655233 596655287
    0xc07080f01050a0c020118060b1c05010905060f010b0a180b031003020109290703030b0618030d050307171909110906010519030905100c08040506060603070906 70
    0x50294400c00515000006600c1c07400740f001d2403d4440403041d000440e49031005c40c504464032004c0103403035150461000100c040490340860540c0c1d00c2c460307044c90129610811101080780c15080405498416030541d0040e4541e03e9140d040d0400a020b0006100018464114541d2240c1640080041d030032001c0c407800c998602c0600c1c61a40141c84802120102240074415541c020b02c41c00300510360498030340340342c1c1040c407050314588000980030400f84d00d00007a5082414841d8003e040d2152004200c0b65588003c403850343c00d442c0c41d084116000340901c600c911001801234041c2c034420420b13901c0b8040410407041c5400300c0103400070102880c010040012011450040c807528090510940e50021001090410000c891500506180c10460108046600300c16038104030707052201c00d4140800c0d00c1025113030a0b41000c80260201582c80d1600c1c1064040c5644a40c5060207107000300107894550b261300d001d01c400342c4000c5440f0000b2982100d0300b009114401c600132002141c10094452003031385 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 596657733 1250 596656483 596656499
    0x3070c050a0209390708130f0605030a0e01050402010503040311011e091b031a1005090a021b0607021c05070b010303080105031b010c030305150307030803070e0f150c07 74
    0x342e44244804e910042c0450b4000f5103038000840400f040342c0704006030102818010381c0341c82480c2009000c510003050000004030000283ca0140c119020b003001c8185e19040c00038890381040702c0c0c5040031800c00340f0040a80c101072244502940d0183d489510355034461318240c0e060301c80e0318080c21035076588802c0000e24603004442e000040d4540c820100319056242012611845c0c814003941c0a520010342c10030004a5010030308101d660009408402c0da518a80e9a032240d074401c0d03126130340040c1820f0800a402c1200d60041c9005030014881d0001c51540600e01c0d40e507102c3c102c407044050380c42810301d0342c50f60804201000034442d0714540709151021940d00d8840964080c0e00c201c0103d1740c40c078014001883e0078020b0211007001000071003490709034100005d00071041c0700b030090280b6582d41c0211300391002c41c00c0103000c8070383c010782102d280544e2440d0007003180c0d0048490400180c0d107480d24495a00d4840c3e010240d1030401081003403000c0ca03194980c41e49a00c06088500e4034494104009602d10b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 596658983 1250 596657733 596657749
    0x11090103060b0301140613110c0708010b091608010509060307180207050f0312041205040909050601080c012105130210090302010207050a030b07030b130f061706060603070c050a02 79
    0xd8458900420502c1890b810306003515240580e41c0703030140e90902001001d0320f8a103d1a269000888800304001c24020782c008c40710301c545011080c16010748580802c481c901500322690b001026504c08a180e603400c0340c503030055240700304c00000045c1700100400040c43c081b101d80c0e402c000010103440340183d5946110b4505004070044005031500401e65005001c0180a4041020040c40155103498800700c0300d925000d07401800100181d001d0301500441c10300c180181c8001d0812080304000805c40342c00c00b1583d41c0030034801e66216201d0100504055486a45604400141040d0301d0500503102d14910002e00002003003a40030b001c06440040140e40d400b042400000d00710b807600c10049046000090070000c640e040640103c10840003080010400460154084028a00000c0010aa000048120000d428082e11046c144481d07201c60404960250048600400300340310301c00f03441d83c00350b0740350101102c4059000900340001952750b4000d0700d817224044d11650659050340142c1d40010b00b04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 596660233 1250 596658983 596658989
    0x1080d1101060b0d090204060e0603030d0c020a1205030f060102030c070315020d0213090f0203150409030e150901030501090b0d12140d1a0301140601050a0212040e270c0409110901 79
    0x490f2a1103664041d1f00345031140c0300142c1a01e02c1c0724492440e241d000b20380d91f441920b259804242d61290f10ba20b54501c2071024000da99440090618660501140100385030020b1700c5000a6607400c0010644540c00001103500700e42c4080068004a4030750385542d070205400047c401c41c141c0c0c080017582c5104105200138403070003654001e80f0300b41c2ca040116460441e403202c0300b18290340b841081400b003030b55180c895480840d0800c95000c13842e044140341c1118544407070280aa0420045040b60100d00711305805044103641c01c2c2d81c108070b40da036034541c420705440300d20b0a540d070090310318520103001c40c10743c000351900005c550410102d06428079034469800c0e0301c20301c0d280f0792036a0307100c0507201d50004901c03d5074900030f000c400900c220301108040e0148070354041d103a5030501000068100001e4000d028071f016604405028507141d60b41c0e52455001c0000c2191a16841c000340309a05482d0396004c150407040303507103100091007900029400c0c8030080c00c00003400e49c0e0040c018541004203640d403400b41400703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 596661483 1250 596660233 596660257
    0x60c070b03010b070507060c02010c02100c0b101406070c0308090118091401060e03280204050901091a0114090604020d0504030c060b0d03080a11091507030906030501080d1101060b 79
    0x1583e134150420074240701c516003091040040400c1d48a0240c0e078011440d120450701141d481418084c8200c00f61080300781c0303140082041001c642008650408686c9407411101c0c450b600c020381740f000f40c04220443c0701d00038000b03185464030354040c404100e0101c007034026007034181802805c45141c0d0007094802681c6520000c01d05407603100300003010069200f2940184800d0405d031000c0750000707001070744407840e203144200c10a042c1c803101d0222594050400190701d4000e00204080d09100c29124003904580e00103440c20310040305075052003426487c0383c2d4102c888036141007108222420420a01c50f0002c0d2805a0090b0217000c03c11020000e40308041c01580309480300c800580c128a00002614200034180d03100c1c2c80c2c00400320303000c00d8020100c40d41c0019280700c00031b0f03c8640c04003103840d580249034049030003d000300f031840c40086006001b0000c1c43d0098549003c2c80d640c0354012001e0315000d004100c5150000c24421602d1400740c00c11035042c050385030010802035140c602c0c03500785421445140d18 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 596662733 1250 596661483 596661487
    0x5060d0c0312030f0608030d0b220e0f19122d020c06090d02220606020d0311070f24050c07063204060b0a03030804060524060c070b03010b 61
    0x500541c15100304500e44c0303400403040c04a94508800d41e0340b2401582903c4c080300785c4070700501c0e205ea80c45010524490703005801c0c00004c41d42e05400d00000344800d1102000ea4030402104030681c600002d4045402e0146510740b50340500641d44071b862240a0030740362400e11110311a42d5100004c6214a14540c103c8815011510f80042c1c50003481c01520400032801303010200700d400c0c0d45840300c2c65003000741901039039003070148149520801c1218080c0407800314814a025004291302d079010900b203000f00e03640e903001d1000044a4400130800c0c441e844008109198410b64400080c152101d2603965a990070321626160307000f800340700e040c0c52040711016003003d400242c0504100192141c4140388001d5685e80c54240300301902480002c10f282d0104a1814080001800b00b100e60b8000c900c600c240a031200b511a541c80c5409000038400b52802c541d07803400c01c00025688041c1180c400602e00d503007011000c04010040500680d40e11050b0450494000c0c4000410100d81c40b030001d6000788000c0000396 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 596663983 1250 596662733 596662763
    0x150a0c0f15050609070203031f080f011b0504080601060c02041b0807090902031e191b0e03010504020904021207080601080a0b010e09030d15031e0606080d05030a05060d0c03 76
    0x202214002801c1d00d04c80c18a050900102540c00000d41e40e001c0030b00c58402e040b00401521385507862019078440159481240400010030b00103400003505e900354a0304107000a00d0b14441610750b4001c80c010000136501a01c0100406441205e03205400c42c0003600000701e40c0301a50a455080c5e102c00c045038041106081802a92540100b00710010014a01c085045081c0001031100d440f000308810002241640c01103080e00301e0f203002030403c1310004a002c100718a100c039844180a00e050ba13414000c1111201c15850504040c00385511903030b401480340d801c583d030b95420495400144140400301d4030030900c020038842000c1100d14082d25100005000c6842d50740b52602003400141c200d85c030b40700d20000902c07030200000402c2d14286603110001092034001e11289801c400800d52001c0c0000b04444100d82c07401203840d0403050b00e0341c0501c000380000340d111000d10b651075013070000d0100011410000180081d40301d900594000100510000c6208000d0322081001c1031340b0780042d0b038503051803007542c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 596665233 1250 596663983 596664023
    0x9061812010c02072310020f06010906050f0409031707110102040303020a121803080304030215011e140f1201110a020f0f060c0418111b070b030402150a0c0f 69
    0x10018844001d1242101c164030105c1d828458000800f01d010b0840360000750079481c000e01051030380c0501c4604035103281d03075903451680150a140c4140da00a01414502540600303007801032145c01605034581481070b4489040403488928001c0181e01000044142007045400c00e000a0005600a1327008050128142c1040c10303030789000107121018004007100a05031208a054808200c03500a4240b41c2c40e6501c5040a0f8100942d145000c40000031000000c941d515400380821001e010088100c1c9605403549040810400a1000e01d5030041c1a03a401c0b0549180c030a0554083e41c06010011401056542e00c28000741c003c100d015001d600034480c400c162440812240212000c400014007550034011145000c1d031081c0e000300134260001010445141300d0355002500380c4040300d00d441f640c07901301440c04007a2100c01c4404a1041c001e200001991101c240d0175a8059074000388450420395908042100980c07018001105000d0980c4258020500c8840c10311020350143e0903c0d20280b03540c6000b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 596666483 1250 596665233 596665243
    0xb0103050a02033c160807020a170d1107060c1103090109050409140f07170102040e06010c1b0308181210020a090f231509061812010c02 60
    0x1085071481441004000381018103a90380b00914811130180c55454446501d07005440fa10700708440c200b2000c240311014207044002d120082490755048500c1d12101c004a8541e4901080070388003845010040c868039651000404407449051400540d06a407d00c01100035000000143d841503070b14611032500c1e580103211041c80e00560f0000c0c1d8680061500040c110688600a0301d001c0c07956054080b0421400c801042c1114113a181140d1045503c4038001755118501d003d404025224114601600c240500950f01950480c080580c15550340c507004603950752044109a8401c4240c8250540540340c000029014500031401a070b500c03c00b4803100042c910129001c207008182150048061300004a116a1f000c00403c10143c1c0c0e4035260682182c84038090b80002c04107141050700000c00c00701134800d2402800720040402446040317038041008140c1d940208a042680c02c102c8200c642c546800100055852000d01d641c460001c0c0b00481c1444400341181c092070ba40d02c01041c43d18a80401c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 596667733 1250 596666483 596666491
    0xe0f0631080307030909090f21020f012a090f0b0406031107050a140f030f0c0d140d09170a2c0a030b0a060504020f07030f09151d12010b010305 63
    0x190300d00219668002c1004045e480390540c403030b544440240420403003c010a4840e07400007800040031110014080990481d0740c60b12000d403080e810a4400c210041c091f010484124441b25500c0c0c44082d41d8008108016111210800c072194034003040f540360101c1108050f0203080341560f112400d096000e002c8030b94040071106106001d201c0308001510019142040079031140e440c3c960071005098140c03501c3e501c21984242800086401c1311901d503d040641030400c0050202e41c10301100060a50f00f038440c0b00c0541544140c100000b03203c0703074030395040700c0050781c030642c6070b8088035219011104594100714540000980345101c41c0741040c503103080028007030601038103204034555080c002408111942c40028000b0242c0c7c0002003290a45a00100c01404040c009640e145200c0c507002a0030380c080c2c1401c80c081180c12600001c443d2003012240c094030003040340103c0c4408000b500f581d1001c4810840e03540d5160700f20b07220840e520b030060507002c00c624080000ca010b000100003d000d550f8020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 596668983 1250 596667733 596667749
    0x609061b150f100b16021002250b0f0c0a0f030f020d0206160e030a0203060a0915060e19200d1d0c01050304051203040803070e01030203070e0f0631 65
    0x1000f488500303030460800500b210440b0100e2640c4420500b00c0881c00e19aa4a010f54804650105191581d0300494000e8050148031041c0e920350340c1d0070a0a0418105602607441e4007502880709000d01542c0c0c400410500601000703c03140341929545000b201d22100808400050341d50001714000c5804010744132201d40716001920382490120a20b845803421070407202d041200c884c0402005440c180700340401c2d10b8002e8141d81143ca00110440302030014040225828030a4840c03d40d02410144100d1095802c034101309a007a444803007029002e0b0b91001092040c055907241e140c080801c1035151880d0194013200640d0b150700e00310100f54204d41800e9010f07002e00702e003403c00064a4030007040b084a45035090030040c1d166212410b040d40740282403a0b4400d400540041400b007800b030b84002942c894403031b558401162111540c0114141c1c0001c0e21074102041d9501030001c514034150520b0040c950003d00154149400a1408011206100c90b84c1c24502c2e40e442005d007030801c1488400b400750990b1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 596670233 1250 596668983 596669011
    0x901080c0a0206041e0c090e0c01050307080106031a061c05060103110403080f25111c02130b040c0905030f121902240a050106080903090609061b15 65
    0x4001d01a40310b10005000901060250352104800200305030418512900b0611a0b00c059884018200c014a0311042c4041d10340304130100e464007584204122072245500380d40e00f040903440e082090b000741040c00c2c99400c2c02c81c403d1040c50045e03112074018282020034160000001e04000c00194229100984445c0c1050304000f5403000302034250b42118112584407841d0f6580d1860311001c8480740c02a40a40b800f4074001060740c0d08000c0604d00c4074041180030354003043c1088000300c10401d038640c4a121100c008003107680c0a6002d03141000d0b04094240011002045500880002604842d50b00c1c0450002c1045180300f88a5401c04100180e05259540000d21145e200900c00c00e10785d0041282d080804e00078800c00300c1c4214801e1140350001c0e005011180c50310026100241210300c41210270041840c9040000940a80300c1d1045902490b01e000c059480c0c64045410300038594450020160050b40802c80102d81c1c3c0300420b01d000c0141100400307002c041220305008040340c00082c01c172080324921 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 596671483 1250 596670233 596670247
    0x6030a0213090b0c03010515030c0405040905030714280c080321010503060705120414120304260412020a030b1003050708030c030a0e010e040903030f11130504090f080705030901080c 80
    0x803468a1000c01608c090721940b00d41d161840d85059120b25040305030410304260602c02007102c0013003d4581d06110300c04003510500340071441d5a81d5807030005424094452045420b1000e9104178000240a0040250302d80c01c2d44ca4041840c43d50307204c03140d80c1c02d09245e00c0c04810313050f0340081c06150152108030003800c5075003045580240b2134004d550003860101f1210012408114101c40b0b1254545031960544601102564580c010340d0400c40d810303a404080322402c2980c00001d40c0702ca50200c0300341118103007010304010f5141084003000c4000c070380020002c00b0100200c0c3e61f0365139071440341c40c0889502100c07a080d454040e04241069202750380c80e91003400301c441072141c040140c0768000c3c82c600e011869101803a004072500540c0b180c109400031301d420502030034946d154010b070000d94060301050001009418180b946480b5a84100f0005d80d081c413028052840d142d00060b061038041c4d20b01310000703540c030384804805601ca400c040301d070390348005040202e03540c01288403984102c0040c0401c3c10024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 596672733 1250 596671483 596671489
    0x905071403190609031d0a09020310090f0e1c080a1814010b0306071407140307050f030c0601270c020313030b1e091506030a0213090b0c030105 63
    0xa15004080c40d424549100e11181c0d2410007518030b500760840d074040c0029205083c00401465030410079000940b4841d000d07020342036040c694210481000e003004044c1c03440d04454170025000a8040030003101c0c480e50000350071500f40910821126604030004208880780c10052904422079400d0105082901d038807030703521713400c80140c81c1d21082000020411084d000c10076000c01118040050035080c001c04000745441d01540045281a421760417100242c9540d8402c0c0e80304004641000388015081059070300040076641141c0030482c81d2030460303041140c3e5660309810b2040c034858029440c1d00103d425050303070000f00002c6006240c0645202440310481c00007400c4100458150000c00c0e44665075180c116100300100c0c0e5000b207880d0040307510943c8074604419020400d4801485a5951180f8a08105983c07102c00e801000c0d01d0700100320700080c03203a070240c50050050145074903014004078280562038801c1c10710fa91f0303d56860001401101071810b83c8400902a20300301c1c54110030f04c01800991 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 596673983 1250 596672733 596672743
    0x9030905130b0303031504090209070309020f0103020421051606020a050c04110a0f0c021c20011b03050d11030105042f1e04061709210307200c10030905 67
    0x20080600c00a841506000318028203a050300c025080962ba508010380d040d815071100a01d10701c05c54000035250500c00044080c0e00960244545501a8903c84c02841c0695006407168030320840c01c0e03614184c0503000807000340e02503030310800240e0847c12000041090030f1000d10390301c00d01140c0800420b100100480c1043c000c41300300205009142039129802c03809000031202d0254001d003150340e056000c805090700e1031203000b001c4400b510481405681c0383c03055001800c10002c1a5500700484084019207240d040c01980c0640500800304440c0310800618003e00c80e9211100001c282d980d4542001d12007115010303406040c0051030b4100541910a1800403122032024104026468040c0645000022450041d406054410000b400168035030488a410a002c440110300f031016900d103001103450307400465900250440981044060703211100140d0381181c0a0324100c04e040d410411180001300c20806041429070000c1010886490850007004112101c2c0c81c0600400410355503a942d10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 596675233 1250 596673983 596673991
    0x80a091e03231c0b151b06040501050105100e090c0a02071e0f0b070b1b1209060f07180b0c030f0f030106120b060d0f0b0409030905130b030303 63
    0x121452020581414030400e5441074039080d200c0b01d800e80e4041050020303440e50090701e200d02280d00c90340401220340f20381d1242402d200005040480124010061110701d5481340300010340d4910800034848081404121040c41284180000141541003c04000c2c0d0030307840714808400c02009200d000c071241c0300c1d4205660402c1c2d45d0b04010361030b80c030800340c10f03402c080b00c0b50010340308400348071208540740310120003203005c075038100540d00d0405403940c506052034407802034007034421000c0c1008640301d10341c0720410140720a2800b05160401e020b0a650a83e028000d50384104a64010014880c1040c500e811264001445c4d01b000918030401c4c00f5040325500341c6125034140540040f0304100c2c429810b00440d150010f0450469075070b401a801c00f1100b5070000e006000010752015200f59a07948140b251440a5170002c2002e8201666001c01c1c201030206600344090b03071603c2e1114100f840e02c40b4020a10400d01c00d40701e000136641490103104012410420030b486160410303010b550b542c1c802004407504 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 596676483 1250 596675233 596675273
    0x31e02010c0311010b0d0c0f080d0f08150405093406080405070e01260111182137020d050f1b04150501020303070c110409060507080a09 60
    0x10f907280003100343d005000c500e56070354111080389400ca01b00700b1152006130668045000c0d80c4042c07621602955910300f46040804041000201d413902039a001701011036200b100340240e4400d0190070030101c1c0c19100b0549440540794080d00d07801e03482e071701006281003842c0210b0600043c009200c4001c12071106081c42080d042c80100c038089800d0180501c00f40340130300060140c2e80d8042d6543c589011030112920810070010704507101c140c0c2e0001041c028812988800320100d81003010b28810504c441c14500609640a500f2040780c130140818400c4a01041d0320390380107007440094060041100d0010201c24500007902c0f501c02c6105c50400c0c40d4240005074042e00e08110000e035901c0c15a103440340e0240e20700079501c150035003e2210710b074601035000988c0050300c046c400c0a0505070303c0c0000319580e01406026800c10306c00200b010b841003440f41d50342c40c0519442000b07001468082001c586003a4001d8a0380351300ca1003040003094000d800e041d0488484941040503601644440505051040c09074503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 596677733 1250 596676483 596676497
    0x120b0406121e11040903020c0d1b0b0712120b120d090905010803160516140f01020604050c130f060f03111c020f060405041802030d0504050901050607020301150e01031e02010c03 78
    0x141071080040340082440070300301d927885145509001c071800c80c0501010b000006400c0e07000c16042412001d441205503c0305114903480c80760401076421000c40c0c034100903116a41e5080c44090b903070380d420f0702c80c030a0056806071103240034049004002c844c481d0800c001c140e003494010041c20000004480020714188208081d02d1007074038005050200c0c1d20380c0c1e0340e022844a000414038041000b4904890581190a5040c0e00b60f00d06c0166181d000c216401742c09608003080881281c00c1015120400105200e170000b207809487c0c03900011a206034000c1d000c5c0500e100301c02c0c01084007004026101e840215905036400b0307582e40b808a82a500f4140003401a4000402d0800b5034440106a40c02307030a0003441800b03448040003010a210102c084242c2c441d104030000c00441500450444042d141c010308900006e07030030074090194642c06070b0f0301246c05660749d10295500040c00c40001010304158041c00602d5455070420b28100309002c0000141001480f03900c02c0140e8000c2c02012449a050030000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 596678983 1250 596677733 596677751
    0x70602031308070b061f0215090f070306050a1a1302070204060e0108010f0c05030601140f0d05010b0a020d02030f07031b170a090806060f01120b0406121e1104 70
    0x40012400114010202d030004a40e280420640300307201e0388102000c0c0e03400300a52070950142c0c180c2d00c0031014210b0258203c3c9031450301c000d0003602465800403240d0110741e80350800b400350340d00c1d2105a40c0306944083c1d8400c01c2c45104d001600503c00110701840345041400704000008105a001080e06c80300c182d40010302604544031500420020300b01000c81e030066607541c0341e010340a040900c840700c04282c5418145040c0ca4005d0050743d0103500306035030b608507540d00c00b4528003059110b000302e41002c4109100d840d08140c1300303004050103080342c50f2800b602c9244200d00640740c0203a002448040d07401c248480c0c8000f40000040e59445601803401e5030313240c02c103000740804411504c2800f03410b2240302071880c964000b0401c01400d0700022666444407150795841d665840380e03030680e0110b500400c1104402d480d0f41c8100590092000c04520002c4d0307460345400024200e030995446603803403818001e8150240659910f00031044c0da940c440c0442e0070105a550820760f1042c0900c100e00c0b890703580c00d241e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 596680233 1250 596678983 596679001
    0xf06090715110d080613090b0c0d09061a1014090405220602031e100b21040b04120e091b070501050a0b0a0f120f02010e03031201030b06041107060203 66
    0x342c510542d0980a5880e49054100024000c1c80c0031600b10f0b010749044041501580b22510580c1421904004446065103408084003541d034003d8042d82e0b20980c4801000000c42c0170b51080c07010107031000d040da45c2100100c80a11203416130007034440082c800b0b070780c21030411111120220b940103001110005170710350381d0360420381d40c0700160b00c007907101e032b609168243e002c0007015402140035102041d4094180d540905072903007480c0045a00400c001103c134010002045400094561000c20040003031095903c492480c1001c1d0040360f0a403207560104c010303c001d10003205140d0001040b14a044082c418843d008912400c001801c145803c10b0071440c1b098158440506a84035140d200c4001d102904058a990014105000155210710340324407001401000c0d24a9101c11203000c124021005000c07900c0707100140c200d83c00142d0510013011407102c1c07560f81c207000501c410fa0320304940c8915035046040c801d10780200144464000d0b0300e0060b49018207045401502c0c401503100300096580da44034000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 596681483 1250 596680233 596680247
    0x80c0910091e0602010b030a020102150a060e0412080c1204030c050f010f0e0c01090501090e0901021603111513020405040c150c1101020607090b0a020705100f020f06090715 76
    0x82040d210302c039001898202c0300e19000304102c0d5051390003070140d0604101015110815604000d0140c0c0c44400102903400c01040c120358403030500340e400140c00395240d00351000260f0440c1e0445003000a1400501e420307420603005901702910000303d600b491101181408405000f40c0061f00740103a18502c401000401c0040201d1200000c009118030390034420ba400292494202501d2a8000e2411f04d600552040019200700d030300580d00c0e0003030146001c1955000200150070328034595000c028800d128510f20801c2501c2034800e07030750100d89040e929603003402c0500f80e280118044201d0303400c1c000c281e0048028480c4554045a00080d10f403100c1c60014440102d55002c0c807000200d00003170310002c507040344074803100f54000c503600c0c0b00d09141180120b80741c0c0811204000400c070180d4050045059110250840c11081d0046810183c3c50740d00040d114000141800005030f001d0800f510100e505012000ba00d96803800208a07602385070f0034164452210b80100200d01c0422202803003110701c6814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 596682733 1250 596681483 596681489
    0x30210030b151305031c0e0d03053a05161b060501080a050f070506070611070c0f0f08030711010c1a0f01060801240503130c150906080c091009 63
    0x140c06a450581a241003c145014401c2e42d200b801800e02551034121409158401c880d038640c1d07090201c002072000c001180e0541c40b01a402c211007030106a201c949140065101d116054070088900c038070780d0003901c410350100840d1504160400090007600d2660000b0300b01c0c590715905002c1d491208081d030401504404850241441d4100300002403106c0011540210840c094416900086021340c83e0690b100c885100e0143c1200c020030000c0003013050795004441105492440c20310308203da071900c00303c2000681151804031807500d010024003d600340c080e001040150051030905656843c0c090300d807810b142c40103062003002c015500401080b610314500c6c11101c1030703450040d4101440d00c030740145024021342002c10010000402e451607100b40f00180780c0c18a0020400380705803200100c5280d0000b401c454845d00700c40d106000001c50309010b100180907090070942c0060b42e0003800515400c2d00da4094010300c41020148500c83e0700c01000c64503a80b40039a0780c02000d80031110700b116280c0c0103074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 596683983 1250 596682733 596682769
    0x5070f022d010212070311030108070302061e0a110f191e0c090b0307170319050c1e010f0203010e013b04030f0f0522030606030b100f030210030b 64
    0x44c515503580d82c4a21250151043d03580801415456054820f614030003800303a000039501c150401c10061401c14010034000c8a24010806a039110025084071500301842440200718413000d04403a86404108404aa02201005000c101d030300302e04008401040304000b900c0712940312140700003072005080e1017490b41d40c00f040900c00384c2c0d62084140010704000001c54400d00503c2c1c4002416018030700e2170360303010108070040c51400711a12074907500d200310880c03003909100042c00099199007051241d07646103000141e04400720003420004500b10340300184030140d40e0f4412300041c4006041c818036141902c03030038a070f4a00d6101142da010001d442040000348403005113441407601480501040c0c5010ba0300c291190b41c1455401c1d8005d03111f040002846170700041e0184140750500d45e058a41c5061061845a4628001d450303450713000c1910b24a40040e00d0030203414090283e8101d802125000a1078000e404003551810355001801200203c03050504042e2075401d0724400b642c800070082018a410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 596685233 1250 596683983 596683987
    0x1a040203100b04030c060314150607020d0501060605041d0c042102060d060509060411090607060902090109020a180f09090305220f090b0939030a05070f022d0102 71
    0x5c1c500b40d0311002d81c0d40103200009050241a060300802d076000240940c011310340c6018070310106020300107260410b000036613011240144100120750280300309809440b2075030701c041da101d007090004032800103462600c0586441d90010007420040c8002981c054425011803401c4100100a0360141101001c901950007000002c401d00c031522141c0c40032080761025a003200740c0e9034a002c1007000700e8a4101240c02e503004d003008540301e00c5c54170303200504602d03110710000500810250017040c2001ca098002c0c9110703a0f40043d00750181500b041c9000c081c8071031410001c9000e41007214008445040f80310b244c041c65102c1c00328008050103070040e40d070008000629007040d51000600c01c41504050300c20803503403d480381e0012600c071904c0c0c0241c0002c81c038003610042c0c49490700d4140c60072075261031450015404800e119540c0381c00501d0603000301e0b80070307140140d03031a414002210000c45070f018180c181070080e42003101000d640c0218545050745820b42883c52440e8440b13900c0c0250002d4146054070b55440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 596686483 1250 596685233 596685239
    0x110c010e010513230301090b06130e0a0b150a06022a0904060b01080a090b01030212010e06071701120201021c1b0308010306060b0f030a09171611041a040203100b04 72
    0x160b012858901e901340328551154403403c44c10705080300c40024001d0714142107600013500354100229801e6841c0140382e00010542010140b5904118141e4012640300e4200c100344005240c002810800121045400281c9940742c40c00103947c43c3c42e00b14409000d4001c203206112941c2100c680d0142194001e027035103a40d8505450000c00801c00800ea0030301080241000c61186106032203412035003a808008107a49901b541c08114003c0ca00c1000c1d4003041d9260381e8130700c1200d4402c3c4411800341440382ca809100c0aa01040c07680e0240c0c0507089610f0308001e2202c01c5000d84c0e4000f80721840d003450b00804044504550000f150f400ba400116074407103003a406615420954400c0b031560489018140401009071103c6450780d09115038000c0d081042d1051000c26a0301031164030807030a0f41c0c0b0841c0b800885c046260803c20b100c0d04200100001c4006102119040c13141c8810b500011001c1160100b2000c143c01e0010286034000080003030180741d01100080705000000e198001a02c1c0d0b090341e01d5201d5503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 596687733 1250 596686483 596686499
    0x18131806050402010e0a15020f010615110705030d0801091107031e1106090d02010e0303040c031401020d061805070809030406030b0f31140a05060d0c08011b110c010e010513 76
    0x43d07031f28040040c842c50f40010748070300040c4609400c2d0b035130040341c40020031140d800441d661491403142d80c845020f100c20010f51547c0411840241500c2034807001c00c00d40c90300191a0880d07180340c0c2c00e01201c50040042e40000f07540030301062007001d1b00300a040703008074451004a42d08100307044090041c0c4034980521559134000900c01012142c694024415038070706142c6140c4038041a030b0000c00600c5c4528041c0b000850b840c6035035892054401c001130406103800c2d0f544007a00c80ca50b01159200710b03a12a144c2880d4500c1c0200c40c0d1183c030701c6c10000d400c0d0400c5002260340c1c1c0310740d1207076408044e82d40c07000407000d40d81c092034684844002003c0d003134405030b00141404070508244c101e000c1000c040500e900038007090701808004e68144500d06201d41d85000c0305030081d0100800305071340105408111000200c482110320080c0c104200000b448035032804240e12170309001c003c828207100420001d00740c50314001907001c545500070318080c10708040070380040e11540584142801540b00880000c20f20711 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 596688983 1250 596687733 596687759
    0x5120102070209042111100c02150a0615021b040b06070204150603051308120601030b281707150e0607050a0209010605040e0a09080f18131806050402010e0a 69
    0x349100a0110302d410104019100449050166a51500280007d900e00b05032588110038107015030040e2040e12030f0f140d4444421080c1200e20035241550f40340d05000307804050f1216820041d1074001440e484012210503421511020262031250783c8036010942e0603200e05007aa088140e02070402d00251400450a404106180c040d50300068505000500c0528503401101c04076500007603128a4440301000c41850b40d0801480541419102d0030810ba03240c40c0d103920800400e00b02c0210200551030003e846440c40c842e0380c0f144c00070040d03444001110b07a00220304401200e41d4440040800c0161203401e80300c0400c15580a0761190380810408184400401d0348103a407032084500e1615681c0780e4906455500803402074540035598103001074002480307a481840443e002d03c3c00c0302e040841f003a025070019806404c088200c000d040314807144608200440144e151784c03103001030022980403106c00d21090340488000c3c001030b440d80040fa003035900911650400c0c040c080c1201d5804c2c0e0f11135156000314 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 596690233 1250 596688983 596689013
    0x4020a0512060a0e04030503060a030f05030c0d03050106021e010b06043f031d0a0b0d050a020405151606020a030b12070e060f06040b04080c1807090512010207020904 73
    0x181900700300103992440d0001c240804c0c0c50310a10928616103d030b8400300c0c2c0c1c0360070043c000d6401c50881c94010002c5100c05039039241c090300c204004c5903106417000040c0d0800c001107020a060509260050100c560080346151600b10740c41c4a43d800342a80000301b5014050200c9000d400c41c0d0002004540c003004100042500e40c0c155602192004c0000482c0905c0e100c1c2c04041803841c4090781e030940c0020700c1602a5000c0e030443c41c0790025141642000203401030000d0f8840000034500260007031901145000b21544041410301c1117082074034000c0401c01c14081e0b030b21892402e040000c0ca9001144d9440c00d078854581e0060821034440d507101d00040c009002038424144145c6800d0a070182c21200003880300c1c1941c00c4075506121540700d601c24050007510304440c841c0d0000c1c0900c004201c594658014200810080c00103001440e24070080c000c0d0101c0c207419200141c400700c1c040021148c0c01c80001d204462040c0c1d0344c8505000400d00c6a40240513060f0003e500c03030086002d000030302501c500cbc07144403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 596691483 1250 596690233 596690257
    0x30411010f14040e13150506030114010f062d02030403060612020f1507020909060f010f030803010b030a0902060c0a06050c040f0e1003140d080a05060904110f04020a05 74
    0x103401c05149081d00d58181d941c2480d00d10060811040c031081c424080c000750019188222205030300055910b50b10f0081d2114036001c00d0036918410441c0740d2a09004014000d900c8011480455050102c000524a50340c000c040c00c1c0710072078214802c0c0c1040d03a0300345d82d01e9020b10300b860000d400c00610000d480354058801920500d040c80000308400b03001c94417035070103258010f1003d400d0305402c00030f000e001a0b43c41040003012034144000130242c0c492a101510811440001d082d082c40c00461043c079020040c2c0041000d0400d00c407041c130000322000110b07415140d580545903103960320b22400ca40500034880e402500300e4030104000451507000254141942e128a405200942d90100300c60301d18040c0c1e03c900e2540a0640e04100300303605080071215000020706110261064580d140e042c242d145040401000380c1c400c42d01c84140b26445030034150008402e03034040c807150a180b0002800920060806000d00d5944040344103182e845200300e0100141c050030079500d84105000c090400c1e00300b0091804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 596692733 1250 596691483 596691497
    0xf0b010e1018171203070215040303021b031b060906071805060705030306011e05070809040b04020c0a060b01030209010c1b15090501021522080c01020f09040b010201142a03041101 79
    0x28212544040e0303403044010f64000c0c810503a80070511140303888027034015400e05a007044855110b2104c1d0040790451504100210f50702c80031444410350500c40910784030302d541c03c070606000b5071500100e03003960440f40a15145405c0824018850820017040d8030035a81301000203000c0341001404405184203802c00d0305c0380d00d101142054840c0700030450344000030000f90100180e0000442c0d400140c541d00101800000e5415210000719040b64080c80185d5120b612110300e010070081e0381d00941c9048a02880c0a40c10130f001000042c100494406008103200380c1d0104a07400c1da200b01480304024056001d90040c05210510003400010403400b0f10b0303005024001d82c9091554045103260b0003200340188078140300400b00c0d4281d0b030a0907529021511091704012101e480c441c00d0018002c982d00101965903500c0042c03007084115119084a18156410807281e25a82a00c800c1807030b502030f00c5501c000300da408032403103181081d80e61500708080c1310030044240b0040c8201d0000302c2207203e46c00c2e00c90750 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 596693983 1250 596692733 596692753
    0xb181902091005060301062d02030712030207080306040f1b0f02070608150d030c080a030203061e031513230d020715050706060503150a0f0b010e101817 67
    0x65440b195001d05900b02c1c400b000104070940c41151400c40c0c0c48402c007410007440032020750b002080e400c20084d0741c0043e4808111a01405140394101e0388100d41810704619058080c0e0310903d181c08001c005074030507035035806504098034150b00104214200f1003120411046021006428070390780f41900306c010b00c244100400c2050160400f140104041820b09080e94240c408000142c1ca582c0001c60422940210340c100181e085001b41825007a5500c01607102d1500b141400361281d00800c00c40414024444031201c941c80110700900b03040e07862215547c00d03540c0c04100320421180703a4001040c41105022000300910456802d140311407034281076410051030f2410480e81c88407503010700401c580056001c140c50300e01410007084c40c0c5100b024003140d015036410029080c50029194031500300314190800c0b0100b05a40b240440d1107400881c10005001001d000030104030341142450700a075001c80880c11400d019040c400d0042000f0030925900710340714030000d0346560018207140090302c1128058 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 596695233 1250 596693983 596694001
    0xd0f0c08120301120201090e09010506031207020105031f0f09050610021606050901031d0604020a2405070212120d06050d03050904020711060409020c06011a0301030b18190209 77
    0x70030010303100c0700a820369003031100f40d80c640c1600000807418015a00c0340000d00070000e1514512814004c000018070f4903042081c14180715030428003c444000c00c10840006072307004404c2e640c0100c0c9040d02100f000b00c440c4224a40c02880b500188901c1181200c005044d00740c680005204000c00e80342105e40c2d2492103000e03642c46955907500481680000b1060240c50b1040700604002681450042a102442c0283c0d0640400c200741454058020070204419401c0c550007040003441807001540c032118188003804020564480090701b00180003900406555990b440308040d04c4442c016035a00c0d50380c100c10440d1342d9200c1100708946605040300002c06d490607e5615050a4040e04c0d071500d40100503040000a520002c022107050080b502d24400c0d688a041c0504041c00d07500c10016543d00310340c400a894010160b000c3d20601c0c005001c3c2141201c080313010f62f811a41c1c040c007120300c1e80c1c407103001b0492001c01d5200900b47d24862445403842050b84840400400ca00945c1c852390b103074071030b0380c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 596696483 1250 596695233 596695243
    0x709150b070804150c08161b060906051b030a0203030106090e0412350a0f060f05060a050d0c0305100501020a0209060f2806030605090103120804020d020d0f0c08 71
    0x1c082d1000005001c1085403904041c0520a81d100c145810300216550b66140380b4603030004816551004401d06401040109020510084401072030300f00d01d00c180381190041c066a05d500822040141c0030495041418000317004451140849080d6074070b5080c03185009503a07802c2485080c00058240b40001000d020050b038690055030403a0050a482007900c0d801d0354250443d0891420032402d00c180c1c1c07010521040f224020500d00e06541c020a81409000a000d489000310a030380e1041c68060708100c0320a070000540b046820a5450940381d0302e81075000d80ba54040c0514200c1c0f401e05113840740d000181d0540c0514032882d280b07100c1007860f80e110742c01282c0d14242d42d40c0c001d40151802c0e012511034034000d40028103441d0004d1003072040c0c0400d50301e008154128041d14031308a41070f03180f007441419054051710005c2e1000782e0711550150702d036841b0361110340d001c058220240700c0908041015510780742c6292102903000341c444005487d003440e01c0f440012400e081a916052842c04c082103914010070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 596697733 1250 596696483 596696497
    0x15140c0c03030a2c0c030f010626030f0a021c09030201050d11270909060702030a120b0907050d050c0405061c0b1909050f011a0d0b030709150b 63
    0xc020350450742c560000ba03009100d0804107081302e1805800c050320b078541c1c25220a0b591201540031305440c00c0c40c14189403401400b4060240a030341444801d101003070164681d0403203541c0100c040c9110380e240d0300b0018110321a9110221f00c805000070340804035900002c5440485e84481c24071001140441411039001200f800002d0000d281005280e10550560700003288540102e001c3c1442d01541d040080b442d1071403410b0074103d03c64180000030a500e4031108065020051801505003032800fa4002500da00c281e1405409005400d403001d0703c99004c983c8010401c41c00944410101d060100b40949542c021a62001000d1f08010000c2d40008451b0203a5044031030103800b07076081c80000e032000d0b000341c05101840c2940e10380d28400b20724203540e154220032082c1011030034580700d641444502e02c1a1000140490341c1c43d84030340b004000d90015200848403e0f01409401c0c1e0300c80c1c0d100c040c00000741c00e0101400c0e51510500d14007140404140c0c0c402e40e01812a003180d9402e169803083c6554131801210 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 596698983 1250 596697733 596697757
    0x2070503031903052e06090816030f0303061e0e2410020c0306041b09020a050702040c02011506020d0f21090f1713211e15140c 56
    0x400100036460284d0010341d08512034003c1803001c0310080009082c0c06100003403028a881d50b42c00200085504036104501a280c00320291000c040301055006007400184002049040c600103040c003418480d078040350140c41155682d0300e0001e481e4016075000c04075400b4070010b1940c00c00100d50341d102589641000004401c517100903101401c020000401070407000c1d40d00f50b004038096400305a40c1800364611507885003a03000030005414038104c4590040e0341000a040780704004070342c07110390080d05032a81180d0440e804600c408001c28101d000d0004182c0d01a2046ca07084404984540c000c02d03e00d0b42c0150b1503480c910f44428000c0d08035a504880c441d00c00c1882a138020f80300540e030085e0480c0e003017180980d400314080103c5681d0200e42030344604d0751a904020214450314220710800b02e0f50001c098103180a030342501100c400c8460300804240003090f0b02c5c2d03243c1040e001c0b003d82c0d50124103859049040410941001d20002020b00b114a40c0183c0b0713840344800103020540d1401c10344d0f02400c168 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 596700233 1250 596698983 596699017
    0x601050414160e12030c0a0c06140d020f0705060711190b060603041e05030903070902030f0f04020112091a010506030103051b030c041b0801050604080d030b060f03040b070207050303 80
    0x70a41c1a200e00e0b540c3c8540c550030440095548007110320402c020302421202e90024242051541402286402d01d500142c007082035840d400340400200c2c4e41030720540101300500590b107100042d41c00e01d2038458010000c090740200010400741e180c108541c1002c0148030819503c0380340707050f8503c3d142904442c00c014445c00c5600c1c0440c00908041000d1940039100d11100c826101c0012030194a0302070b507510440d00c65000290012150600740b2000340208032031681941142030100c0c7c41c04c012400141034440d00380c1ca100008083d680300da1250240500d00c04000c124003289030501100b00b82c1c1c84191903024004400c00001d990900c442224103e98104000d071000364500c0300c6540198410058840d4144500e40301d90140d80d80794802c0e1f10032285151b541c0100110003100150549005074012442810240410080c01102140b0210f60349004e1a00107588448040012aa80900505031000d010040304010030041c803103281c0707401103109400300c4240ca5030b618209030340c908c5802e15210003034040e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 596701483 1250 596700233 596700271
    0xf050108010615031e1503120906050f0a020c04060b07061803020606060c070b13030b060a050f04020d180609140a120e1201110301090b01090302030d050a090b0c0601050414 76
    0x130030303804100701e029502507244150002c0902007060f19042caa5940603107109103c10020010300e40203032001e00f042810170f0f242e418078011001d4401d004951840718441000103c2c902054800c0c001c0000c0d40034010410800581c81d194048960b821400045030b01d117141240700c150650b0210078060015a040d40100780681c0c0c2e2406208440d001386079000724511032070f07901103001c413403a001130080030700f00d50b4414005514604206a9501001d80703000c0c010324111109011544400c5420000c600090742c0160b50b61070308506003002002c1d882e00400d01c500d2002d00030000c01c40b20744c10201c480c0c4d0280100405056498080548a1000c01070003081c506840c41010b40e00d6010b007860303101d0314078010407030021a22544051420740c0d504a60140204c1070010051242044500c00d1780da5021082c6000c00f0354504660100340c3d504585c8103010203010001c2482c52a10b4499120034000e00f59140d4120703122048501324917a1082d0a001c2c00703100b1402c11a4140069102c0904544211981e214030140045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 596702733 1250 596701483 596701487
    0x30803060111030c030c060a05011421030c01091101270e0c0403020603151f05030406050a0b0303040909060c0c0f03080601050f0c0c10050a020d050a02010b0a06030f050108010615 79
    0x3602d0348031003225000c188035060710004140082c1540d80701681c00b91120746450040d80d0308855050300300f0b0344030404280316200d4a03166058500c014011184403002c24000d030300b0b041e510f14010700c280854250300345031b002400c0105c544c1045800c043c1c282c803205d080c445403100c0c2000494904034001c03001c00a4100c02c201c5c1c00690296260452600c80e0710900d03243d2690041682a0300841d1840411000400220014103201060250502d8003815203120300202400042c45844091b101908042d100d00214600307400f03a41c0510300307200004007182d42d1255940d400c83c2c041e001d1041d00f510000e2803c05090440340c02040b001d2080390384481120307855001541c0c244c46500024042c94100801405105046001e40000b0b040700c0b5840e00040410b07624020402030510044444141004003d10040158540010f126144000e41e0304205485a6521004134014040c4050003944010480c00c0001c50030f8160f8811080b15071014001c0c410f0f03a8071200c0d06400c0e5007291058560804840801d4000a8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 596703983 1250 596702733 596702747
    0x7020f120d020c0a1d0c07030909020a08090d020c21071502060a050a1509020a27090b03010209101103090910170c010212070804050306040503040e090a170f0d2f03010308030601 78
    0x18400d00b08820700c130391102b1555089820040702c01010610741002e100c4d003060208006107404074a8802041155480c1001c40d8401355903045120f03c82000c01c00c128a8003c0c140301620240108440089004034407520095440005403881c9030801e150201007803982c9070500582d03501d8403c80403400221032a06040e40e00a60104a4040421841c85c002a00d407440f0040030485094842184400c101d080c58008021107218070591403103a0f1042000604603222031103000c031504d50a0810b013503c48003070000720b800d5124101070309600a54640401c419000c1000c1101c007500c103651600b2040d40704250101e0382d90482c01c450079002d40e000030160310504445500410403244038211903400c00d641ea401080c6010b03002e030340840f0680c10201d03040c803407100410380d01036021007007400521074201991030300240500d0035010f84909490008100710354031340170400c130394911610340b90800c40d0b05040610608824100c4804405403401c1110800c40004e405050b64141d0360001180ac0c5180c4444005588003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 596705233 1250 596703983 596703997
    0x2303013b1507210f060503030301030f0b0712020a0c0605070f090e070504050d050601050103050708100501050d020f0c0d0905010f140a020f03040e04030905041107020f120d020c0a1d0c 81
    0x510b210803059205540c0f00c18800180714024007040f42c4503262055020f84040350415070003a441800108041036540000e510302640000e41e51041e034072040c5044402d80c00d40f0300000a51800003526a10b0254000c010480301405a2401c01890710f540404540d540b60300c0c544c503800690a40801d0000c0e680000d665600403209007401c5103410b55400c042648000d20040c02e58040c0c000c1001000309581601415a0060301d034900312101d860503480642c8103c0c001d024460401c0390114003e071888096a04440103000c20302e200603210741c0da4440c8543d0b245a51041100040c1500d4800036803540140061092071100f03486111202041010b204603540184041e030b8110310070282e0300b20640400b40010b0002c2c1298a03101c85940c40c0600700a84071420952025004038540210032184105410603130b09000da04455080008858400042031111500d820b05254007405209501040c0c000440d0605184183e581c071643d1a920503409040c00344a10256004991080000e401448000e004203a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 596706483 1250 596705233 596705237
    0xb07030f06050a08011a030105010b160f17030402101103070209060f060714061f030f240605130510030b0406110d0203010512010e072303013b1507 65
    0x19090ba6480026050b500a6000c40400d940d100f140b15031444585440d181c9211054009000c0c551401c24400f08034440d84c025441040312141c0300c4410860b203500c0300c1d152140c0100b0000320044180c949403a141d801035504034481d404100c0d1180300c1d0750090b00c40c0c4005803c0180910705001c059020300c40c020600078911540403510b1700070f82e443d40e40e17008080c20005020310131003203a00c040800300c05d1810501401c00384801c00688041d11100650741541c10a80364840c40d0740340b4420007850441821261102c40c4c41540c0e86180c1d10901c50041c17580254202e139030888000604502c002c3e001011940c0030b4034412079610624605202003805602c0481d0454441c01000412140585001100b50400880d0220f016000001000180f5002e00340e0080c0201540c001c025402c40c4c282125601d00c1795208003441401c0500c0e1a4080e81c0c1c2c449412075956102500a00210588120171038030f10714100e0b40304400c1c15119460350706413110711074408426544080208010302e400c000404071148000c5c40e50742 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 596707733 1250 596706483 596706491
    0x20d03050c180a0521190b07110a020301140603150c040e0405151f090203071d06130f2603040b0304060e0f070e0106050903101d0a0c05100c0b07030f 66
    0xe0039848080400744060b1800c180c409905c446440d185003070850b042030340c2d80e800744c0250315140402c0d200b488007600584c10f8100501e2410100001d0b03400e100d804100039605520f0040d0960240d1000004a881140704400351601c401d006503034006081404d546d1a0b002d610240418080d882102c0740c5c2e40d4200c0c0c0284d044503034914140c00c20981e0070908a0b90b20004a114038003d0441c1c600100030b81000c0e121740c940c01d60443c640038000820700522880d0b441c0260708810002e02e103c0e290941200d4812072080d0075030703010175115088140403c5d00b034880d0144028903000c2000780814001d0001c41380c85102405185081e00c0d0503a91501500050001c1e80c425a8404120209801c204500c2d40c0780340258000d0003510780f401c81e041e192074030305034800c0c0d0610104102d40c00c6203603004a01d4000300b2004010000315683c140110754040c80c13100e00c1040c90303403040c01000c00c00d20036049110412074104403560b04070a84840c0c021640d03070840c208000d052180c910f0200740c100d406a08045002861400002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 596708983 1250 596707733 596707739
    0xb0304020609090c0c060c030736031a0604110307030c050f0c010c0e0a060c02062107021f14190f05070f030f0c05030408030a1407050406020d03050c180a 68
    0x1900c405019913a084913800d00142d0056101414003201d6404011070f10700c542907140450700509082c24910040d01c1e03143c498084801c3c840ca6016003040003a40421a05288a0300d07032420098500c05100d04004401d4210000b4500c0e1802c2e003d10072410b503003181807500395101c0340815405802c0c0b4407642020704c40d05005d030807001181c1e00050448d084101c000494076100d9068042c045280c030500c8280a540e18000501007260800400215294180c80c0c03035903a00040649604c2420b0f0b070706030707144443c02e000381840041607000940d01800d4650b0502005402c00a846610440300c040164894044c1d0200005110610301c01d20041c61200e03ea41c042080301c070341e40b400c0c021100200d40400219080c942684040c59161107210340350780041d041006108140034000c0e049010082c001081608008001940e0310307035075080809495840c03407010456040440009e0a581c009000f4540184a4025601e075401c4c441e0007414002d03800c8140151910a050b8002c408605480341c42030703000000d201d000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 596710233 1250 596708983 596708989
    0x307020a050a08070b10080309061b01020a030c080108030408061303020a0f0b01090605060c060a0903020304030c0b091203090a0315023001050907020303191b0c11010207030c0b0304020609 83
    0x28114492050f4103e980d00c800c1468000807111000d004001b00c0905d1140501000c02c00004940411404507a07546d2168440c0c1c41c680d2499801c036640713400e25400811020305068244d04600f480310080c0c8c4410308543e80b40c1d14002d584e401644503010256004501042c1e41c01808841644c0250191040e111444020340350440510140c01048a01c0d185071801009802e48074030669001c3e040032200c0034034045621b00169514000030b01011102a585c28928003018000c1085500a42d0301500760b9030b00983e945402c1040350807030030740103010740e115030240e803600c1c5408000c90709401c900500c00003040e0705640300e01401d0305207881c20402040d03003002003400408001c45020101c00d103003e2448484410145600710004041e84800d0040c1c60031010300c440c40760003000340c0307501c84940109241200c03c0c83e034002c00a4844540c0001440048a04001050381d016840c0034505000b0442c00320b04401210048bc0e0720502840050032a04c24001d00703000314580400150f4106000900c0c0d1418a40703c8000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 596711483 1250 596710233 596710243
    0xc03120507082101080f060406050c091005041a190c23070503010c0809070315091a060108070206011d1f170c0102010c080a05040606170a03030b0d03050a050307020a05 74
    0x1a01441c880f1041000e010403451400e5280501310102c0030740b2000411040c100e41d1031101900007401c81e034460380020f00400c032420980e0f03a25000100032045d00071114a015003245e2140c012404649000792640f54a03c0000c0102c900d5180f94860790407450307240b09030440d0001e110400458913803008540481d02c07010f80411450400d80c40e10040d16100f46480c00701400c4030881d45070602403140340e004010110344045610812250441030301c0d03104400c3d21490400500050200508a0072484005898414a00d050a201d00000e80741c0750541e84501d1070a230303070f201024411200b028400e904814940100d079100340c0e0f0800c040030391100c3d00c903c0000c0c0c0d8409500310b5400c20020320350700a989900d80e100c1003200450300c1c103003800200100c4405100040c0024001040703c51607503141c202040400c540c61380250000c020345240c040310340340404070072616a20140c80980c0000d041c0580c048817031800d108019103141d451b446240c54180407840c180c4068100034854801c2d40590020342002c80e406008d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 596712733 1250 596711483 596711497
    0x5012601141206100e07030b0d03120e0601031e030507060c0e19050f040b030f1015050603010815060d050d0507140a031202090406050402070c0e060d0c0312050708 72
    0x45a452001050002c1c0204801c40d12242c81481e4440790a103e0403e0f5101c1c45502654620407120110f6076503010154040c21800744156040300710030a0341014507902440e100c8004000030302c181324680080b8850359a070b100c20700014002c2d0712103180180c0e00c101080304450b0307540e110341401c030300301501c5486030805c5500250a0b00c011540d03441044401e0302d000b40031468003000c100c444403191418a000f25200300c0e140c00c0458061030344c0c0d9090a540340c2d010016001b201091034112601c42c0003070708084024084d030035464285201501c5000c10303117150400590b070503142c0f44001090581070f201c2d07881c0c8403118050952074100c401c4861980102d070302840307103c0031858251030b0540c1c0d4984034a01440c409070364a807013205030b801121000c40002d90103003880c01151403412000d40ca44400300c00050041078240c0c01207034071510000350700c0e040100c1e9a005d50300b19100340d5620b4656544101c14805100c070441c00040c01d03d06201d900b4400241c0d05224080720740c415160646c104100c2d9562406d140d0300841e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 596713983 1250 596712733 596712749
    0x6060d180c0503010e06010303020a1514090c10020a05101109060c0102071b030b0f090106090f0902030114010b0f0a050f18040b1c1707081b010b0f0a05012601 70
    0x8070240101d080900403140c0c0051260000c0441d580346450013034445000100c000c00302181e00200544020664124007081092581858014101081032039910703914404003030300480c0702c2c048014426001003201a101c50300700c40503100320400d481e89003000700b450007101c00c983e103403c1c40340c0341098840401900d0f4554848000503602d0403d81010340c622209213148054101c110101400001e85400c0800d4100030004d51495490b10303107214030b50240c0301a410599507140f07000d2010100010307070b400c110003003402034008100f011120216109000000d000d1550001d904002c0d404c03108540100901e0300880500d001030504038100c2d41040705501411001107142c1500c04d075410945050303c00e88885400c106e645402c0b10035910412100030b48840c00103002c0071045850f01c40303041d0342242116101640154402d58650f800c05078505803d1014000c0403442d071a1040007107050401016108880000070000d8100500e8200111020001e40290300c9039420b005900d4508000c044007028083c000c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 596715233 1250 596713983 596714003
    0x307030f050706030522110a09050903070311010b1f0905060304030806091632030a0509060c0403020a23040515101805041503050f0d0f050c0606060d18 67
    0x2200c0024107440d00a400c0d80c807801110f01c11506c01c0407201922200b8140d12a407a650409500400541403100a5216004283c02c060800404100c044000c081c0244281c9845642140c1503281c14200c4141600031a013089401401c0003030308400d902d00072560b070050b00d0603d0200351140085021a00b060314114081a03801081c00020f2811407101da0b44084020351080310551110002007500d10b00d88100d42c2030b0100c10b60301c0185e040080c0c0103012441c240003079860303130303400d05080320030042108540c501410b00070304020480703004a003011601260340003841110b80ea414290038082c00368858048280da5240340489146079181c42c01014413030089403c100c6601c40104084c040380084420001e4204059906018501c4080c0c05030002a900e080d03138002045c44015040d0100c079070b000e0f080540356208000901c01d101b00d000491060405041c2c1d02c21949030600720060315903014206038004142c01860010b03d441c2058005813a0840c40c0c00c1001c5560808100e1503848581a60401d840c8102c00d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 596716483 1250 596715233 596715239
    0x50715030b0d020f04020c030702030604390b3103030806010f08011203050f12090114010b1206220203010801051f150228050c041b0309020307030f0507 67
    0x98480c0e0004010306444092a0810b10390024901c020080d10103842a80d0201e40043c2e07040c8200b003640c01070356001d81160124101402d202e082d4103154110604d06c0c1050b0080380540407000300e0341c3c000d18003107440543e42c003504042185160b07030812440341d812188480040502e074910301c50707140c071040c84a60411500c581142401003c000f0001d03d51410702504d05411428694070044045c111742c82c0000b0705180b1682854105c4151061501c2d085a802d40400c1500c080107600124071300a035080c0000f0420f40340c0c2e501d00a40001801d101d2080125814020000105101140700b0351005c40107050f00b040000c2c0c003520190b401c45000e0b100c40b595a011006201385d40003441020f410801445200b010300c0d6820728030100d049044e00400446807010b0305030800c224000c01c081c0001c54541d040140d684405170280b1440c154903d030041d64a8480c40d86401d0640c101031140c4080b001c3c03800c5210601042d0f1142c00c0d0003419a00004a8262085207000004624000b48103600b2500c100d015100c0649 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 596717733 1250 596716483 596716487
    0xa03030e01030f0605130f02040b120f0f010302061b07170307150e0a03050c16090e0d0305070801061412090102090a0f2702071b050102010e150f090307050715 70
    0x4603807020f034409140307400e0b02405a43d40b2090000e00c248240384021410055400d4000082e000380d51010114400210300720351000092643d103485031100e000d0050956903800f10b030809060003840080d400290402ca02540910015458011002d00e80100d6501c2543c58218001284d038481380d06400d500b002c10300d00b0402c25091840a090041100d040c42501121001944c1f20382d40d4a40040902000254800000d60103011186d40d00c420401800042a41c0d0506007018250090002c0c0d064007582041180341030103407040e1130060391142d442c840260300308002520500d820342d10203014410203004440d880c02403510180d21a014050000d40c4614802d024001007118a401030032101845d840300b0b0000081c030244520440300300362418990009080c40313200003441500c0c0e0140400f504420004441d0414562810840d403003a4000c100010001000c5602d5041c64020700340d102000320003180034010703900c24590b08802d00c602502d14042d02656140d140c1b100f41d0748030003903c034003405c08216103513 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 596718983 1250 596717733 596717741
    0xe210d1e020c060405010305041707031701060f120c02030c0102033c07050d092312070818030309060c010c20030a120605040e100b0a03030c0609020f0a03030e0103 72
    0x4820390000340100c0380c201c00020650f000c2d40c0582d504040d07503100010207111540841d07070343e0307030050140c0300d0303600c182906008110f0020300c00220000940e01c000000d150b849001040801081903982c100c441003035040303003005003800041c484110710080c850344521400c02e200031400340c881107091f44859841c072401008507070640d401d04441800c0310440b545a103242c1d000000c3d4000d4461514035038a040c03001000e0b00408083d40d0151400c44505011800c000012007408004000361085482004003003051a042d44141d1030014003220701403091040218456000141d066030040980307040c1034180c0041001504140042e210680d11510b001c03240f9900212010f0f080030854080c0b01c100340300750012581e40c0c8035807144d003401c2150009501c070007071526034000030141000400c18010309030001c644603a01c1816400481d08c5a20f0b025040d02c030740c9480c2c80c981d81100c1d0301d602c40711001105612402c00038900700c101640c02403016000d811603135a074443c0703607000f85100c1d0b02c1e038044c19000f0f0b000041c211 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 596720233 1250 596718983 596719037
    0x5130801060605073002100f05091b0d0f0803190207080403140708120a1103070201080105130b04141801051b0a0203130b03190c0e210d 60
    0x1030340340a00600100380c0c054110350a06400048400c032850825101940550700400e00d0071903104031394241846030764080f440f50303400741c4c1031502072240203500d4a0b03200071030304145d840c0c40c0b40390b004a007000c3c0c101c90307045a003a0204a00508081200c00940c88518504101000032105600000204207401141407092803107822903e50031030a100c0c460303640306124400c81c0000351104004180c1e1106000003004480b001c3d003040c2d020b90b40c204072015002c0d6200d411030707100399000c10b5000c91624003d52002041c3c59409070140c0d600748042c1d02c0d04d4140000142203960420565840b2050025aa11940140b109000162034010312501c2e00707514030550300c1403d01c02103d4590600040c01000c140280900e8807041c540400d0640d28403007100c05904c1c41c0300c0e0f00d920002d44c424210300051034003c80405544100990703031183c8540000070010303000311015840c20750702040c410a41c0004508180c1122244419044d90a03104011446001440d20301140e03811000501007940110b0060706d0941c0705889 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 596721483 1250 596720233 596720249
    0xc031209011115060402090621070905090f0f09030409020a0807260f1504060e15060a020d03020d060306020d1d1504020d0f0221070e190903020705040204060513 71
    0x4444400070080c0c0315020b0180c4d0700c01c980200b5132132801d90715482110710203a15502c40066190182d403500b845294110380f1100400e008401c00102d9090005103a84124508002c0c0c01a80c0e40360050180c40680c060070303110030740c0301c140000320310950148006c064a29041d01c82903594940f0300c1c3c0003001c07524082c0c04081c00000880034410b55089282c1000e40020620b2200c84559451034111800340c0c0150813031b00d034424108140051410130404820340103082c111600005400e5450611107644200b103035001c0140e0200c40564141032196015002c0010400004110300c0c0c0e40b0388a4200340d8010040c41312115560708995508448050000003060171150058a031042d1098499171039a140108041c1c0140b60365241d504c20404105030503100603034010001a006041040303038010644001001421603c150ba0300403c03612003d00300b242c801c50400c03070b00065810362111030b540a040384102c1102507102e000008a01943c0b0380c006440a0801942c44a456101038010440c0d80c0f00583c3c06103c1c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 596722733 1250 596721483 596721493
    0x40f0612060e070b180114090a0b0304053f040f0e1005010201060609052202160b090c090127050a0218090f040f08070b0703020a17010609170c0312090111 68
    0x1700002d0010080349001003420042420f004408038021a8400c8084882c0c0c020101400460a000131201660049003e082100e160900140d00041d03000700c82c0100c004c00000c111940400f40031105001c4140e6100401c2c02400d2559134900022002e960b6000000ca1132942c00c00c2004001c1c103c000c200051800b44003d012141c9400d1000c0c0c0401201e005407402000500b0341803908818203404046d00907003c440031542c420a15204002443c90140c08640740110000401c500510000d00c9152040b80207204440d01d0746045004441f030b4070702000d0200c8041c2400c1604030020102e00c41d407445040c0e215000350b0382c0c40d50180ca0491f42800581047d06c92022542444403e5400120705942b00d0f07444800c00411003103d040040c038902441070300802482070141041001517041d006800340303103e10740354031080031081c555400016100b4003481d00040d411100411542406611690106c80200256542400c2c082d0219041419403c28201d07d54000100780e402c41d64000004144010000054030b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 596723983 1250 596722733 596722747
    0x3050f0609040803010b0f1b160906050306010902030a0e070303030b0114070507050906030307050313031e02010210020307092105070828080904090606170a0f02040f0612060e070b 79
    0x6002808180102006106c02091443c600d000b604211444000207614035800307c080c0040090780c90001140724424a20340010000b40003190f8020b1109841008019103505c0e0b0070303e04158025000180351403c800d803640d003d02c0e0900400d02c00c03000518003e540104e020f4141d00c0000d48010030030001260510300c100240e4011481c0440d2171000c0d104d088406500c1d9454010010b882c44c002c40e54007030030358000010b01c207560004001d055400c49108041c01040b94144402c40103440491007130282c0917811100701c030510054140d00031a0b2204243c104125105c0e02c903211a90385440300180c01c101803110b00100400d2210030090b85000b841e526004041e0b04c0001c940d5420b11100f010035201c0d2894201104904001103103050b1020060007a2003007100c18000d062403005081c40784250b402e01c81c0e81405250450f8400305144184c0c3e60800c580d200b40e0f200c01d90070700c00204008090780c400c055441d01c0c08540004c1100454120038043c04021034642c42d260115800c2004607800941c400d0301c200001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 596725233 1250 596723983 596723993
    0x5041d060901120528120203090306071b0b180106180e0708070b0a090308122a070206090a050303210609060904030309031107080f010f0515120a021003050f060904 72
    0x440c0b10103291000c044d11880f20100706040d0161700100c000c01e442a0100300c040c8840e400400b40c0a842c00441c01c8500e01d445d4944c0c25584020621104180100107044450200381c4a8000310f40141c000f500800b11641e4401c07840d800c48080d501311032a0302c01101400d2240c03001d5030003090000c54243d005004006e240c6120b1544d94001c0b40300302604446c011400f01074190241074040e00440e080045150742e460540411044140c04603000400d03d031519030948000c1c1c6041e6420122301c101d8401562414503580c0030400d03c2d03003041480d00d80c4075051600104150700c081c0044d142502064070900032032400e02e407408060060061900d40106155070402c00e00356180200690416010b042c0003400701c0c400c5c1821501c0341e1100d14500c10310300c520714000030700b030304001410750303030b020300b03e402040007000d0302a80d8000c1d1003054179403440344400c8087e038403014517080302d9110f9840810421128900c0c195808a81c1c03c0d8400962103010179070314010050829a90150198840ca0884020496141039a20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 596726483 1250 596725233 596725243
    0x305010b090f31052203050414030a02030109050109020909010b010c03030f14010f150302040b04062007030804030b091c120e0a050307121e0c0305041d0609011205 72
    0x520941d8000c07040c240f100700410468400390044140c9080007040e404100c80980000d6480405821011440d91040c28580b80000c0290340d241d920149001e141c40490401e08481100c03a5505019125410b40169000d210346003840380314800109012540340104400824020700074080b81c0d040c40b041860701c0c0c1c0d01030a110702c0d55505003800600c102280b104080100031048407580e51800070000441c292601120340f40448541c00b203003c40301c8116001c00c070164055403050606040086c001802250b00480b8129417040c1e80c1a0912040f50400400e0f40c0752900c0c030f03402500c0c4850006010700501021015180c1d014032900020f010300c001c0c50722084490080000704100f0400d0711200740022107002d801813001030914500304c4001c4030fa9424030b03130b490740e200f000304880d114407072030034070070700d00c3c082c02112100400c05000c0c0000fa0342e11003810354103d401b03507a0490821000700030208106100488525064000011200c100e241c0b04050241c6088181c00c00400103101540050000d100069 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 596727733 1250 596726483 596726509
    0x604060507060906020705150603010f0e07030f020d201801060c140f0d0e040b0904030207060f020c040203070e0307140607110f090702061e07080c16061b0305010b09 73
    0x605083c0d2400e000001313009100c401440ca010302038a882c40500b100d5420303401028220020003451141c000310b1021541a03030030550700d0b50070280d01040400c111005510b4031600151080101c0352b850b07510014000c10b5400781c0030b9111801454000c0d00d040c80001c1c100410303040c502d4010203504211004c1c20400207181d00406d003518011402140c403000b070100c10031241d90001141e01041440da07015020300258424076000758500100000300b0301e8071007180fa026030b416801401c403690030200b044408120b00c03640074042d40b00e140903041894680307100031032107400e03a95a6040071031198010142040c0355940000030303812041001d100242d88041c11a648554080040600f0356481404a021460740c180700952003003400d02002040d9402160a45c030480460014402d1154107008000008405407080c000040100c0c1c000707000c200e28100140750b074414040a500341e40e40b081d546ca905640542412035260341440c1060065941c0601603203001d000348007407a0381014035010100f900c2c940401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 596728983 1250 596727733 596727743
    0xf1104140f1b0301081513030c0228060e01021605010203040b090d0204020f031e0c0d09140706200619020915070b01050f060a08041202100e100b0604060507 69
    0x8242e80752112054603000000920b20a41c0b02e40e5514096615014a607402106440700d0000041c89801d0f2489030581e0103601d0340351000703980010303004d1055401802030115601a03208880050102100b400c0200910301a030790140406c0d800000241000c580102648450386511020302541e0f80200c00e40d03080d00d9810898075200c0a4100c0000c0c441d64642d00060341180c0300240c3d2044c4002c0c11002035124400c441d000c408850300c03540b00d406440704111400388a0b0750042c000d18160741c1664109040950140c10005034268801c4800b078113003002c660004011850701c6841d400008140115805500c3c04000500038a16000700040001c907881450207143c9135000a54043c540d8600a071119050605600303191205150310b070030103c2080a008580c8501c02c416660301007807400d1000c44000c6481ca80d079410060707e546c0d0b00c0b81c0001e60000d4000c015402203659000072180d06202d6008205001c40003003081c154501d50010032131312510075841c041d45007040103012054010b412565000d40c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 596730233 1250 596728983 596729011
    0x1050307020a1707140304030f030c110402180102010b0409050616301b200c191406070203070b0d1104060f08180a031b020d0f110414 59
    0x490201e041000112004005100103c0181c00203414100a803c455104220020161544495555581c011880000c092030106c90041c3c000078031920350004142d00c01d111110101b8050340c005000e03a008004030410720407080e054801c0c19a424003500740301740000e403001c00001081e40c84041c0c0b240001400c061040c034074500074034101c41c412075202c410400c4074904180040b2110340030150718010140c0300c001d500d0509881d03070291115810040d540201d071b51210303001c14020b690115450340500040007824010b01e5080300607601c410f103160100200d1030f1161103a00d03050240220305050b540c05124060ba50a100c03980c01a140020304600341d40c6034061803070b1a062081c4d64200a48000780344407114500200300061b1454110100c14074040f225110180c0320f9031503d080c000100c9150402d04407950014040b00082401400c0400c0b2801c104158000f00354010f40100390480f014142c111482c00704a507a41c8144401404800c10050301110144017240d40d4181034885150042d00c1d0340610165 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 596731483 1250 596730233 596730241
    0xf0d1119182402010e0106061b1401020d020706051e0c0c2b1d0a0603090c03082d0c03030402010e13050109061503060315050403050d05150f031902010503 68
    0x3491251000900060810610092003410b8031046a4010000d0300059801c2101c0b2124062042c007401701580c00507901e80c031a842c80744102c0c03103001c0c40280d001d80f0192920b09100b10040317070038002040c0c1402583c0002d6130b1861103150043c1181d00052840340c2010030003038510700b109414800d550b041401c03481031940b01d40f000b203500c0c1c1c10103031281c1c85a060f00c60110146044041d600c2c4c000300c810312482e200c50f0040e440c8403e10300b2044401201c001d82c0600000d00600215000e5070000801900500741c60160944079034406981d40c1c00041d01e403241c10b040c48021240030003400c0c06800303000b003400c81860420104d01402d955074000504001d0500159242a080c540c0311226402031b281c0030218240110350752403c15200601c00c9004100441d14460b180c0f0400c14081c1c0100022a071748403031075014605a0405510051101078811000c11108010140000040e40280c50140c8442c0060180c0c2501000411898141000407d4000d802030001030308824260090403486507020b0030182da0301d6803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 596732733 1250 596731483 596731517
    0x32030a02041e05151c0c15030f0908220f03020f120102181f0206150a170c1003050603030d09060f0c110c0411160201050f0f0d1119 58
    0xc0080e0882c50000d00e80ba04014103042d000e036515211520640e07041d200c9181d15003010325414030991014000a40c1c5410800044840317100100c5891014940095594880d50303d6200751250008155069000400c4c20a450403800d6800119200740229001d90a80303040c0600003405494400070b44036403080e0041206130b449007901720551142d100000c66813409040f04030410285441c01c000c2c0a29000ea0300b0801d0201c4108044d111030031030b9002005950380313480ca11034800012070490742c1c00018580000500d00c0415405d403456403601000f8011170810306c800c0c082d5040c0303545504000c06007084240665920044200c4041c44800140031a00e1500c1e401c011001d49080030880164914084801d42c11a51200111501034414403c3d0b03002c1c1d000b41010003042d1500c0081c1001c210008202855505440c81d04403d00d030342c41810300c03a0400c00c1e100030b9000141c00c416011f6494041c00a82310010500500c980a07103020030404060400c8140090040d8000c009442601402034107112120408 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 596733983 1250 596732733 596732771
    0x9031a06010f0528031b09050f040b0d02120304090b03010c050a1206170c0429011805033a0203090f06070c060c020319120f0c06050132030a0204 64
    0x3100c020b030007003411003840d007004006189602e500008182132030325420311b031031041b04100d00701c0f03000910b00c100f00d12840c0204401460180d2419902502400c003890040e22140b00245482e031180c80559115440d01e41c0d024250780340c10700e04920a03498203d1920b01c507a000b8040ea5024411498429020305000042000030b1100350000c02d4401308400244001110020b05030315104002d4905000c19420100214400e86040710990107a885514044410b9407095503049041d00703041c000766614541d102e0210b0705047c07240012100c12a8002d50090310b00548040d052030444101c1d0004031640603551009440740141003d4910441c0d0f42c0c8070000e45982c8160035501000c1e046030811890350758a000140925006403000c90282c0100d2058090640c1990704007130f0101e402c000003100d40002110700325201048281c10384140700c2c00c1e14848003c19041d01c500e50280104020000d03034800c40c801c590044101800e00241e208013010b40040c000e840115124065540c1030301c02142980302600da4041e40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 596735233 1250 596733983 596734027
    0x2030f0a051b1614060d230906040c080a0f03030b0d140c040501061e0305041401020705010e10020a140304020303210a110306011b030504090c09031a06010f05 70
    0x4111104900084240b011038401e19840c00c035071082510564629104501c112a90001d40c0c2c08030040c4025a00c00034190071003c592031400c03c25603501c4540e064400c2000701d040c4c0b011603980d4046000c010400c640354040c18041e1000800501850020369117940361802107490080030113450303181c0b0200725203a1503010502c041c2d2011011340c085040050055030b401d01901d0b4148070302e09007000003495034020f0850820390400c00705080301c01c0014cd03205501402c0054400c4948425428000405185c2031018040c554410030000c2800c25142400d1481c0150f5500ca000d50a4030410503900c029810104030420301ca074041d1540e40342c0d9981d00020307040d070040c031380080035208650022940030f011810000b0300c5816800d500f004101e00400030304500c0c1c003007110202d020403034411004290f41645452040c0d220710030714190345016201c5442c00c0c16141c0c9610741401081c80c40c04144100842ca600c8036481030032010140740300b0b25100740020912208054048144240013807803d200c03050140307145441c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 596736483 1250 596735233 596735257
    0x606090f010f181d061215060607020a080c0f100909090f0204050f0f01091401031e05030f0901020615010804080a0903121d0a03020f061804060303080403020d0f02030f0a05 76
    0x7003a9554846610042040d002151300a08500c00036080f45002d4524040919514000f0040e045001da0070020303105014205940c000824440c141c0181e4425030300b14080c1c0281009807000440003020b0050f00524a24070621904500601c000351940c0038800b882110030b5100c0c0400e50400500701200e0401c02450b019401c64200410404580e211a40190044140326402c40c020380e41c3d140410122801c0307440e0282c00e80c41c40390040000ca000c000180001c0017001034200c50354081656031a241da0b200034182c188070300d00860302e500303650380612030350740e10a0441242c0707940d00c940c0b040000c0c180040100020554100411404105031082c10200003941d80700420b0706070a9803900d00900544c5501c4102d1030408825003001d0030721f0070310305446402ca9501510071000c3d40d01c46420804507401000d22485039100b0507800b0100740c0d4640c00340c03400031030003500c60715410f04081c01c0007810040c4c004112010b00441d130f1044100309900200321581c00c4900b001c440d40fa1101200304590b184142440412 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 596737733 1250 596736483 596736527
    0x1b0f050a1a13080f1b1c0219020a0302010f0c1e1e032c060d051f0803030609072c100216090b0303070804060909050606090f010f 57
    0x10071a00c0d40c4215900c2160218041456980c04079080706500b412100405801003130001d95980302001d4003501a019007104010055403190801d1494021a4071101604514160305a180b2a80500641059080402500619541540200714204810301c002410810401e0050703402c58440d0325107854090703000303418007000102c100c102050807000b24400e031031602c0602949900e2600300010b89000ea035054640520600228902c1c903d40102070078402ca519128880b000b40700d80e03601e40105813400e0481c0b400170b141d003416855056500c1c0030014a0030803400300401800740c80b000005a942c0002c00302d507010080c0d0303903200040f9601100c6086030540300d443c1911060194804c01c13460981204151a01d071911400c0c01822a5180d080344146444064007080501c02d04403560401c00c011000541224940038a5584a01266005030711020016001e4036050005039400d0203003a0b00706a0485505d41810400750026008907980d20005040c040066581182c15001e15030110080ca00e00c100c0300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 596738983 1250 596737733 596737753
    0x5250e010b0a03051e04030806130e03040f060c03051602040f050c030906250e0a03140604030e0a140105090301150909020f18010e1e010f0501120504031b0f05 70
    0x50810380012600074003203802c0100140180c99600c5d0901c050b199859402ca00a45a90700e06807608580a45516040400303945e0f1308604c0081406031840000341d5100a5940d80e141c2a0382c4c0d441041c1d40c1d0002e40821a40d03074010004607912205580d112109100700d25080c85140c40010002c2c1200e51034906650b04050030488803841050165200f1554142038801c02c0d40c5100030444021649603010f601681c600f01c840410522803c89031000700009404080c0c3e46413203840b02d0342904c02009103c0c1595020b03070104010907a00090100203883c0542e04901072a0401e24041d5440e1810a20503040002c081003520782940c09400444504403221a00c070f000544511500019003541c1c0003d07409000781c10082c64081c180206c1b00034400340728001c0007450b0390a0101450304070402420a0120f2a03a0807020545040c250388081c0c000c041c040e805940c85071801c0c00140404030701c1820360380c0d0b0914000410010035000805860561140c08600e914000d06181140960f40e50a0300a4454810481e0309 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 596740233 1250 596738983 596738999
    0x9060b07050d090b181201020706051915090506190305070914090304030b060a031205031603050601020d0e031204030b250212160209040c03170705250e01 68
    0x42400354011030584070300c500100740c10b4030603a03514440c1e2000c01900b0080010801c021103800708102400600b0105c0c00b0b42082c0315203081e0303040724905585255980301808846080e03510021140c02d0206000d002105400c007025145003880c1c801c4001d01c0da2568001506a035602c03e07600d000c2c0c0520202a00700c0c80e01c07401c00c581e655409000d000d034000d2402000c455007002d20000b00e4820604203004500e020b0560752104002c50000e48059004941001c000c000511200c0c01d0840d00180b5541d916120700d13014800d03440612075900c000b001e262800d4140416640d01041e00c01408105042c00fa26459002010030301d00075079403403c00200000410040204441404c1c9136000c2d1040d00259400315440b4600084004c00740e80816015034070101d01d6031201041c15000d460040340b214210302c031011607500801e841c02d030100c50071541c014000c80280200200b00380c100300010188580b40c0d081102c03d40e1941c1c0e03078148003501840c035004a070b50030f00316003000c90740000c014140b042d9814801e56951101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 596741483 1250 596740233 596740237
    0xc141810020a203c0a080d0807050409020f0702030c0315070c06090c06080f090c0f04020d110a020a03021005040305040302060a020a02210c1507150609060b 69
    0x86118640304040358010354030014001414603003000060598140d14a0140c49003501420081d4109028800029481c40403412a00360b02800388240c40765292200c00085812003d0a00184075284400080c40301400008501441c3c07412814515046c0c1ca0b490001c0d26203014950180d038403540005024414100d84c030b005416118400d60441e40202d854804041c0c441082e221078803666000d541c0001c40491054000b00301290244000107503c21494880c6543d00206e60003013000303d410001800361014481d55850303030140c60301000c2e1419101203c0021200c07801510070740c1c4507a402185294500303901d98400103040e8020700d01c00307554a0396042c000e511012024000d074094010501c041200c0c6400d03000c0c59100301e40c960b842518050540d070070890690040c0400380118403410030703604010f032106841280c515807030114402c2c00b001d41925103403070000f4811105020306040c40098101d04030310010380f0151a4810350070310341c81d110322610000a04103a40010760706405c1c6000020707401e0080340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 596742733 1250 596741483 596741527
    0xe060307030617070b120c0c0712110a0b0307050c0709061d010b0a0c030507030c05011401230d030309052e0605010503042001050d0e160e0709090c14 66
    0x4140c0c10450003c10951581228400d44010710010070a0000714640d0aa420764003400825000e030a1401c0e1038181442e00a4541200403284824a441c02c10300c0b01103c4504107003039007203c4000f221410982d601c40340d400081c0c80e51051010120b1400445030b4140f0014001c0c21011200700252036894541e100000b200381100d0013628561000481c680b042401162201203190b1211a02d40e0314075501211035520006040d4204030490303030750790001102030007070003402034403207040d0b0310303154100169076150b04064001702403005482c0010314107685443c40050800b5426040000704802941400d5040c03880e02107240701400700613800c5048402003028403180c0309210490070003465869000540d80791009a030050445030342c01100000301e034030540e40c050a200042c984981001c0881c031814041e17500300c56000fa0181c000002c00c841d00c2e00c4480c6241c0c000c280c02d46030782c0520305200b1005084685113000766942c5980b00c0008410860050f030f5012484000c3c0302c041035403094150000080317980909 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 596743983 1250 596742733 596742749
    0x16060c0c0609050a021009030308010e06310c02030a0c02040f020f0c030c0706080601022109030a2103060e040b09070e04080901023d0e03040605030a0f0207080d05070e0603070306 79
    0x6c255414000d100b81c000100b62a490f484400c80e59081131070304c62100382c0c01404254005000c80d891008040001d13942888403640f80314083c1c00300426240c3c1b40682d460210040115403081c03200200055012121404c455016280003c0100d440c01c8140d02174820300c102012140000101428601030002c01040180100300554491548400e0100e510f00010b40d64580140d02021000348bd1010b101a4040340d415480401884c0c00124804070b810710880c20b000b0307521b1110300514480000b9403900c802c0c901485600d4100011400d280000c5604c0e480500054690340f08140007460b604d0382080010050008054241528600351400c407515030f02982095006001c0c890400c1c0d039030642050780302040d400442d000e13142a41603120302550002416100406291540c0c022468008188000e0000e1f010f075540c0c0c9942d0b8540041c0280030343c2d072940c0c4500c211600c100103d602146102091340c880181c0700f1000302c0c80c4c0d11384d040120340c452803252a00384c0c00f5000000344501903805174801c0044642c08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 596745233 1250 596743983 596743999
    0x706060e060d030528090302010206010e0f012303071403010b0d0201050a35180303040c0501050d0914010c1d06030a09150e06011a16060c0c0609050a02 67
    0x5080d05421000040d9406074000e61031048450000340540f016003801e040040d1400c1c500760500f80070000c403200c40d5040c407004c201c0b110400d00565a051003082c1c05090254800201c5060010461540120500c10b03904040340f81c048000300585111010000b81c280102219040780c1c680f03002d010360030054410240300750320780311500700c00d4100485030102d803a405854040c20310b01c1010040c3c1c0c4000030f6144d03400d011400c030390f040080c0b46092841490008404203141c0c0082c84d12428607824400381c070040c03000703d510600400c00001c1e410952030041e91028a495916150345900e1000604002c80005005044440b094054000305510040e8400300c16a92012031382c8504800c3b40300c042c08040206e800543c10000501c0c040c03141e40006909500c506070385020780b615088010120380c0424044e0720036401140040110b85803a0981e08002c88a4000742d034a003c814480c8402c030320685040c02404145c5440744442d50a004075450404190401000d214402e01d5151040d12072000d08000c0b4843e0041e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 596746483 1250 596745233 596745239
    0x31112010f02250224040e2d10050607110907020c030c01091a030c1605010209091602030304141c02070306060b030903030403080405011e050403080702030f090d1703010b070606 78
    0x4400480041c080e00600741c40c0748640403180c4003426200c00e9505c191800401c000002c1d420341c0c60304800c1d1068907500b180300b00700d0a00c1c0d12048140c044208050842403800000c0c0000301301040c5142041f69400c43c3c0d440d91380c210f540f078404210301c0182400c517401220841040880e54020900c0744c40c00d5401c0342992045e0081c1001074030150300078011608484400e51a812120308400b0045800120044172035050603041245a07940c424081011246a500401c0c0d41d0000c0c2003050000390050352656080781d02100c944c50003944c13400020405401c1190360503400c018140d0a2044181010b016030402189580468010b55030fa106031208407480d51800706d000800505000541b030140400c5400b8614540300c640b0222100d0202600c165520b541e036190300d20300c130001c0787c41c0c0071201d1034840d40202e0249824240072300044002440700301076410810540b00003042100488180400890340c4008171420380c02c00d142040214168802c0d0b0803000400401c0c0284000040c0c214584602824000307151 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 596747733 1250 596746483 596746537
    0x50c10150918020a06120c0c0f080310050a060903030905060408030a050f130f0303020f1c0f020c0d030e0a0b0702030705100c0f0605011518031112010f02 68
    0x1010150000030003003040d80034814001d158000c80c040455844400e0050b0030540c00107640d800c0e6035445000403c031031100c05a00240715000381000c0b0703209401e102c2091100c9032240080c8a210180c001e00c00500000012450890450210003074480034104260480d00e420018000c01d06c1800300b0b8000c5070151200240ea490001d04880c02c0e43e10681c069404d1902002c41919103420503c121500e801d001d000303008010203c00441c5004000e60380285140d80c0c80c40c00c0c040e00340107500c14881d40640104026900d040b1109410322a104854609040b4010780701408a042c03220044135154008000e4044509041d80020449069901100c450705000c0c0c0d10720000c02c807481500c40003901741d0001c04007000300e40350031904c481c2c101142d400d180c0360304015a40c51000b207960070201181c1003907a450062100b0600119000d00380402410712070340801820034140d40ca85100d00c0000e03c0c0c85001c111710b8a4503241c101c400101c0c040c481e8000d0160310002c05000c1c001c0d401c2038080c921021f03584508188418 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 596748983 1250 596747733 596747741
    0x100908130503160e07050d02300618060402070b0405010b1f0c080a030e0109030c062d0c170a050403020c09010608071124010f0e0106120228050c10 65
    0x12040c0001030460311302c2c00410741e00381d0000805540a10009005603407029846000400a1020400c02a031060300200f01741201e50403d540c110078100a503000304403203515650460700001c10f1f0410314a2207a500c410014002e44580080189954007450900081000541040c60600801c4072407150030b0107015101c00c1c1c0149500801c900103040b445401010410780001000c00075150302d400305002c0540c031030050968064080850004141113404028049540b050100c03c081001014501c2c0c5010200300d50038680c0d00514022103580c9144003240c050103080f48110070f203a140b6407015a40340610440000300411203060f00540148a946691032810452183c1030308c0301615807100b99101d05004803000403209840e1305251043c0320000e51504401c01e086108546010072454440d810007160018152003940001ca07031401c098014845141c101c15240359080302020016224001d280c0040326002180c4100904a41001c0350507290076480760050032050303030340f204450300c40b02c3c0d55407081c00300c2e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 596750233 1250 596748983 596749003
    0xc03020306130c0f0c0c0b07051501050108070e040218090108070305010f09211808070603060b07030c0323070606031217150a0f0806010303170103020906010e03100908130503 77
    0x84ea03101d0364465503601a20f1101c503814064403a50901030f49a02c02c8061943c400e2030291850ba0140541c2610396078902103c501409003844c0403d10760409100180207114205001880750788c020072000e10302d0019180040101d04020715806495035681d04103030307e41c0300c0ba01095669500708005032003000028000c203210541d01000000001c5081841e90000124500180d4100710448451440e1070b140c4102890280c4880406800c00714580440941182d040c0d6100c0b0002800500044010030f40151a914a0355090f0418441e48030a10154001c054419098031b454003402007103000500c02d01c0e41c03045096a2082c0300d0351055400c5424262445c4060138900c10503240c120001990902da0400300c0703102e0b0b100c054039460805441c2c030344108840010b0342080086900040041081c15440180400000303038040b0281c1d0254119004034a003001c009140c0b0341400704502900b4600d4404001d081004c040303d1100b08240041c070324041c001940045410030110b171a0400100d01c910b004641d40440b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 596751483 1250 596750233 596750237
    0x6090c090f0601110a060e210a0e031c03020405130216140102121303020d0c050304140d0501020d06062a0b06010e0904050c031006230402040503010c03020306130c 72
    0x19075036030040321011407000102140d04102104e0501c070b910010402500d103850f031003440041401d0903003600c420700c0c1c6056020364400da400301044c50035122130307407008075882c0440c80e1521281c00380006011038a01050702c00c03000c44d41070b40080c1c2480307440d525034043e100b958005c03501c1000820031a034207401a80138a914080b402c020070803c540001d01010700d0115100c180000242c24100071004818940300104c4030240800e4000128104250f4180305006000c41a410441217609941c1c44e403594a004030b001f0301040809040c07140845503681105211110341c800025965036400300c1c0e44001802c51441040041062071541540340030400c1c06c1c0a02e000200710402903141d0303140e240c0130003564020300b2050501488101007a102c0c3c8800715442d21450159005020441d107503070a0501e042d1120b000caa039514986002403203400d4000d171a00e181c00d100820341c1c0d0005200703c0000380003446194070013541076280c818021903403501500070b944121030440e05000080048042c600c1511000103070080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 596752733 1250 596751483 596751499
    0xc0406050909090705270a0e0303011a040312020d0e0312160602041203020715020606010c0f062a12050603070b0717070f020f0a060207090207060f1b0206090c 70
    0x503503410404100ca90083c07100c8122111641c3d66000308514040b0903201e004c810404003603032071250000c0c49490b500444ca8079010050300b4081d030600c2c1c0e207a00040c040d1469a0071052008075442c0031031001d4078041c1d600003010203115101d00c40080d54582c070004124000c01d4502961030750707500d0003152003032800a01528452030f00022954117a51360390307030710011280180e080c4070200301c80071044214540107109070014900e0301d0401c01c400601244d038144c80c201f1940100104209668004030b6101540c0c3c2c410002042c0000358901400540109004c0c413802000f916440204241c0841d0000c2c9010250f4542c00c7c4001a194980e100391907080314060b40551002008100081d084401403080c02d004030019207565049000c24246a840070702c2c180c03420561860400258074000d000d100250700121410310b855850000069152910b502c01d090300b480e808035540c2d0500c00e8540115800079040f1008004102e2610071081c0710440425044d00123124500009102c103c001944040074003006011038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 596753983 1250 596752733 596752747
    0x121e010806071818020a0909051e180607021e071a0a090b0a0503010f05040e06071b021503011706010b0702060901050702090a09110a032a0b0a08040b0c040605 70
    0x145269059410b020011803007290000340b0200d502c011494140765150313003d42d80311000200101804440d801603042c1502d80002c0c042c0c0c1011200340454800030090580c0349541d65070440d54181035881c1100b182c00d00540701000321150b40070480c1a40700991028048000c131588a0075130b0350b07440e6030048140c00c29000130b1103005c200441015002040013807030030112190712640640034542000c05c108020030b07004801489100340d82c0c00c6000c094a03094030108801c000500c00ae03680c80d00c02811213414020b0903001038003600c0300c11b80d803038141d1500034003401000b4548403048030f44c9510910074000c0c10300095072558084600420342d54100c0700e2401c4250304001c2d01d5002c01c031499125096050502400704424801030300c8140a07a446101e80c61800508081c141c00c1a2003100c0b1034402481c450f184651040c0f0000d940761807881c443d0399120b4040d0321040300602410020380c2e602d400c0341d61851800300f40c4202c4181d201d00940d1050748201c0d9914a43e0311200ea10111f940940e018403070200302c05100306 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 596755233 1250 596753983 596753987
    0x405010b1312082b06120b060d0641070206070e0d170915040b07080702030304031a09011803050405010807210c0801050a03080f0d060b121e01080607 66
    0x42c0e141580211030641c90245000c9850300149078030f1142c0c2680200a4202041c00022441480000e0691300b01902c001c103280d541c0d108140b0310003006c00d8880e00c220072800e01801020b510130341411240c0b8007c07103081c9a01841c0c4105071030b05650f0b984c0000d42840040d0000245031902c141c054581c6070000d203400d80b2610002d44140c44403180700c540042c840e0542c000440e5081039151214640114801d54541101090020307500c0ea406540f101a1010042080b56507a01c1c001c8844003508030b0900c03034858150340700090a5106d0703540050641500c01018040b4008a441600d0164030380000801942e40316900406581c0801e850190203e042072004210319400340040030350205540c83c10380103081940d542c0014240000042107102ca955075240a00c06400c00402170243c0001c030746900e49613141d03568160180c4201c0c0c040ba04080d0000c9170075181d0a40c25002003003d0f104119190380c40c0c4500c407696000f241c500315010001d400c61010092500030708103070100d060341c01002c0988181d40d00c180342 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 596756483 1250 596755233 596755259
    0x4180b0a051516080301090501080607080f06040b030f0a0803060a0e10050405130506102c01030609050f1b040605012d0e0a230303310b0d0b0405010b13 67
    0xf803a011418400b0000685100c004502034a10104001aa54100800d4914220004240c602400610814400026081e100643e84518202c0c4c000c41c0f0440d81c0004281414403010107031089200307500c400c0c420402c03003002840c403030780c0240e4007041070781d60364411b41c51f07080744c2950f40030105421880c051085d401c10350421a4003d2801d0792652030150190f442c5840d001c4100c501005408050300b0a01c440741003d4010140003080e0100c03d01005802d0042841592041c070005010070741d9015582e00b080701c240003240c4004641001e603403840003910900000345c3d8100d00203621561074440045025809810503209400c4c1085404802c100841c0e410a03652050104520511512124441d0141d0340d004240307014140c0310f08404000019030381244461070103540307018804e41047c012060f1401c0701c4a1080150345d80000c180480060b1035105003560035207500001804903002825030460181500074030165541950308114580ea05c543d050018050944035011200f40c110003003106042c101c803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 596757733 1250 596756483 596756497
    0x1e0c04171c0c020d140703020405103503030108010209010201140f0414120c0c13060e0a0f0209040e0a0201090b0a1704051e0604122d110304180b0a0515 67
    0x244001403140394036403840c4403035003c440d09606c0c0d211000600c01c6042034051031390012045980ca451543c2000603081d07014030b82da600c840305e0a050a024101091016410313481980b007040940782d881d6140e000842c007030751205800502560070241d005144050f40c202e15407003a03401070026603441d02c607580c5402c2c3c904402d1480900500c50074074109241c0b0b440b41e0081c1140d4150700010080d2040e900c050012041d100d00901398a00e03c0d02804004a07440710b0722840d07014400700700024114003480185402401032144041d0010714200384051a0040000c2c5510703114002d0700c030303080040d81c0d940e030140741e80c4980c10784200001c0d50000f40243e218103009000740c20510520980381406d4440c4281c0d81b4a200c000d00c152060352010051009111071480301d01d201d00128944011000c41d03216a42041c44c7d140007071480c880c201103524251023403282056a031410310f07031713015640e456544120011803480c5080060b130b0302c6860804c50710704524085100703e086a44c0a002c00d03940800650524503a078208031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 596758983 1250 596757733 596757739
    0x1d0613050f0307080609011401140f010507030513120203010e010506010e311b0f0206270a0b0a0b030601050d03050f0409110a0905030f10051e0c04171c0c02 69
    0x42408a0704a109020341c80c8200311031b0b000001c00300300c1d4a003030b080d12500c1a17015104080e2040400e4055031121050101214003c2c07c21555603da0307440c1c03c071410710038100d0105040841d0030b404243d40d814964a200118000c070001e02640312080d00d1f560807140c0139100c0a000c59041c102c14021800d01c80c840c4090b83d0404c041c050b668048845002c80120700c04205180d40f140d0310318060b000c0c00450340b00030075840c419150003140401000700280d07650f200604898296041f0080880d82182126210382030160484c0030b42d2401b100510345900b40c11010380f4400961030500f40032940d1818002501070407550300a007000590419510141c500d58011140011418801c103c08109180d04e0b009408042c074810a01c0da0b0f41c0d083c0401c00600c0d0503074a03000a846030b001480030224000c1c1c000381591032100c0d101c4001a0b130340c0f240d00b4030100140c1c160503022440002c160400c0802c0b01780d10090000c0320b0442d2886810b035001d40e21394a440704110440c4500703403c044107101c001c0e179100740c0041441e40c0c0b0103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 596760233 1250 596758983 596758993
    0x6070807031d01020405150a3216150c0c0605070318050a06050109110714070510020309040b030616080c210405010609020f070618080a1d0613050f03 66
    0x14600942c2588001d10700c51078141e40001c1c08000e00e0400d9880c000c00320260304442d6007011582c0f038004048074001101c40780c60030f0f20101e181855a502c0c4554888004400a41a9442c01072040c20b24001d2074809043d0380510b00035960b1090800c050007071414014583d07a901d900842546e645900901c400781c1810201503075841e0700b143c141c440d0300010303280a0041004009940082c40e011080c0d0300141c11440071241010b14216040c04004140d4055030f900c11a000d00451816401500c0c00440364001e80d4001c013004d0042101507000320040c50000b0040c0c40c14440800e6078401d1503031381d083c15600b40c04888002d481c042034652254403d0b0303400184000415281c92040801105101d5102451101c00304095091000700071092042000400030440c056040c40002c0d441450f060081c110b01502c1c0c01d4441ca403003a0101d178010844046940e00002d0139840b6948844000c0c103e041803140d04905240710150f5483c4c074074140c41901c118401c80360700c0305220ba00f00350a02580b815014001e035054851 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 596761483 1250 596760233 596760251
    0xf0608060103030c1407050d0312140106050c150f220b070908101a01050a020c09010b0c07080f1c0e03010e0c1c33051e060f01020607080703 62
    0x203116080c021406035940d810b101e4018200b407160b00000c003400302607503400721504010540f100011156250707010f040c00c282c03807501c0d10821400b61040742085d8652450003400450380036000300c064001c9010003c00c4859031084040082c20700ac4040d100100f145195070005943c06ea403010981ca04c420002040503c0c58250340d40781d040c0c982d41940c5d02d1001c02d01d00030050283e1401048400142480c990042c403e62201c0e2a51000000002c0441c904200000610301741d44c0d40200029200e04002030082c020350b41c0d440b0f107131503480d400c2600400c003240110310300002c81d040b00084401a100001d0060460102c0040c1075254010f0300f0040c28050010040c40300031250307000c2c411406500e808002500d40c000b8803c0401854180e4401d14140244e03501da034810202d0010302e014022035822070201d0b13441ca0900b60700101021440010200301c241860304005c7d04410f00b8030000780b03029816281040a440e00d00400c03004d000500706150060f07000c000040d019034401c82c1c070b054215809007000100206 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 596762589 1106 596761483 596761499
    0x9011e0510050a0b09090c0a1b02120a05010b01260f070201021e0a180b0304020f1c030309110a03080301060c080d0f1401170d030f06 59
    0x103512400986626000315600001d00802040350382d659644442c200a60340c0801500760184002d200490801d00c4c040d800e9500800940d211400c020f99003c4526194101c1c0c5841a40e1105400403007580c018414030896592500480004c10f142880f04005020781441102c402c800000801c9141c482515600b100b540100390f0101303003001610740004c100c0c003a001c0c44009840d59500442484840321841c401030600c0c141c241c032240d5100c26081d640004a42c0310344507200c0040010000903006140000341c950004000401001a0001b1070042c06d03070402c10141d0480120b651603c0e031409004441d60349504500044074549003103411940d480410340010321605051024600e014020024110181d0307180480c1f00d0000c1004040c3c15a109000d4a403a440061203200740d14008075424074441d00401d50344445400138580001058000c07802400100d00c601d0680341e903880c011070000b03 = true := by decide +kernel

theorem cover : BRFrame.Cov 596582733 596762589 := by
  have h0 := BRFrame.cov_init 596582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 596582733 ≤ n) (h2 : n < 596762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
