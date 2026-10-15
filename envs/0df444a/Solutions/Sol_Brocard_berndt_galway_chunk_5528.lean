-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5528
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:09:29.309169+00:00
-- url     : https://prove2.me/submissions/ea219aa0-b961-452d-9e9d-6a24ab0b50dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 994064748 ≤ n < 994244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 994065998 1250 994064748 994064759
    0xf1b080115090f02090a0b0301051c05061803090a060503060f040b030a030c06140a020a11210f070b13050d18030f020f0402030a090501050612070303050c030c060721060609 76
    0x1d003c0c80280c24044401400c0c48070032004202c1000103600700f86405040480100076900d48403000c0545005c091001031411815661a55a40c49000d414003510801251140e082c0190030030a88090380402840108c1e400e541d208041c00c030350300035210700b40221101403000340e1500b054014080410000341c02800107810390345040360064120041203480945850180c411813510b00340890180340d000310011b985440034100034000c0041700961800741d0308030720199185040390180074110104d030190f5155588041181454043c86840001010101400103011075100d0f03142c8058201880b075000c0b0340c003050b40440300b503030340200c12010050705604294040c0005030087e500c84123128070240030a13107607040398400038003a0f0304201c980e440d1065444070188140728013405403541240054600d100560602c14401f40c42d4000c60201a0501000091b442c85c0300200b00110b9401c0b5001c00140c0c0c145042ca4a001020403c041030301d0f50744541c410781212049807052140f001140c9072515040680b92078032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 994067248 1250 994065998 994066001
    0x80601030311071208030f060904021005161e020114070b010b0a0c331a152506050a0b22090b0c040e100b070f020a030f1b08011509 58
    0x40c1810300382c003e0b150001801080035250400d0b80340700c0e2185580382e16000c2c10b103446030b22004166900c10f404540600000da15454508031004a05d40f0780707560789101307441d80c080074015140300040190b10000303a950b403120020b9801ca41400c2c402d990300d404260300e03402d17114200d000d0602c0280c00f04501c076004103d48a9143c2c001c0c0130040180c140b403540320480303440701e1b5041d071031804403260302040031a82d00c00c0da98503183c003203804210140c030208214032500d004007038040540c3d0300e810302480e6401c83c0c03070740382c0080c0d04155503400541c0c99070410360390041a00724000034081071048a401e428400402c00801c043c0c01030f01204d0f20081d207401540c40c0fa804c100c00c42000310350403401c400707030b960041c0702c0100303440e21800c40c41911020010b070f035240c2ca00b0f0110301c600580100708a90000c0c1c801002d009405401c130440e18000c0d00901da0740c000102d0b0b40001840d0b2400303603200a00b0320801d05285420402001e030f60710000807000e441020411358401c000c50a8584001e10b501c20350102401c1480800c80c079 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 994068498 1250 994067248 994067267
    0xb060126130203010c090915080622140706020c0607050a120311041e050a030323130618081b0111030c0a0f05010509030f030109090201020f010c05041e0806010303 72
    0x70038480c0d000301e401c0750003080c2140c1a40400c1000600c1e10403052011a1003030058070b81d00c140200d40001c450f440c20f0b00c031b1900c039007004c0c00040041100c10507096800e100030f680d900c0780b1908807552031452401840026038800e02c9101c2c5001500a101c007042d042d04e401000c0e40e0695070000094040c40040ea80c031115229a488000f0081c50768400c000d4031194590405880600740038880e9100c0c010340e4051ba0b025000c07290740000d200c0c0b0164041480020740c04cd8402031540c4044600c07242c000707140701c0c110005008504c882d4403000c26280c40020314607840100071020b005031000d40a0710540f21400240c0310a480c4c0030f000d80115048090300c0d103552141c24101c040c080c180302903904107081558610309101009800784c580c01000350701c41d000d129081c07103155040035a150086140c01016050380006010503c0388034003240e0b4132144e440c150390081c0b01001000d4032800007000780c554030001c050819003160040c880c061428800641108100c01704190680b800c540007045103038610364045503070361034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 994069748 1250 994068498 994068511
    0x40e0901090b0a0c12060f0b0d1103070806120106082e09051c03201804060b0301090b040207021e0120011409010506010c030305270601030b060126 65
    0x6a4241c0710002c1618182c0c01030050315610000b2503070b0920118000c20090807042661040c43c9010400c001d03d40100d00000104c0c0c10b0000501c0d12010b040e48600024400400d03144c1c3c28a03000010000c1a50707001003503900c150422205054004140d164a5007200d06034020040c80ea40564640c01d8520124800140c07180300c1001010002e9000c2081d040c1a201031000455150b0300a04124244185500803801519140d00e010025095a48202ca141c00d00804900c1140c84000500e41000c0d2104802402c41c030717601a205100c0241e50b020134000a920902c91488841e00d0a4002c550620f0580211002550018120002005426000d1010100080142d41440100a00c071119140040035142d8008004000001c98280000035545200b0f401403052030380341d1400d0100700f02aa000049000c0710382e0180380c0010140e40303c10050208586643d49000079140d10003c400d50060002840d5041c1e0f03100e04c00500c042e458040040d240c8104852083e044c40080c000c0b4540f081800350b60080e070008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 994070998 1250 994069748 994069751
    0xf090b040327030b0901050c1201030807140f1c0306080709020d0b100f0905010e060a180b28020105040b190f0c030911010e0607032d021f020f040e0901 67
    0x1c100102d100c1d07600b00380c0d00c01c070341c1c0303180b01020000600d03420301c101a403040710307060174502c0d0102039007201000150500005101007004a00e4000b800501d458021816010104640c051809100415641c01400c095458004100310402c10540d04ca802031408480c0750900402100c0d0400200300040e4019503441c10303640c0c0d500c44480314507584111035600c5241182d161113038005c140d884014461741d0142c000c54180600400001c002c1d480740c40071190001d0b0b01c7c1c60f100110301d40920b01e40344d25400644c402415414040740e00c984881c2c079070702ea00f554400c0c00c410504100b121840182e091b41c80c110342c040d1054400000242003000d200440c899070240c0c100c800903c40c0510000101203c4641002e00002030b5121003050422154000303080c9074100908080400740016400507030240b0602600600300892168000350030600d10003160301008000c1900300c41c41c085014001d40d1108102e02034154051164038203060b800261003155041542c40800911701030800710b12040310000607011070700c01d6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 994072248 1250 994070998 994071047
    0x80d050d051909290105090403050715051906140102031905090d06060e15130f0b03100c02070e0402030a03030b220c0e030312011710050403120f090b0403 68
    0x2c8155204807000c480c070804600c05411440500c444903140126005402203c90b20b00500c010b42e00c0f010030690050b8135207080c5503500300901e0980d280c030990107106d41615044c0002e10a04203c94032480d41c260003900000c0004c140c2d0351110fa01544401900315000da00104200754103a001c00709846060281400c001c1d01d800b000f5804103104010038001940c031259248002d014040d011549950000d00e12082e207584181100700060160308401200200c003039a843e0051101001d0303030445450903000a0554060007a04110340020745a50116000103008084c03002c6843c0c40180e0180c4d014580140062000090a680690052140000da1a07021102c00d16121103401800305065a00c54901c10106d10550001d0024280c4244060054400d41080c005840007688600440b81101c810030300340e0b00704c080c0840701035003032070025181160f01034141410001450b41180c02050105101c120811204c036020b00d294084030720f65040180445004004100860310410117100050b101000da81c981 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 994073498 1250 994072248 994072291
    0x160b0406022205360108030a170610180b040e04020103060f12020915101d01140d1d03030702070510051603080c09190e060109051c03020102250c080d050d05 69
    0x54a400b60300840740303031f80000b9035815000c1d4003000301e001c0c0706031041184400d070814a002030801907001c4446802c115005035060001156007070608010100d02c010f13907613116205c1204000364a0f08907400e9020a00f40200040c1211420100d0411500d5031081054404600e9007000f100701c0015204084041000170480c0940d503400d501000c200709030b502da1841e590f041d849200c40818503070392428188680482030680e800c40e51000caa8401085840024800e06001b480d2020106104584502c0d0b200110070006440c0d0001605000c9c0d40302100d01a04526410100302d0392881180ca016030b03c0034440740c0c18030021b4041c41c1da03290040b0030342b41258148110640441c003984c1c0c4880d41350382d02e080031100420103c00c0d403020140e000442843c111501c1400c240101e00100c0c0d07610180c07101d41c2034100341541894400e40c1500e501500c2c517100c00c40582910b22456500c202914015a1000c5641000249044000031226541302c000c0d140c40d824280103010b450000c00c0b000b042c84681c0207942d10003216 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 994074748 1250 994073498 994073599
    0x201020d0513020306010b0a0909020c030403230f0307030e0405060f030f0a0b0603030f0f0c010f02040306020c0105070c0c17190302060106091a040506160b0406022205 74
    0x424030b020503001e140c0e141c02d40101450028107900810b4119000c100413038141c1d038009c994400341c5a0340000542c1d111054020310b8614032642e4005005107030150001003442d00030312004561030000c4000c07100310002001140391070744140c0300001c02280082040310a10300303054124a03070045004107210001e2103a03002103070601070301c0b00080483d50015a00381042001d00c03004113410800590044d41000c00099660780107110b8980c0100e80e07270301e011032003524810003500142400c08840c03a040d500c03155a4600740010350020740b0012102e50030078000500d41840f407890201c1c01034200402626540c94242502c18580f01c05603804c4060184038680030352031b0440d400d60580e491180c0d0041015615014000700003d5444e000312070b85041000103600c61402203000d507801d0714400c98083c3d03075803500c031b05928a5003034650074010200b0750120100800d01016030302a00691111050041440c0404c041c08191b1890fa030240e80c0e403082c05030700c900c5035545c09940b03001c0401e1440880070700040381c503664515 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 994075998 1250 994074748 994074751
    0x50f03011409060a0c02010501030c0306050907080d02031c1a1011120a17010b0d020f090d050a201311250515090d0c0305130303090e1008060a09030201020d05 70
    0xd588400c1c14404d103100641310701c1442c41081c0c070080040394110350312214240c42603c8080d0449442c0c07000715042c2081441484010300114007129442c82c0007200182d01c0341c101b40391108800421004412009516004005c1e1820004083c0300c4042c05d4041008803182034038541d1703010004802a043c403903041c1003042400110f49110440d0303d49942e040e0080898aa04800d1003040360791600411944c4440010f0700c09c2d8030500f810143e195484568681d03c14020b426280b50f0100700700c5120340901c20b0220314144058056000d00d00c1312020750b4140030040850291682d0051f04400d0f4000f60000350758010f41d102907582d0b0300b40b40351596028a082c40001ca99001500d04003c03540c3c41d008021081184640c0240c008129140c41e103410b201c03581c0c8a00b044000311081c1b00c5510364020801d40700798201c030320801d160301449600b99160300300141081c1c264000c0451301d154a901141050384ad40d035440c002c440c000802401140c4d90032001101178a400c000840956401380304e0345840203524010503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 994077248 1250 994075998 994076011
    0x906020d0f2c1c050303070f0e06031e0a02090609012106080609060601020d05040510140a18050307051507030903020303070305030402030c10081807170706090b040f050f030114 78
    0x24003080a12004200740c1c040b40c210f402c10f50161040c0780100145003c001d603581710000e828551040a601001a10701a008068030390748984d00104002c10794100d61020004c007018103000e400c803640e50680c002c04134454251300c586d02030000e1000820302e6100349103a05000400072040c076000006900d550b0300b0365200c2e412001664006104121f0407003070400a2a501401c244000c00e041c3c40400c00143c010700c200c0c0245402020b140002c121400d00440c5042041600c40e41c3d400d9998503100c1d0f0043c060548003503010800005030701b00060a190020703960003a80c1c401040c0b00089407080311028041d6000400c128140301c40300f100000903a0701400a0f0200303c0c001e03100c0c00daa82c6070074410582000e426110040c800d600d00708031003001541c80100e141c2e21591202071000031041044540b80707040502d0f4003d61407640c03466a001028500440c0810403580180c13030318160079441301c800d60240e020f5800782241d8080c01c5503040116292250031650240b10240000032070304031454020506000440e840c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 994078498 1250 994077248 994077317
    0x53a02100e03091518090408121602150c030705130306021804050112050607030b032a01140414010c06140906012909042307090e01060906020d0f 64
    0x1843d11410052035411076501854595450a2440710300c41c00a101c4040300389028942080000f000c1020307110488420700d04180d100380007440c04034911080018600c00d100b0042c0201100b001074900c418801902038012040c1d82815a030f590802100c1e6900402c0c024041044280740000228546200a1616880c40111a00031010002c00d00050b144103901841030003c090300404081000850040d4200d00b0b186004261840c00e0b00000707141501e002c1070b180058141e0051460120007603044a40c001e40283c907106000012420002024002c80c800d645210160b0200c011a942c0b15005243d803a07480782800091181c1d907a80315414050003101c1c00403d550021006004800e095099010880c0c040c005049220b82c1c180b010025600844140b540110b4840b00488031240c85c40100d0801c01810300a0070764246003101c4024180c2c0158400d5140c1840340b80c0000c1101481400c503001502c4498008003080e9210000486242c1e65402c9100300300101c851590300700d1039044c41e074240003c410151 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 994079748 1250 994078498 994078507
    0x604230a0305191b064b1e1a01081003141e01150504021309091505090307300522121403031303110304031e053a02100e03 54
    0x416a03549442d034000c0780d03108451050800b249840ba581110503400000962081b100d50f0307a000c90014000803410080e000d8003d4000f41e0300550690300c00d1109500380c540b2090018003540040d12072000668038401d401c01c00410500110b1551541005441c0b0050f04946d501001420b0160b0121b03e4030200c680d0300d0f510b0b096100d00c88100c00380464060103046404500c0d141040302a016500d0b618880c0758040340c2c07599800c41c14460701103400040b03104201000d2000c0c0c80d0404402d034403035000e80700480b030b04030306620200844100500b101c1c21350350218441100100c14048107551641202502e141e02d22003440320b07006001018a0482d0042c80844910340001c965450214490902503002080c0c55105208010148000328510504140c142c2410144080040011030542c130950b000503095045c054024031542c03440030740026072140181c0540b00700c5200ba254004881418203035003007840d46040e02d00c2d0440320704036241080141c860f00494082003c505a230b0003d032004040b902107141c00106 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 994080998 1250 994079748 994079771
    0x207030506070314161d040b0604081f06080705060d0b030f072111190f08100e0105091002030a0e120702042319020c0604230a0305191b06 61
    0x2102ca0b811000c0b13260891003012030000006c2c81402ca800b0701c030481540313850801602e0b03180d0b43d020100740100070b0950740d0782e60b481e42e4030a6901c006403141c4181c40041019842e201c44c0062151000351342916025001041c501800c0040303c0e040740f500c4501196440c485842c203950300f04600d10b84060f01c003001c0c06000f4074000341c90029800082c2000c04c880c0c1003d03032900000714800204108400100d4024110940c1094161b5130001d2503000000c90740040540030680050001e9030040c540440001444000c2002030080d00380d585c2580c0d8100141d021080c511001c441503005164480890a0300241c0e05110296862400d803801a22480602d400100b107400d50503d40903105804103902818800c00f0843c058022390f2060040c0021503012810008503a801002c7e0100d07485440340404540b210b040900b8004840058003030b084004648440790b81c1d40200c004101400d80c46d4060b154036080400c0400748507005491201c050007082180d0b078000c2d030401c028090b5851001c1c000e010001300c00743e032034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 994082248 1250 994080998 994081031
    0x3040c0303080108010e030403060518030a02030d0c0c050d08070e0d2904020901030314040b0a021b01030509030a030b060702030d05030a2f07111314130f02060a02070305060703 78
    0x40c4c1102440740d0400c250080708440c0001140e003101d500100028290740c4003072148209a43c0b907014100c49000000300011100c0d400406000076810200040120340a090340648810341042c1d00140103810481d0b10760444d500595103103904c1030381814480510450280090301c03d910442c0c0440e4842540134400e081e80c14496005010b141c22084003100c141415000a40e030010144001000c200358000014807040c1030400b0f40b0000c11402d601c03541c03902c000b80d2010351120888420741d22a070000302c4040c1155880780c0112030084003018095403400821000440c090310070300c402c03250000010030810005071020041180e000e0580c4e43c030f8035140e0070450710081c25140482c008085568141d0844100d000300d4070300030000f01c144184425035540b46841c003480f80c2012040c1842e4041d84084144420049540081c07610034441e107482d02d4580d480141c040c00c00724000401601901c40040c45c07400500b010802807a0803541e074012203552a075039582c0e403803404000703c8031003002a407100100c0000c001032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 994083498 1250 994082248 994082251
    0x13030c060c20030a0b0705161109060d0804060507170c071a030402060a1b0b0f070908070b07030f020a05060406021305040b03120306010e031e0c03031c1104090203040c030308 77
    0x40941e8025082d44800040c2d929038007444064060303085200402c0441d40190211140000c101740c2c0c036034070440035050141d0741020340c01e2503d000346510400502107181c13034100074069030b42c07143d402e0382001d041680494464000000407500494100e408900a14041020b854000ca0350360050150f517040c881d244845c000003803030105410b44c1c10b000707000c0143e85d14010340300d548a0a00c3d0161001e580c0900c0501c900c00b0000b0040c0420300c1d06000d00ca420050a00c515104c0c59003902d5225043c7d44d80e080261740c0e80c00d107104000c1c41c0c2d4404d11072031b80040c1c42442c41c00262102403040350210030706900c426003003150544080b1803555000030b10040c844203920184000b0802190100400800140404d49441004c01c201100820020000300c040e802681901900c2d0300203421100003515600c807036082600720100d008a0740c0b041c1440f203509403400000300c440d03108607004c0803403441805094500c0500700d503c42015451100b884045489200c03803000d10b00c41c40c054050048005d203541000341507600e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 994084748 1250 994083498 994083533
    0x90c0f01091d0712020c01091e02011e110d08010311010806011b060609020a02010203090610030c0b070618120306060912020904080702180a060b03011a13030c060c 72
    0x158900100082091010840014802d0a5042c0c1da10343e220030049030030124660154040700c0c03012942c08840c420561103081040d110703c100ba8070800c801a404c801900708100020f000900c214118040c40400e104448103045590801d9107082684240036824190400c000f400014400380040080c000340c0d01040484040030f080c0044139090900000b0100c0ca94032081d0040c6500000c46034040000765030040c00181001d060442d21060344100c000d001c0d6000340d4a4070b1462291202050302c01c44134072000f8049940c442c085c201064541400c40d07440790807040d400d0f14082e903074140e00d1034a00400c0840c0350742c032032042252a4204925804c0501180c06641000c410032840c80c8051101c00022001d40c01a0350b0104c03441c002903034451424041a10035421300039005061140c00ca07181d009543e16843c02a504110705010040e1569005030707071400248104580511184508036207824510300400b001e0741c8e4000300340703101501e81c2c03103501c140f244d191700c000d001551040030002804841c8181200190 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 994085998 1250 994084748 994084757
    0xf03160905060f04170a0803190501090203010f030b1f0b1908161103070203010f05100e070c200d080d0c050c0d1103070c08071d0709091104090203090c0f01 69
    0x180042d0380080d5024900581032a417a14104082c402c1c0001c20a07450746030340c483c81481d600d10701010060100032402e00302885103400c103000800d0018043c002d40c0d06032080a107030b1000491440d183e2819031140030340400d0001508040307030480007502e809040080d06100c402d0305d59600305200d02428004818100a0400c24070000740004103120a0700c03041d039603100d881c0134801000e910400c01d08501c25124000c0d8550f04e4605030b000c41c02030540140c1c4c0720322a0407440d100a541e0342c000b5505152011505040090401c0584c1c0e0000380d8904c40a000305c0038040c921492a141da000461541c2c001c2c1d200545505202040c090b003000708038001d041005016140860600c16820700301d5a869182000700c3d000d01145c0c44000c141310100f0002da41003240c11104108007641d44500e5642c40312100d020780040301101302012000ba044120410b4003410b070b640d545101003490b180e801c1d40104001c01900e0311102d010030001495001e1400550300407501e501c06400c0340c2403010104900b581c02c0060190501 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 994087248 1250 994085998 994086007
    0x11409010827011506140c0d0804060b060705060f01090e120d02090901150f0f0e040e030408120d140103120e0109091a0f0105032403030f0316090506 66
    0xd0740e106441a401c001c01d800d185030414594011109142c070324403400a220343c0b0300004030b0240c000d0415003500315881d5880b04801d0010850058990703121705010341d42c00e984440c010054851056404c107070702c14020b100000b0322405120000708036500159094403281e01200038401c105400341e200343e00415851b003041060007100c10030252106c0c84000300e2510078001107006a000b4407241c0481c2d000072002403504006684804000808440b0200070400140c0e0388558040032134000e080c40c2041450607100d50b8920305010302084050820407014611742e0006000005030407004001c10000a40042c41c425101c00b10500140111020b00340c0c0f0311020034034500108040f410719401008104064603104e003506401e00c00503245080d980d80580103440c60503507042094103004250303145200007200c00d200603200c800011501400181c850510406130814481c03240020507141c000e0b40341000d016a0300b010b4002e01e59060941086401400546101110001c11940309042001520040b2640c6041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 994088498 1250 994087248 994087267
    0x4050d030c030e030f0c06070c17060106020d17150a08030a03060e060f100f030e0304031401050604090c0504020724020912010c08012d091506050705120f0408010c080103020114 78
    0x46d044044100b80c01040c0004800c02400f11050707480c1c003d041c00c4180aa8255010303c0000d42d288400d208030f1006006400d403860440e40f040f030035085d0006074a42042110303114070801840d007041011281da4000c0c4044000201008244045e003500000c1c0c0e140014038525040305401e007200000c1245128480003551000c880d46c410f078078102c140b8228a0311143d2540865425402807003606001034482c400071500108200000000040010407540288607030f49454042c4400e485e0854002451060201c0d024861803c25602505225020b4401ea100a903911549051051106003001c0c0300d440d00081c030484141401c0c90341e1546c0c03080400080081103054100200115010702444e4402414810079241044098002041e0a50600c0001c002030340d0740c4200c103005003003c4201301c103940c840703d6000981c58060700c15142640e4001000c0c10803251518200400c0d54001da0104100078024800031890b50801d00c92000545281c1e1a2040a9419400058901d4103e02d5640407074207010400e1070f12 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 994089748 1250 994088498 994088503
    0x301060807060507051f05160e030a02130f02040b12061e10030605130e0f0f07030809060f071b05041b030c03020d020a020703170406081b04050d030c030e030f 70
    0xc4480b14541991110388900d805400c044e1640e0703800728080c090345291846102e10b64400c038003551802400800042a801090760350100f920311096142c2c01c490044005810140d808588181c92040c00080032401e034801c40e801c81e08141c02c000f1442002283d060885c00b600480d00d80c01c11800c0b6405400301c0940030308442120072030500700f07001e01f480e400e030003d009009410000142c48004c000d080c0b1500101e002c04002e210180c00600c091042c90180381e8103d00124944001040e8038020300300c02829602c40c03841c680d00582c00c1d04d0700701000700048003602110300064200d0510a0366510f049032000e5110b80208043c1e0b400c01d6124524201518a18446240740140d400b459400c02082d02003001209900a0182481901c0c80c3d44c00001c500061590214084c000d581c801d40b14034402d4146842c0781c00b00740c0180e018000101326000007248050300c109500d1103003030224105051619403505e000c00c001544082c0100c000c9004d1020510415821125601b4034a4090700240301d10243c1c1c2c0b40c2c056 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 994090998 1250 994089748 994089763
    0x6030e100c0c0b07051905040b0d020714030f0712050406050912010603060608150f060108061509100807081612111e0406110105100512030c01052403010608 69
    0x303010580d90300c004600709004100c0000a03a42282409a040c64203c4020b05194048950f8003400c000d800002c245082c0548140d6042d02c60011a10342044001d1103248020751014400340c607000602401c04030030b26070420003402280c03440e60105480b441640b4081c001d03002a440341c3c5050010500050120b82d078800103655000c40c046515031507100b05000740600516007500050001c60401c6000f140704200042c1c2d0800b944588612070300e003030b61600142c034060002540e1300e500240540020601a1a0034190458410501c01d481481e150481c000200f0074190119402c021800c0da104000013150800d05141d0700042c40e074400340c40351600c000010112700da5400c4d0600002d03a20381d022406042248140c2d485641c01c400720381105410484900001d030802e1003400d0001381031600e201080d65040c01400d0103001d900140451032402d003001c10540c0075076002c294030f45110512803c1d40100003405254094020809802080b42d50554659244000d0030444c50290b81003060030003041070001f03004c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 994092248 1250 994090998 994091023
    0x430e0a090c0e013c0210060b070f082206110a02010804081b0109050102030906180a380f010b0a090e04030c0803090705091608060d020a120b1006030e 66
    0xa41c041810461390b0020681c500d000020100c03480c080250b400c0c061141520800607005c48440042ea10341400070345404d07004000c0c03141c40901003100011080f24280f40da80d80300741811401c1c15a503050348500080d40c406016007081e800c1100f0000d05410107032032400e90201c0c5000d010300582940000e41040e502400080407035a0025420070100000f81c008206901b01c0002406103c03003504000b03020350016105400d0b81d00512012a01400da071080074507406000c03001400000c221603c0c0c0100c1e04446151184071307900380e00c03011080100000c00f00c0709442e020000d503042e030f4100800c0c16294424144c00c11100c26808021180d5038941007050f0303400b1102d904804045503910b514045800c14556040103140308404000e00411640104512060701ea040e1500701c0c4541e0b074040300e2b0030340c840350040c05030104d0940340c081540c0f42000040103d0203400503140142c0d50340d4038030342d02558514500040e01c505118500744a400b41c28002c00f40020011880d052281520750b9540d00e49640641c1c001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 994093498 1250 994092248 994092257
    0x5030606090603010b030d120c030e0a110d0b0109050717070912080702030105010e19020f090f1206090d030b090106020c01110111040603051e430e0a090c0e01 70
    0x10b82e003a602500305504040c0c014081c1c0e8054402d648000e4061002ca0441b44c640c1e43c20721900500c22440f03031195061061103800101034903001a1900403005110030880ca802c6520102c0030030224507212565402440c0c0715400046034a440d010041c080000c84500384060454082804800d0f035003c4402c0c0141c45103221230703854080682ca00040e20344103a200c000c0d05942040c0000542c402205171103446108101e407100b2601109055070403c0344512a1460b910050500c211284e5042c014041c9104034800303010b0201040c48204c1181c54003000321031041c810b0780214000542240d140c01440e22120080e95820069410514082d482c0c480c00c18a06040100d01c585509003104250001822071081d03015031941c6d03e440340d4005011b4030003110310406000500d44c1d00219040b60000d120b103e0700c82c0d1484010200419070384545004034a01408850002c05e600c5481111074605040131180c02940740c611241440d4003d0052220541d80a10f001a01d0030070100b540640003103501542a109180 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 994094748 1250 994093498 994093501
    0x11040c0207030c2303100c020d020f1b061b01021c06050603131707050c120319031a1c14070f030210031407090f17190c1a030a0501090203010503060609 67
    0x404c00d81021054140d154584103070103000030f00344500da1144c00041c60701d500707646961084003001c0e42d0320000800740452650028100c0112000c08007006201c60744014807807843c1a5211041010708180c1701c1c00016540d50000300c901700300702c0c258020305229607910814000d01c4e14200001d80030b80801441040070f401112041401c03c00d07010003100106c0c60200704a9166003490610595403021916500e005a00b604d82000b5801c0c4008142d500300c1c280c0e100c1040407003001210840c09403e0604507201d074815281000d1040e940d035425519402e900307011000709000c016041c1021004400070b41c0c3da400390000070003440107002c070251100580350182c07418101c02559040032001454600d20b4040010810014418040e9000c0200b0301100d1900c802c2d07840703180d20707241d6503010401c0d10700c80300d542c5901034080d81144401c4121a15080c5025200c440d0380e10399a0104401170103402d100c2c03520001c00000400140c1ca500744201405003100900450840d0305000120350b60700d4019004d0742c4942080c40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 994095998 1250 994094748 994094789
    0x70807140d08090433050607050303060d1b081b0f0114030c07080703030504154a060106020f0105060a0b07060e011113090b060306010c03090506030411040c0207030c 73
    0x20030908030803201210400c880317106403400c2032000b00c154902e00200b94074135000040780e16250064461568010340554a151180c10801142d40c02400c0308a804121441e2070792003075148041240300400c0743e0b0000c0c02c2074514007012000c401800320004c9100e500c0102c1c204025990004080e06a4038584501680e0380c1c4034501011400d028503503009000b1000000c000d800c25515801a0380501e2280d0808604111f41c4a000030940c0c4448800c81c081c5c050190483d60343c149450101d2f82d00036070242e00f04200e0b0000100983c000e101d20700c0c1d410000d504c82001004240d034100000701c01181c2a03c02042142004c00000328030380c06610031807114600210300c96080c00440d91041c101d2016460003089070140310718455106800502c1c1c001751070600c039070f0000381c40203107070058641c03000004050a10f10340e2020300544c0c040c545000b0540420107040000b050b1a00c0e0400118091070050000354800490102004180d401d48580c600864001d510300b040040c0540c45240251500383e80e500c0c00b04161072 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 994097248 1250 994095998 994096001
    0xe010b0a27020405040f020403120c38090a05070b030903180f0916030b04020c06010501111501180501061e0e15120105040615020a120c0b09070807140d080904 70
    0x240c01090784503186c000418410360f0654014000c40f0310038852000c2140c6900300545240c9a540380c0034203902003441104410500100d00010040382c2c24071402d0354203844d1000000100c0c81103a1204a617404a40d402c1c0510200300304038401001c107400315602d1841e0801c051a00c0f0f018440e041090301500140c10502c0340e031744500128098801a00000051071300e10301400c11442c0080c0c107a0042842d200328041c0c0c03401c00d402191800c242c200d00400450f4039100044500c01c3c62108030075090701960500d240c540c4d2101c01c106008140701c00b500b0241081c3c02c03400c1030440300c040e800581400700b5081c0401415400c00c0391018140d0072405c10120a9107003401151800701c1080a4181c00c3c400000c40b65884606055814140c071016207003080125228119400080040786c0e2603805688458481c000050454035900d11072103180c80c3c8001b808805664480300c500301501c0b540520382101400f80b149190400c001c1e0001c00b40d450b010941d40d05048041482094043d002400902002891440310b44a5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 994098498 1250 994097248 994097257
    0x181208061804051c030212041e02090c07150203010518040c09022a03030c030109050c0f120f0703050c09040509010e070305070f050306061509220e010b0a2702 70
    0x90701030321061900d440c0c11629078103221025004001e8541c59068030301c0c446c6c8250b48044040d81c22440c4941c5031911408480c0e8030050b10a10007143c0b1504060061f00c1c0d00d01801e00602000701c1301d944030801898034410001d2219101074200348140010042c5c3d81c0c40c281c528800b5140111022100d480d40e043c50408860180c00c40d8112600020b4024090442d0103058141e4032000e50092842d52007a01d07400380c407480251806032484000f4001408241e41550050b5084100031401c9480d006035136400380c8158000e0001046485003e604106e80d034112140b80507406400d9240030441071034000b00c0718042d802403462407406103555a0014490200c02d40c03001ca1420040800c68a49540d07900e0220350b190030364058000e210381c1158000500e0309000071500e00401000307000c0d40e100d80c070b40c0c000800c01c0e8100c1d41485520900d10000300e008400c9000c10503404070201d59011905000e485160350a5499102d6814000c0c090501c0401200000b92071000190f0185102c11004400c0c002020001c2d015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 994099748 1250 994098498 994098529
    0xd020d02131505010806030a170a0203041a0a030b0d0305030a0b0102070305060f06151312062d11120c030714031e0703150b0a050d06031518120806 65
    0x40d241c28030b00e603508040c0c4420110b0300242e070ba40500d561070006141d118004000c009050106114030b501104144402604441015204403401c00f41c0d00c081c480320840e01841c000705a60b03000191100306641c5406005001002590500460314199230010440e100c01009603d00503681c1110500b00e0b807080c00300f0001150400b0840b51282080b02c420050004142d42c030310321070045884480c000010100946140c4c100c40384400090501d01200a504582100340403603840e9542c001c1018001e0034507220308096800324107004a400745031582c81042721115001c2d0b04803500244005401458071400295010f60b4061215440713840e00d2100750780c440c0000c042c034206250b0203c100160020303d041c1000d6001019880da1030306031281c5274141d0407514105003136410841c100006005d04ad01c580000c00f4503902c24a4510314264402d80c801007281c4481e00121043c0400c11480c0180c2d02e460302807043d409044120201c01280c280e07442d8030100043c02c48642c14002030360001011071741d503d086030040c6078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 994100998 1250 994099748 994099751
    0x70f24020d0f0c110705101110060306180503031801090503030103030315152003092e1404140a050603040303090203010c0e241b03031005010e0d020d0213 68
    0x240c00d601d1400107088210a2580700794540b00f18003118520903900503105861290141079054142401d00001403c112802810300088888041c105401007113045045072000200083c000d09519202081c0c9011480e496481d120140d2601d012a6012040360f03006020b4008002e030213044520654050010440c001d0300300e000c040000030626415801041980401d8608600300c1501c032400705803a0841c405010b80080c504102c3d240805041d647c02c2c01c00b0120741000c603410b00c4014400200e44510050300b031030b05c40c0d100c2e0000c280b000140c0110880e4014490800080007587d20b03880c040c09000342d1144511441c1c04803c50459607d0328aa52000740c08054442640c03450542806800f0f0310100604034020341c03a022203010810b1094040321969400181000c2805e0000d00c440c0d41142c4603400c40c40d070400c1003007000100690a030118107041101c2003002c3e540744d00e881260400465002d5000d40c1c140405501071540c580c0d120b0b1808901301d40d0454230603403044401c0c0045492545249420404075 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 994102248 1250 994100998 994101007
    0x7030605040b0f0f0c040b161212060b0301060c030f11070311100906050f0d060b0307020a0c06020c10261008070602240c1c140a02070f2402 62
    0x2074005242d0f100e40d802d1504182c00740ca48800f500c09030142100d801868000500042c4030240d5410f000388905007030051400b001480c66100e5802e04501c401154001c9038880003050350b031801e140070f404014801e00c80e04034115132412002a00e81e0422280c0207003000115295a01c5c400e0051405400d90340300e840441c3d146507100d00e045d02d820f103840621248500c841c8503004c1c458a1255181c0403c0d03407a150755550500c2c85045444405d0340140f81074054440d102c01004c19501715140c0614401d004550080c1168825801e21081070719498001d00d0454200780040c4c46140c07075100103148001110300e407104214214802511050b0403050103980352584002c28840305403076080082043d1103802056030b5080c0c6e600c881c16a80c0760881c000503c48542c406480110a44440040a50144034440309900d070001e805403e980005004281c0c1c11580c4d9609840c11820400d0344805511443c494000c5241881e03039200e01d800c1c0384c4458001044040d42a0306c403907001500d910a0401e00b200903809540342c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 994103498 1250 994102248 994102253
    0x20c0a031a0624040f140a030305030603030702030307050115290f36030d1b1a04030f020d1106041113090c0504050c271f1d0907200703060504 63
    0x3c55129128000a080c1898000724050b07880c5c0e003513203000d032000902c81d03c102840c654003a0307000d400c000c025039810701081c0801805a1014001000300c18460400056244d4440000128448041d0081c11004680000c02a407541728015400d0700c82d00c2a803070103a00c881c0d0020421403e486907408040e0002c03082085c08066617560011800c50304668280c0a1001050f1024107a40d01360364451500080d9406140c10f14241130b40c3d007142c11080c022031000c00107020781c6240300003646054030214001a00808100d020560510550140c0d000903c0d020441120326400b480e03075044090310180980b20a024450082d43e1100c0d610202044007500c01d100c00320450800c084440480e200f003601a604003c005004400408220741207142056003054050308030f814030040c02480400c1c0d16802110510114449260040d00401080740540d17501031010485024021f543c408900e405014000c500144000a90818404e04500d6900000030194286d025155460040c036584050901032404050005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 994104748 1250 994103498 994103569
    0x506031905061602010209010507021210020a080a2d05130b0c0c0c03070f0608040c091b120c051602031504030e0a06021902040504080c1c020c0a031a06 67
    0x81000006802280a51295004ea00b44d120f101c1d03010b0b0000d542040042c0044c58404200c40c807050b82041107441901829000c0012640422080b802080d43c41c41040a501d01c1402200c54910041c04004400014103d21a0103003024604025055484100007961404243c0200740541d801210218190510107418000c5038822f0360482c070705010f000e800c11018100024942d0854200c42d141084c6546030100851f24120060300444074050043d40015180205004440341e80100041c0365201c11500c8038007806014030301c91580366031428a200100303001d800a090b100b8480d8643c4488105050340c0c40003900746504ca0f084258107204903420300007031642c4803100355006282941d4051a19480d0780c001e03030366000140400030340c03003100c810b40f00c0041c05d01d604450741080c4945019410220721101aa003000e00e0002030488540f0400d031020240b9a0400ca013180003001541d210b1100c1c0d0031030f2a0b84900001941e41d20008001d2500403502e41e84822000020700d28011001c1d50f480700c0300c417810380c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 994105998 1250 994104748 994104751
    0x7171c0e010905030a020a0e090f10140105090601140a020102070813090e0a0c0303050a09180c1d0d06091a0f070f090806070804061b02031c02040315050603190506 72
    0x41c0000c01484010a0b1414006195200a42c004000ba01120305d40a1425916040202880b1450107460382d1900b4640041040301000b208800c2c000c80c0180c3c0110401081400507030040d40b0500c0041c0a000250b60041000d07142903905c1c0d021540d4850781e400e01a406849080002005861300059618103044a98922415103908000034451400c10112056551b99110806405138800e6801000080d00a00081072a040e40341400b440c910f664240140e074844481e0218000c641d1541c002c41480d5501c288805501540c8110044400100c039000c0f0301a040d01c180300074032003a0707519900c00174050141071200c1da5014440e41c083d410702d44400d03098580541503e001d0045003254a001c0c10a80c01080b408060750090001880c0d10358684504450300760000c0c1c1305882441d035810080f41104c10344a540f08494469400650796000d01c2e031000c0030010104150031020a2040c0000e0002849014074050040645607002c83d8540b111800203045c1621048a482031002004501080010105006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 994107248 1250 994105998 994106027
    0x30c111503090f0109053a030c020f06090a1e0209041a0115080610121109130c05041e0e0a09051603120513030602040905180d0207171c 60
    0x940501843d0024035080e5219110014000d07084000750f0340c840034a4440348203101c00607131507a040d040b038900741c0c2100c880b0141900d0000a42c48a210700101c540402001c45204985d900034a5a07240401d0704075126445400300419031020460401e154100c102c04001450341c0042059030181403910305000d50b071070550804941d0101d1080002001c840c2800c4a407110151611207400d20ba03540c1c810070190032181c86001c41800f0440d082d50000b95001d110303541002c007005c8071085c2d4030900d000030000000400c80c42c0304100350030301d07a500c402503901c142034a08880360a003401c1c103620700081c4150400c900c56000107100c1d00d03154003000401a0190400c418290188091340c0514022917030315040110b00e030101400a041603d021314045115100508046558031482101161a55140c0041c1c0c0e0146d0703c59503441d40c8903414000e0094808620540e018026402042c1146c03611801039250061485400600c020464a048030400b09011b01c0784000664811001481c40c0c1c0301020b071a1800c41c40f000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 994108498 1250 994107248 994107253
    0x3040b07032003270d170d140601031406030a06021605010c080106031113050f12190308060618060702011209121103090a030f05010204050a0f150509060304030c11150309 75
    0x1152a41d4180080c1e50303155201c06800c0403d68201030302c13180341c2c1e407403042e44103201c2500400c8070350309080a030b1065641c0a000c00f500054030303041c14400100ce80719003070200d40e10f100002017885036a950003e1120035155002c040540c40e49000c04001250b280c04401c050043e5090143e450b034904d5000b00c4241c10380c1c0312078800b0440d640310014000342030b001d100d8114610a61a11040c0b2241c0791441d03e801404070300070210500080740f800b010f0304020320107442440c456a00c803091420160404441640102c003070b1881f07814800c1c0b8540d40c0440d848a000c0a9018040001d450019a4460841c48400340c2460600f4486401c8070b00c6c11012015000034003a0001b0074982204592040100850700c61010003000481300c0340c11515400094288000304445940d801c010024681c0c48242c0c41100804800380410380c10752070071740a44411007016040b502001070401c854020b580e1031000742e076002500340c6001c28100140d403400321042040200c100c0d52000704514099880950f5200541c0300c0d9102005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 994109748 1250 994108498 994108537
    0xa17061507032a020612090115090e0607110604061104030218162c13110309010c03050403080408070303090b131709061c0207060603060507030b0f0303040b07032003 73
    0x30740c0c0415900100081d80200200b0400e400c03848842d540b190400900c0e400050441005402d98234005da255018040880d21030019103030b4114203200f102d60dc400c5608060900f618403500c2c06880b1035000f0401091595500f0044c107580703000c042600c02450f4040c1c00c012a0245a40d003040003081d00300c51200744829801c001c5d002c1e80e44035103040c0c003205145a20b414a01202d10061034200b03d40d020966401c042c09119200340581540156043e1040e00079070b0b55603030309000601c9800d4602040b0900c0615003018244400203510294466200d90410a0551540341c645800c9016003030854020304010140002d106000803201351241840748030b820260940c1560305001c0a0f00e0080c01403540e8840d60500c1141107401565544051071184040010310300441039903030904232500d541064403980e550b6070070040200d0b0548510f515412044959103007999000700000d940f4440c17809070035400c0e100810f40104141c026490042105c00101217200e10000c6030220b80d41d00e40007031000080e121404003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 994110998 1250 994109748 994109807
    0x1204060e0c0f1f030207020a1401080c1606020703020f0a1407120519020310090302150606070c050103020a0e0a0308030403090b03090304140a05041505040c03020a1706150703 77
    0x51007401c03441c40c0a040c1501c00c90f43c0c481c4a2960b0074280d0200e400741602001a04016074915011201070303c9401b900700341d56103d16000510303000004000000d850801c0094014a254282c0008401c1e85c4c080c0015948031101e281c12400c3c5451030b140342000b8410701201c0000c20410004c146540f038501c204071590780c1d6403072403540e0303000c00e60610140c42c90700142c40c071107004141d4143e54042540007400322a8118101401c0b1412519540c0e410b500580018203508020601806980c0c2c00007800c883c80c0c1d091408075103442060340703030921545040c507a0000da61342c00940035007035642000c8002011024801c0c3da078117140c0741690040360200c001400002d0040780052442c1e017920301032520711005604050030403264065640c240742010381d00090004001815540c1c03401119080c02c0c41601c1c0300c1a961911091205494030383e02041d051500511199801301c0c0d0011124a00700c0040210726495220100415103448603040002c07801d860001da88024141c0241d041002c40b138220340040034016046 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 994112248 1250 994110998 994111009
    0x13020f0304051c1815020a14030409050a02040303050307030f1d0601051002030703080c0a140f0d0c02010b0d020d0819390b150306150a090203010b031801021204060e0c 74
    0x900315600340300e800c0d5805c0c030204500082c105102c0ca06030044890140c01d58481c940030414400342075442c0d0707200203400d105c031039154080d2507004103480c401541044d0456a01900b503010003803000c000c2613600c100071410348140390000c0c100301e409090010310114201c0e24507034641c07509001e181d0280b91403a03544603006200008441116405039200ca401d81c0350400601c41c580e00c005416020400b0b50381c00d0001501c01c0100419072250039140c0f4907500e4036001200c0d02500d203508501c00c00d69240c06ca044015840b500200640030790f04071400d600510b4285000c604500805103c0030101c1d01440542d00407541001e046a83e045109480d41c2c42c0700082d0310419905048031800b06510002c0742540e10005002028064100c0d42d0303034000000405007000464684034003201e0a0003840e198030880c3d1164140350641c9405824103030000d52441d0306202c8210154403025105150041b15640080d43c054401e50640307991003a68070b40503065003410704058ac05030400c0c4407179000a0099440321901ba1901 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 994113498 1250 994112248 994112267
    0x120102070303052a070819170702010c120c03021b16120503040b160203010c0816080c0f0a020a0807030915022103070905030a14010e0706050913020f0304051c 70
    0xc2c2c000800e94004d00c60910b00403070f0801c0b101210f80403414894080c0000791100b183e001501d05a451300440c06000031a00c00d000c10250150040da450b00030142d50095100c601d00c01c2c402141c020108108882c00340490091048044480b6410302c0b80c00d4500c0281408a0354045099040440c1c006c1c0c5030f01d500036101c0d2251211401400340e88100010081c003607240000c1d01d100421400b502e01400c202d034000ca0b0966011340c04a40c001242207080203250b0036544401c00760b0101d64a000201d0386440128034107284900300b145201c00c40c010030001c00051003000f122640941c40880192143d48030b10703010b8032164090245656040c1d64240038172130140700048480b44e142c40605001204c0b10301300440382c0581d001810300010001c420314003180c03d840811070307a440c46110700c461144401e05074040170b08640c01040c2100d169000018100700d0b9581c4041a02d01030b90085482d442e000500c0b11014009110350459800a685d01000304402e111000c42c44118032031404820b001207001801c001c0b42c540e0038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 994114748 1250 994113498 994113541
    0x80709061b0f051b46180c020d050313030309020301060b0f090f1818161502120405180c09040e03130614190c0212010207030305 57
    0x10400a02074040c5103815007107030765030062080e00c01e244601e0b1142802d0108050f101414030b40742480d01100b608059003000d8142d00c1801c40302404031000000b0751003800b0180c008034804191401d80700b603040c10700e40a80c4010807945400d24070000c0c030003403841c0141101f0804840580201c1c04101d4601c2d01800440e4403442d40100e81260280295605130f0080c041c40c8011703a010742d698a008251203410301c4c001c040741c0441855013030315004048100300070903852112080c0a030484020300300a600c003421415800c050404644000c6010600c469494a001d0451082c40250302e80d00000c1d91554500d4000c0303941516500303035041105140b1841d001441144621034120078003c00765100e089404c2c01268000c40c1c4002043d1619101c48009001c0d20350010400c0346580000580403a0203004111850013030071203003010002c803441c5041400e03190140752140381a100c3d440c03441d800c1c80c81c0b2a8058140550303006140d192900d4014441600030340000008402181c039020205003c078052015081d0b8006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 994115998 1250 994114748 994114757
    0x20d0c0b0105040f0e0d0903140f0309060307020f0106030305040e07020c150a050c0a08091002070819033e010b1003090816050c01030605090f071b05010608010b0108070906 76
    0x24641030a0200900901c060038035025590305d00b02c00300800c00d0280112500c0720781d442805403829401e02030901980c9800c0c03020640d000071485600c2000100135920901000c81e4051384075520a201030741058814080440c1c0d9500e000008000c242d080000390040d10340c000c02c1350030726645070322007030703a6400c04046582e902104070380514050141301002080b2901417450000c1c203200341c00c42c81510b02600301404880140000c500394249007000c0702c40c040303405110700c024178072f140c03038403910648401d242ea0b420402c9840b44403594003414000d41598805801000a0411500d60f500c3d40000c0003016080d8004480c1010f100310448801c1401015542440103102640185104000360000d01d03d10800b01d40c3ca005c14040311a0300900c0340c04501186010b20f01404034401442c0004044820542289100300c0204043c480c0092450b4161548400c1a041281000d220354081c2c03901072103034120080203076083c01c1c000300304a08190041a00701c8020b0b00c80440c2030310b07014421b0380c500312240140310005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 994117248 1250 994115998 994116001
    0x24c080f150a0e0f18060c03010b09060f0a020a050c0307050102100e070e0103030314060103140402040b040e0a1b0f050603040b0a06030f0521130303081b0703020d020d0c0b 76
    0x2024515400655458002e18140007240d030740150b0401c24400310381c0e41c0c41030240082002000840d52124052985025000c5d02d0240b03060640d645548c003060050054124011030744100b0b0b6118402169410910b250b07030591562501c5200a603260101007048446000755a280185400c4c00200c030000e9070340580140c90191900b0b15010010540c942a03ea043d11444c0d0380085c0d0800d50903107143c069406540c01044242c0000e032881c1800d08c1c0645a2410907180440340203108044448054100c1c0d4100d03008504062048005805482c03000c84641072405141c4000e010484d42c441603201054080c40b5000c00c1070382d5070741c40d9030200183d44155504041c080002400154090b144070390300c28904000090f41c507071030341c880182c030072941c060468003980441d4a99580040340a42084409003200e500d0b4a480b010031079003542889180303c01410b109440d0042203910864041d10303485884044d1640d03850381c68500f4003e5580b4403040000001d4014000d02e5200c0794820001014940d402c021105844d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 994118498 1250 994117248 994117261
    0x1d0a14030c030a03050a020409110a090819080714030423100507030507061806020703110601062010050903040e15010806010f051b06071416024c080f 66
    0xe064010043d04c00c46e5406c0201140403a03151180c4c00c003190310110b985440391030017003001e404503803035811040385540314844150303080030307803900e8072440c82e60000350103845210920b0030b0000e00d01085d101000034003001c100070a500d00020044140520008840201151201c0501c4841d2082c00d45450004108101c2d0602007800341c802030000c2c621500c0c0009507c2c614000304500e140341400c1c21946c082e0005080c2061640c40208025000d13403043c00341c01d05500d815000b401c07441c007041911440700d4810758803402d51441802010058a4101b0050110345441c82c0030907100d50040c001c202c41c0c42090404035a002454525901c940e03d010f8442c00e1441d06d80000550b8441d1401406208000b02084241c4134002151200f6503c82c4901d8000d1845040c020005004070340c4a03d0302c034040341380c20300001615044400f0340341075583e01a01c16254103081d214004074040c0c85a150b2020a8010800341c003280d5529155405840d0a0f400c001120300d2205101261200c07410741d000c44d107100107100400d070b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 994119748 1250 994118498 994118501
    0x91e2d0109060302310b07061407030509150c0d060909140a3c0b1b0c031806041d06041808030a2c011d01022b1d0a14030c030a03 57
    0xc5e1114001000041281c1e1a084411568031080c0b0803200a5141d001d41e1403011a080006504400c9605050006141c92105540c2e1200041c2404072810310702804a24008007090482d41c1441030000244501900c486130407020705180b0404480851820110000141002c203c6088e100d52203201d440310030014070703901601c61400380c0041100d042c480202034000b159603240c0d201c0d99403195403001d01d6480c1c000500c4141900084003100b0044d03080051101064000c0110340c680c40c2c1c4d001240020166002c041407450141b43c206855404140543c50030011810510b14452401210103205214054a80090984040a000f8003141d02400403031880c02154200d002d5440254410200a0303003090b00304110030702e00d40d40c206650b035540e42600400d8070502010b540003080c094000d610b0203101101c002d2400085207001520b89811070a0100050341c1074200b4981181b058130603850070351030380a070075440b03104840085a098020401d403002503000072003901c000040c010051403d12603101001d40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 994120998 1250 994119748 994119817
    0x30c02090124121803230301120219031b170c220b0405010902040e06060c1c0507050102030c0c0f01060503030901050702040b030d03060503060a02091e2d0109060302 73
    0x220f40c0d6260114044020a81d85854030241d000b41c2c0c43c2c51200808040b46842c45100341c041c41c070400c4e8100014410a12201034805503154142d518922000c066440042e041d03601d80c02c0200072503100054001c60078842c2420700240e800e00c400742c7c0b0a03010007900c40350340c0343c4426460304d03084540940702050441e926021901501801a03000c51940200000601150402d8000307d504030750100b41804034004091a2642c8210183c2ea018030313150450b252140c0d1040c02c1184000c1800401410202d40b0b807184080d00e1000d6407103002552a41410601d01c0c1da25082101c0318041841454500061100140690300843d0005030180d032a045680d0700440740b99202100981c3c0040d05e4050300001518104148108002e003684c0024480c0d04280806040c03000140641c0c0c45203005010700059655200009400b041c00c41d45050320390440e010116140d054a0210749516100580d1045289a032002d0282c0c0d951f9000d03602e4181060311220300780c080340608076038100c0804108005405010181c5481e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 994122248 1250 994120998 994121027
    0x281508091c210c110c0a0b0412140a05030409140601080109050612030706090204060b07050309040522060608061305070b090105040b0c01020720090604050a0b0d030c02090124 77
    0x2195002c0407800342c01501c035840300040004c3d0034044060241e800501480d242c0d541c08890f84d030342c9140780100200d9180520302400020302c684600b1038003005100d085020307101120005554030388c0514140f854407500148900303010603040400c600c0d0142564940d151042c1c0c0305071951400f590070100d820b0000c1400410340340d0050006400c2c42e2025a0405c040c10405202d21008206031105205010640341507500450340440180100c1e40051800300641d0707410001030780c001943d0365541e4410400c400b054002e00d02c0b5080340c07820501c2803024941003d01501c1c849021510142c4a0060214082c4004840588990041b0700d05100745005480100b0040c401403600c40c0c03c0584419900c201580310160070a501da50002e0340c1c00c208050a0070101981c5616030300c2c40cbc40c91200102003525a4001030040703100300d60710000643e26004035400035256030006814403031507118a18010740100220b40041c0c1c03060b440a400010042c1000c1e1020b01c0301c440d14906141d088080d800140c40418403000030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 994123498 1250 994122248 994122287
    0xe04030c03142d07120f02190501050708011509140a05090f0a180201140a0306030605090c0102060c09011e14030c090f010c030905281508091c 63
    0x2080744512416016100da480c42500fa140c0b00c010201c02205510f02d01d0010450b01c0c6801c1c014032010804010a040b00c4080c1410404818490340c0d1003242090f064400d60b49038465115442828040c0c158445880381d00c0c07a0700c0703031900da90b22070421082101c5101d02200026042d08801d02c210300c420071160754a45009001e043c0d070703030b511800000c0500c00101c81d0900e41c40812410402084140d0042441090452405014961090f00000c0c40c907065201041b882d03010001d001e0801074880d6014000854109034200803d00b07151040903101c0c006440303218014840d442c041201c4d02c1c0407004032540868161280e07480780d40e80f0401e0010f0701130140019010f005055604040c6190340030011440754408040a513a105440c0d000c00403001c01d902e103e1410040700d0615140000c1d000203c203000e6640840b4610700d016440c2803a42220404860390b010345044030180019441c1c0000e40041305241a5101c41d01c16903100c42800d80d03611404002d24500d4030200304ca80d000d41c2d00807190003c0313a4214484 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 994124748 1250 994123498 994123517
    0x70e15090d0602070308041a04080403030f0e03010606090609171c05070506010303030504021807021506030712050106030b011205100c09090504050d1d0f10020f12030603060a060e04030c03 83
    0x8510b4202d800c000426004a58100c00708010000c006141b00324044009100915a0515444000c414007031400300400b030105910740c0c00a258000e803062850300800070001c1c800e031500e541e0300070000000c1d4890000410841107010a2001c80544002002e0404100408900a00003081540103505d50860001d10000304156008600c06100345070203940a5103010139070342002e00c180070b940c02c92100b2046403d400b035802e2152450f400b040c1c03026a00d04e00d00010665072918000241000c0c083d52103c103c100901d2a0142004010b4101c0e81c1100c2c041c500d290802e80e640c245074417520840d03101c02841c54029450004007840c1581c410003001c50786280682ca1540c8616107074049642c103a406860640c8800800d088465001c1d1f504548603c1c04c0d40442100030301080482c0f03050803003005081c03090a81c50010a0654800c0042d0074229072110102c82c2900c4c41449050035660042c0c4e84640a40501400074505c2e05542c0114400c8809603101d0503425600d6803000c55405203040000c4040114120 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 994125998 1250 994124748 994124753
    0x516020a051207062307062a0e09010b04030b01090c0c0b010803120601050c1518150a0f09030e0405100e070f02070e0403170907120f0506070e15090d 66
    0xd40c08006510003000524030741e0f04014000d0032a8405c070000e41142c408200d0703c41d6183c000902541d42e61030307001c540400c40c40858900c100d8642c0f03000c40c06d60030b507034070285003445150390290b4550201d800607205007100d6600d0794103140c0707140b06d1804068203000e04130740100282141c3c1e83c000c040a40c820b1030300709000c007002c1e61030f03004900d020382c0181000d0307001050012401060300380c2c2c0750b04034509007001480d04140400d401c1d280c0f0303011840300f481c694850b80002c2d20340b210890800d0000c0d8240b803c2c2c0e81100b0000e03121551410b01034410001c5140b9018210b03038118001d110364004950191920301c01c2448203000c000150400400403c03540c840c46100080d02c03201d04003000d00403000b50b02c500d0070400000b80001d00c2e05800343c2c010040c1e0100035041c00042a08102c0c03da80016046600f0405030ba62051620f24203d01e0340d12103023810051510401c2405500030703082600c0351080041c0d0341c642e01d5070142258000000c1c0e05440c0c0c0400200d043c07000c4052618001c006184010b09411402030894 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 994127248 1250 994125998 994126009
    0x1a130803090a021908160e0106030b040e100516020115051c0b150414061f110f0309210606100e030a080c07050d110103090606081617010c0516020a05 66
    0x24102d490444e140b0b4a01484941014440240f0900482c4425240c080c03500341750240120040c401c1c0c20500d691120403c425440340d0300b000d4040c20b003c008950000384500c002c60010601152002900e181d00b80c1c00b40740c0188180140c85400b030b09003109801c8a81814108040d001126101c49000918800940001408500c2c03851181d211300c0b500c48010004a0188419201e01181d41048a11000108a03059407080c05115042d404c4661040e8a2a00e400098031000c02c003c2406242d07110b103807010440304000000a20340003805a0307842203011100305000e040701d101c3c4203001c04283c02042c0040e03200e0038100c5040480b49031a140c007588000c800404139080c02112107040c0d5081d400000e000c590742904225201c003e02060300d01e0b083e0213080ba102c40103402040c030071090406442e10816002d129040c2c02001c003034032194090303d144410004558069400398032035650171408807d00b0803000e600622414041d042c858071014503140e075000000101c0b880251089074407181608000c82c81e0b4460 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 994128498 1250 994127248 994127269
    0x70807110a080a050706020d0504030b04061a0a08030408010f02041d0421180501180608190c120518030d0f3c06030c0302060904090605070c1a130803090a02 69
    0x140f13002c0e00c00d6508110000381007040416001c070034064100000c1000420a018582e0302c544c00070b80000728000024260b01c01d4000e0180b03a158001e00c050408541d00c0c60100040c003c46034080c0003005070540060400c1c0590145115000009050580680e0030032006440c283c0d202d4401c200d041d41c2401954202341c103005100d6240341c00a942c1d0109840c0351600c203001000545400d003030566102c188060003990440060044100300004900031400c40300c03009a2051509400d60401c1c0083c2e44800001405810000a4100d80a0030080401e065000702a240030a14801002a5180c140c0c0103c14801500030300c03909175031050f07666052000b501600c0035000d82008081709650080c440d8500d034010f080c0c0041041c404494034211080001404000c003800460b641a200b042e1a000c941001400816000c9405080ba500b40010404e10030390044e01501d03403d00c1841005141e00c0ca140201c0c08800e000c80718031480d8081d0306803090103d81804003071030788025210115801c000301c81c1d012903200b130030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 994129748 1250 994128498 994128503
    0x9080a0e041118120601030b18070e01062105010807140109030b09030c0d020705060304061e0f0b0a06020321060a0f060c0c0602010b0109150c060204030f021203070807110a080a 78
    0x42110f82036500d01c0e100c0c2e20721813000649001004203504517100c450781200050b20300c00084502a041094020303090004a004000392034400da603642c0d6403131001e0004540500324080510f801034100109002a2003035905072400c2d00e0040c14503e0a01000790025440c80d9012170500414000000008503a60340840c42903400700055903c0d10400d2294a00c5c01c000300b440036095420040003844161104000da076881500500080361034016100f50700c0500103c003400540c1103041507151001505c0a4000c4415420309075401550266580000ca85034018110b00c1c000b01c07500e403003140d21801400395059400c00ca0003070420002603a101c0b413868000596070b0254011881c030445400074807007031f40380e09001401140000d01449500c600020008800c90103090f40c8000c0d420351314450148501010010f06510050465659880c1e0510b141c0c2c50380034101c00c80c424200d2150608803d40080103450009030311085160400030107903141c034a4480c5003142e058002d00615000602d81d00c080190702c0c890f50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 994130998 1250 994129748 994129777
    0x1211060108011b0815010f0507120c1226060303130e0a1503120809013213030c0807060908070b100b0f0d021623010b010309080a0e0411 60
    0x114030750382c3c0141c00400c103100e940c144840a0104898610242400140b0003030900c0c0031010b00d070b08514282da09015414001d0050807540b130360b60304195000b102e8a1090f40c003038a202a080043e250089030b42c011150043c81c00c0030321146001d096003a004000b113030080d00060580f41000e909900c0b00c41d03000207642c440384045103a28240030700c0c6c6c0e01c0351040321601040380341c0d1007000d01d0661311250240e4428a48079001c01c0680c41c00920140300c290b11000721100c0c2c12080404c0b41c030007120922195000b000300e90740d1000450000c200707003222030f46032580966419102d000e1801c82ea81c40f41c01680d04544001c1d221541c841882e40300089140d07006011540c41149001440c1c10100c4000c2012401c542041d000c8001c10800e41960755511403d0b1020042080303405a40c655449102ea0300007007400c0c0000b426007592200b41082603502140141c0a1070300138000308000b864140046083d143c0004003d0500e240401c004400c161150042484080f0040c00100321101184d0841a10341e00040541d80082c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 994132248 1250 994130998 994131011
    0x20d02040e0f010f150e01081504050c0a0914030a0f03140a08221709030c060c1f150b090303070f060c020d022d1212010927121106010801 61
    0x10030405024406088405500c000d103104046002e8030b0001b240703100c00c0c14007040344005510b062035106404003c1001500034007450503c00445001034014100781070100b00560001b190b5010200e5881d003c00a00500500000d401c0c1e441d050000f0112070341c25001c00a29102040d00348841c3c0b00101b0b54044c1d941e440102919004041c0704104a5501542180c1c404210304100480c16148901c40c0b002d00e281c01c0c90b0360354125080002d1420b149000040d8000c0d5022403440800a800719a40240640b01d0540a0050800d00d08080c101c03540400000d1502c12405002e01540c0c0c4058050070501c240602200d1400d0456140c41c2d468101d002170440b0402d440d0107024421039814018480780040500060400f805c02d10983c9500541801186003003c200b600c40d9011000100310f1210340315010000d603960360610303440051f061202400b440c11501c2c02c1c0a94002c16401035250a590a03141030030540312219159a03148400e24100e10001c01c110a480c03003170040c180180103c0d4001e00e622030002070107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 994133498 1250 994132248 994132259
    0x8090313080309100516170909090309042d090309051f0e0415030f030309150204050a0f152724051215010201020f07030f110619020d02040e0f01 64
    0x20941100da081086010311a8182c11b00103180100070403503000c0c807902c1c0300000d001c20400c003034010014007540c003182200030700000c0742011008000000050f241400705c11500041581c00c4a0156002d030301060281d9003540c1c18160550040941501c41d18020703a40741e0b035620000c0d4140300c0a0040c811058074500e032100c0580d412401c81141c1d0300d402d60b803d20203130402c3c1e000010f14403601e00c005014811440000d80c10107100e0750051011541c40802c403002c0c40307440445540290810b005040c010142c1074008910b000050001c64100d0b13441b103000c2c548c48480c01c04104c03440e14200b41c00c0081d07032140b0f0b10312060123a05c080e0210090300201340c4400841d8400d070044a0100c0002d8200404c0c46001c01c8032a64400c40f0082e490361002c14820820143e217034230310040380217110b000740040d52242c001ca40c44e010164400024141d0600c1c5a5a0b10001c2d50846100c644500d0141c4200291460b440c07040c0d491405141c0152001402d00f8100609041e510800303201d070301070106c0c0d820158442c0d29005112 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 994134748 1250 994133498 994133509
    0xe0a1205060603100c09090f151d091203180717150a0506010504120305090618010f0201150501110f06090f1b09010504051f0609090c08150108090313080309 69
    0xe12524424052241c0c808150300030b80031b54003500900c4021034564519402140c40b503000040c00b00030990011110f05c1d641c03e922a8060400d2840340c0864801101040301d41c840022116110f55041c501d0a10f192114401342d407124540e081d410b0000e0050410000701c50201e141d040c204c0758156800b40c00a805c081840d03100002c401071401d81001d2400d030030b00c10340e070743c2c89001e43d001d031082d00310034103143d250505055800d40034944510b544084005900f80c5501002c4005640510b000e0702d520b0444541c02c0000d9082c0c078449110101102084075040240758402c96083d007690440c40141c1300300c41401981d0500b401d004581a0896511910039012602400c01c800c1600441800184400c00c0c1ea660001e100c1c10413b128961040e03072a0004a14116000b1079100c10034a00360a0a10a9070364a50300988210918400d01c0c0c0ca01e45041c2c01c4404143c0580314051081648100f6180c0c640c0e04900103451500c0082d1150700e10340f00034045005004482c680480182c05654011500c5103600d004100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 994135998 1250 994134748 994134763
    0x150405010506042405010507031b030509040501080309010e06030a060b22150807080606090d060501030507050d02090f1b0a09030516030b1506090a0b030103020f0f100e0a1205060603 80
    0x502d142c900d0721502c4002102e42c0194042d2a001d03e00305035200038500303042b40d00e02205a00d01141e0410091720004040c0c00100a02c02c4100c2500c0c207104903a43d41100540380e0092040141c0490122403d02101d481c004005507805034000f80d00151090300c80c000c0c05c40980004240807407800205c40c524007051b0301417804100030039040080c60f0a501c1480740003012040054096800d1050103000709902d9a29407080d1942d032100907040c000a1000e50030f00c1c0025050038030040d00c0d54020020007181074107200041210054010705070791590345800c0e0003502c200000901d680030390701c40318181610788a00b001c01020000000d0b41c0b10384111703040d420001d003851034540c001208544140b1003080003039104491242d10542000092083c5510000842d500748107040798180c1c0b0100070040031440c4240400514140c074025a808020190000c0c01c1c406518648c0b08040c4d0b0203604002c000750982e2088100014081003d0407031041140c2d5019200500c0089080480395030b0041070402c13100742410007204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 994137248 1250 994135998 994136021
    0x60504060f0501052514030706111608031302330712030b010e060d060806090f191e080a030524010507140303010b210702030301120515040501050604 66
    0x500034940b40c81e002920900c01c070310005a0036010040e902c8001101c3e0b0f8031482c101070300302100da40f200d40c0402c2c0807030b143d80c0450811103890b45064040ba040224030303019242d0105800f0359124110701a520340300816007004040c5802402031250503801070b1a07503007811440309008034203603400da6580d1911006940d240c2c90100317076180702404440081613141011064200700781c00c00107104040403004840708041d0b804040d82043c0002140b00116101c0d911400031240442d0544480d625800340940e156900c910702215030b0b92040c5c40782c1820030040b0300b500300c0c0b1500c2035140b542c80700d035420322080c00c1291140d0160340c00c440200c0c1c5452040c0c2c1500402da8004600162000090018000e454240321045100d030304002010a6140410910700302c58000d020b03080040381c1d101d61b528040200c940e4000108501c0c0d0b220b80105042010003900d40983c020790075034016506580c20107031020355442603034106032a503108003c2d24003c07088a49220034060382c01200040707414a4224144810740d15110f900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 994138498 1250 994137248 994137269
    0x1141509151b0a0308010e0a020909091e0c090f07020313060f1b050a03110c0402030907050307060c03082a0a08060a1421010e0f03070c091404300306050406 69
    0x9040004c0d80c4600c405041d1341a96011450a8907202090700090003a844903d0300800d2072014061a181c000454820b00b1740000140c0000140c0100e00f280c0b126071440c583c5420200b1310010a500828044960307a1042c0b40b48112405c1c144a0101c00030b4403c0c15a2052011501050300400305075440300501070fa1034101c01601d100061580d881030780e41c1c1c080c0c1802404003c000080e03e050102c0c1405032280b1490003c100359100d00f00089000d0700c1d03c91500c1042d00c0703031140340c00009904e0b000710044c01d046e42e09510340035020344d00c07020151201d581c034141c0c0c07110440d420b0303200c054940c1444000c0c3c500c11802d80e0390322a00341750103018000e044110380c200121184040d40e0180580d52851008443c140c01d00a00500c1f058142e020980035040c46c0003006060f010b89440120040320000192548034014144004126902e00c0220100c40c14200f1918032550204009404500c6090440b000c10400101c02e143e54441c1ca400d035009964490300c00790007c0e8032104200701c140ba2902a400191104032603 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 994139748 1250 994138498 994138513
    0x140a05121e0421020303090a090e100b090106081b0409020c0c010207150e062104050c0907080c1b2a0306060a1a1c0e0f0601141509151b 60
    0x900b0008150820310004600116071407400c64901744191803007620050440303040c20340c07548014400750500d02c94ac224280714490003410514103900400c0400c0c8000307841440c40340d090503402c554070000101102215811651840e101c032942c2802400248000e00c401602c070f03080c000b085814509a044283c0c110741c8030a00910071800d840c45010280300310f9050249800c0d0300071000c12140e000d0703c016030000341c0c0700d02e14411402c044264868422803058042e250490400020003030342c140d041d111080064a0000098180d0004038000c0c0081038034100c50548810780c81f50402c1c0390400b1143d00007602a04500c0040010450001800c2c0c7c80c0c208901920304c614112011988911151003001c405045410103200c2d2000140202d50482208800c0b054903900300b0308101016161906180c0c0c0d0360303c10305034924030142000c12181c1c1a00d5440e030b01850f031004207004101c3c1440303e00741003a4504000b0082d9011656a03000c1100000031480c42a98031960f121660801c000076031003003000c05030031050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 994140998 1250 994139748 994139759
    0x2012706050907081b04090206130315051e19090507061808030f0a050c0616080c030709060e04020903190515010605040303030f1b0806040501050a0302030307140a05121e04 76
    0x10301d4445d00e1010f014426041450680007030050825543d001c2d42000c00000d00f0b0480070710f03040c1c4402c2035a000300840c002400031000d4a00440d0402c0704c1c5d14004440c0640c1c50382c204200842529000710707620307100c00e00c101c500304414400c6030104001290180c0c0440c4040150320340201070f141085034140351b2601428601500240c4038422554801c038040000900240914040e4082d9610a07810008540310303441d2606a4108424140060380049990030f000107180803004011a4460304a990360001c0e6589410710a0340c140c4030441c0d035154425021303c0700e442d203034030100000c0007146550310000c0c1011030320b8140541000a00d00814028040e03080040c480242c02c24103c03401c80340d162900003001201400028020401d011810398511184d007456608694400d06860103044101c40400003641d9072001c1210180300da00c00250507410a2000310041880105607840000c55141500e040000c07a44c0d0311810000ca08600315103012010502080c00310b151400451412103025900b0305e8541082d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 994142248 1250 994140998 994141003
    0x103090305190c201309030c0f110d0c050907020703030c0312020708040b1317120d0e070e0f1f0512070f0f1809080f0304030201270605090708 63
    0x70354000120b064000780d035003115101c2e40c281c000040d044180c420800d2490342c14118545402251544103103010790542401501d64400c0090495040d280c81860304030030340c0d8010758414200c0b401d64806054107000700300d98480815054501e803140518500381d508040400551101c00b80a500c11948128070510009801158814000b501403d08002081d0710403801c0c00a8418503800030003140010500141442e60103010308590016403500c603aa041e00d0f140095005051401040c110340c2c01b03801e8210880c403643c0c4c02414a50b8002c6000b044441c5c031407890919003000760303210007119041a42084000401240340d0380d0810ec034903103449600c20412003900c440c05c00a0140074440d90f5898111050108204494001801c02c00c5284c91000e603100b0b01c0c88440b504034071604007a00e0780003800c140320b03540394400c00c400c41ea03011f4803581c245082004104515000108105c05541da20701c2145440303040040641007046030703004e00326540481860004113461002c2c0c9a1140d03648000341c24801a00003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 994143498 1250 994142248 994142257
    0x40815130201050705030d0c2d0912020a0b122413020f09090403050306280b090112050109050a14070c0201030209220c081b0406080402062104020f0103090305 70
    0x2440d002d40c913002c043c2046400c62252601c104840c5117840c0c91020507030340217070000d855070007241031a445070b400c00c1c041000004541c003520300001e40704034418483d9140b2450b44034001c0f030000c1c08610109485421105150303115071800d80c055800c16080080300c03070481d078005210100c40103080040d8848200030400c404d06001411030103e03000b20303001c0002030455003a0b4030300f1400100344e140c407401c0030300740600305070301c1a62164050340103010034007049040c0c1c1c594040800030788243c4510061070105200b41e03d030451103145041203900c184040e107851840c080c26010342043d00002520342071452800b42181d180ea15001c8807201d4545c100080640c20031050046290282809652541000e00040c0c41d040ea64059400d9005259590010030100d81d011042d07075a01c54841c5203442c1c59141c1145001c00700302c2000b00b50418108028800319102d1b12140d03401c035202038881414400100c0f40105000d604546280303001040600b048298a0442040203480000b0f081c104852405914000c0a6204 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 994144748 1250 994143498 994143503
    0x60b0a0602030c0c0906123a020703111207091a090c1b0325060f05371e060b0a0e0402090d080f0705010e0705061207140f04081513 58
    0x300c05c00250316a142d601e070314403074001100103552403403004404100504000880405110962024102d1002ca60302003107017990001d90010221145140d50703483d50402c5454100c0e03080700400300e40c080c000200f001503401414507410089002070440200d140c1d914101203000b48641d903403d0a009051100e281141d01054040d28407d4000c01b10f5101645544241c40c000496507004a20144c10502d8421201030340c0c03441000c09014401e2050501c000340e640c00d42d0304001108202c1c2a1519440310b105c80c40c5003001d01c000307100c030048111212101c00c8130160381d0101d0100c80c9080592546851038803440000e8640104c546013030007091040142841078404281e806107a00086040d81d60f921840003500c09940146282c1e5501c016610b211003c1e003010400f00c800c0e42c01d0032a0510f20110105440c2c0c1a200702034036481c01c009864485013516000501070030240301c00780f1113036440786c140c03035004102d0072030180c0c03500355103600c1c20948600e0113146480e0b04403c00c9050047c409068441c20071190800c2c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 994145998 1250 994144748 994144759
    0x80d020c09041101030f0b130b0a05040c08070c110301150509070311091302070c09021b01020906070b0604140f10060c080906030402011b0b040c05061614100603060b0a0602030c0c 79
    0x14091034001000b8003201d48081c4d84071000a0064048e994640c000103000a0160b60500200c0c1d510400c1c0030a6030740788000400480d1206002904441c4600740c51400c041c001c038440304811314018082800c43e042c00d00710000318841c1d05000d00031810400d8a80307400848600d02000364110540c1d1040c898001c202e2013070700c200442e40b41028607031003c2d0151160990804a500e100c29501e581000c02540460032502c07100703e24205910024070306100355600210301070b102610306440e0790340b80310740300100500150b0b00552714038a40e0210b040b0040f000f48102d080001c42001c5080c180c2d82c0f01045001541308a0410070f440500c080018451b000340c9079a80c2c820748825449844074070050750b011340840c0703c1a5080007807108000510421800042c082e0740030f10b000110a81e01e80060005a2140f110a108042455400540000c4040c00d0920010601c41e0035030b2440081208500251615944180e071225201d288410661416a0113800104058002107240504500b055a00d036440698083c0c8610f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 994147248 1250 994145998 994146011
    0xb040b070c0614041e05030307120f020a0c03091e030b073011030708040f05030c0307080405040c211a041107030207050603010f0308070f0c080d020c0904110103 71
    0xa0040c142803240d00e81c051001d120100c01d0b09810180d2a008580556900450401002d0300520360402c5d0340c0741e103030400040d5140d80d44140701541c0f80b85900e0314000c1c1e41981c4007050003200040348054076203c84940c0d40c0301c0c01091300d8103006000c9203064119001818020540400704c0361080729510441c2e0388840c41d540da5694804003a02c401035001400300340074040c00ca1a001c0d00340c1c6840c05103414442100104006c0342030100c840e07510b00048070b07002c02199a41c0c0105010921455100c40001e00c40d104407031602c03030110b600a05607007051030119074100c80414140040c5c0341501035035000054910f0034900c3e006941c5245944001c0032900c440030340f942e6560041910b105003625154100f8094414480700b07035105c000500a034813440d0254014016041c020583c1e10700300c02103078101c49418800f14030050541d201c010b400d41c020303c0201c1c0c03070109600d038030400644c90b10202d40042007840090040c5440b0050041c1c2018060744041e4840d411100401002850b00e0540c1d5100d004203207000100c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 994148498 1250 994147248 994147261
    0x1504050405160303050a090f0f12020d0c14041a01020c1c0210050a02010c0f0e280305061006080603030d0c02100f02031803040f05041e051e090a0b040b 67
    0x41c802034050b14801035003038400110030701d90044024000c284080d925207400725070b55403e8204808c1c042c0201024401c4048040084040010005070311500013400610603280c0d641d1101500001c1d03500c6840c8000b90420103042c00c0c6007900ca540c0412400c0890004401c114400007501e442c00581520f104282c10f001d8031038040312030741c458015541d018000306500100014041c12980040003030000641c21310501c030800520904040080751901e403103912505401c102080300c6221340032203c491408a1003000ea02140c04026a880214012000780103141490403006c004944140c201c04140106603042c0039681c1c5001048a50704a440240024011401c880881c14100d8a101030184c90341440c54408074105190f000350b024a0300208030500d11100e11500c2c40e124000d5128010203a03280003010130030382c00c294201c0e0341303c00440d00c590000500304000e68011070f00e0070b4401614040c00d0811030b00310304991440060b044004e41004200b460016507034480c01010082c070040c99414404007080c103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 994149748 1250 994148498 994148503
    0x9051c050a0c0306050a0b10391407050d150203251205100b0708031512060906060a0b190302160f11092509230f091504050405 56
    0x80c0c140d20a40044482d6038a09240003d0f2100740d801e660700720b20740b5011a60314501514142c0004801e61140034100500c501c6a0b2412900710016040c40303142c280302c4d9000606c111f1603201c1014030032070070440c0610351040d8070f43c90501180c11a0f802050307070084d00d0000c21503082e28000702485c0c005d00541e40ea5140d00c0c06100014543d140d50707140400c0c0c18010000c440e00311900340d01201c8428420040da030345250307421403000c40350320544108140c10001d40c0f0109482d6001180e00000c46104d07400e0030b500100c04a00d001c080421501c00e2038101d1428045c050b2801d00c20a50001d20480d038040c0f140d418140d40344150300c0f412640d82c4c1d81234042080b001c0a903000340c06239113100b6006481ba02d080e9515003003e624602111400300c0310b02e002440d079141c0900d804600307280240d841d41c903602e80050300d46001c403205005400c0c020080c40590b180020300251300c01e01010804450702d02103e9003000110074000241d651ba100c4520501070a010000311400002405000c80e030121804a216143c5040450 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 994150998 1250 994149748 994149763
    0x302010b06120906070525020f120d0906080114040e0c0405090d020f01022a0337170703092405010503060c040f05060904021b1b0109051c05 62
    0x1d03006040899860b41940055a5040c0f14800000c01d86655a548000c101e03040e2048103110040c03441240409040c15040c8402517100c10310242c15000ca40b0b00b10030018001d01031101c0700720040c0d07204c044504c1c9a84d5005007644000c10850810800c07550605501c85084031441c0042c074021651517801074404801002502c0001002400800560800b04100f5455a00c40131061003d480781524915500c072051081f11320b000841c40184c080c00e090501010303880d031452401c0d40d00c00c1c8401e00403200da1080981049014508804400c016540f44017140654100f41008507410b0101a10b00b030082480c0701c10050354002014540020400311070b240080034600fa142080da2140c00200c0c0700156240b2992000d8140c95045040b0740e01070740c84451800c2c0520690140702c0748414410f0b0304100c2420600094800340000400150800102480c2c4069910f4103030083c501c0c5a00045420800c0c140900e1900e0b949107081c44c281c03c0326030a00010601c2c4082103c580342c940512008020f00b80a418400c24 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 994152248 1250 994150998 994151021
    0xc090a020705011509060510081005040504050f0d02071d270a0c0e090105060a08030706020a0302090d06061503020c1203070309020306010b130506030f040b100503010618050115020601030f030201 86
    0x542c600d5266000d4500809490140c1d81c040d024510103840e450b40501c0c02c14ac850720445c1400e11010341020144009401c002e03008548510640c4801c030104601441012483c1c4100d0740100101854240c06944107e403071109100038801c51001d00000b04180c003515883c01408100341c0312000760401340b2602d050314032400a0304040901c500400c005207281a003601480d0000000e10041d116070003040b4640300c942c42404803981c070811074400058465005000340481905006007485440c3c40403d03592101040b007100d00c1641d4604c03c0c440d24440100381100c10409140c00c40c14070110360119075841302d81c1000e01c055094040000350407940309400050001e035001d0181c1d00c8a5a640c5911300645e0402255051514106180420039081102c1074a12404410f10701614a444984542401d03c02c084c0c0000003c084852001c80c2030344090140d00c00815079802034000b404048043c1030308032401a00039100d0000e5454007071840f1036000422506681d0800548410b5801c240f0302603005002d84100d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 994153498 1250 994152248 994152281
    0x26040503071b051009090c080118090303021b1e121206030705060708191d0105340203010e06011415040e180c010f020601060311040f030803090d020c090a02070501 72
    0x13070440659110f409102192540802800445a000c03000c0c1c0c1c144809002e100d900113080e0405980303110b80c903000311580f03900074140180b419084401c0030300c800c1c10380702050356a0380c07203172003d01d40c80c040312009007101c01e000d20b0140800d220b80078005411849240d0042c0101150000802e441c2c0d40c0c00e2140f08002d0000801c0302c0e5a803880351401c49100c1d0400380c0301040941c40c1101c4c05039028002c60407d81d41c1807001c900c480341c1c10403030801920f030342d040ba484011400c0e401c540042e1400c0d450004060840319485004e880c0e6200c10303c101429030380400041800d64000c01300400030b45485591005040308101e42c020402e120b0003650441034002c60740910780d40024501807001c90100340f01c42d0020701031507000340d0340e900071002c005503507034551104044016030144004001442c820390000c0310304200e8001003481c103a40ca00180020b9041768106030341c84ca00000a03c00c424030104069900100b880c005080d00000010004040760402000c0500c401e40000e0314000304903080d4024000044654035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 994154748 1250 994153498 994153519
    0x140102070f42180b0609090d12021602041e0b06040e0a050603030706050406090c0503060424110301030501060501090806131502040e1005093301180626040503071b05 73
    0x10480c004c0398050342d030b083c01200c100003c1080c0402c0031810103286251512450215003080105200950107207000c014400804001c2c1c20060703403240540390f440300c080c10601c104c0480c0e0710068030459907221b4290b4850301d4100070820800708509a10390f40403090240000ea503580790000b1030f05521a400000703051500e000100010131596511208805000b0303445001c4150f224000d06649000c143e6014000100201c1c0c03c0c0085082d2032001d084400751810041040c00203c0d81c810714a030001e030002c41d001e035100d00080c022564030040c05c00052150800825041c103000c5000260248a070318040c0800c1c4020460b040c0503000c81d01100d00914111082e0030a81c50950810303003801a05001d8144100d100354041030741441a0303078144410356203004150f46003d11502c41000001c051040e9113040c01442e085810510410b154000e000b0000c07901d5102e2880c1800c150400f4050324210724141540c0a1310900001c1507000054401156110f41200500400070201c4500014191f01142d4010000740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 994155998 1250 994154748 994154753
    0xc24070506160f02102f120a020f16020d0f03121b17190606050c0106060503010e041b05030f030d0e060c0a0c140102070f4218 56
    0x181c0988142d102c4100380d00703800000e100c00c40342c460342241d00e0001a4800407020b01c01e030440764401e00b0030300071a0036080c03202e00c03403020391800502d240d4450281b0309001050b10001464029006940124a80011403416103d0000c14890f03004206211071650b100c84a003808540b15031580466064104c17409200420a5180091041c0d0b4034480d2245602d0030804545110500b0b54100200031080f80c444030110710041e04400c3c0d4440b402051a60b08003a84038081e6038400542c82808042e02050707031801d40d02e01e585401c40c5c0c00c0d54070716031254040001c100010840000d441c5071072504030303501c800c20709805905071540d02c06044031500032940c18000d1141180f82c040c4004001d003100054040d09002052401103034585902c0d040b0740381740b40c681e810000a04041e02c112182155148207010303040160009007042401c9800540c0304031030004102940c0c900b030202684401012000d0001105c0c5d00d29007440c1003803200040886010304511900c8500d2458007440d801a4001a140c01c400d40071030700c00760 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 994157248 1250 994155998 994156003
    0x509131a0711030415230a21060608061c0b24030d091e050d03050f1308210c1b0307031505150d0515040f1407030c0501050c0c240705 59
    0x4090000124860300c0503509020f1440e0b00045441025003409418030550b1902a102c1c0403890040623001d1000f4140f500b0a0941403003982c3c05498503568041c014a003000c1030091040724201840c812007401e881800000c0c1c01c140142d41d1221800c2e41400d90300e206680f8040c03403c01e0266080e54540a05070803107100340da00c00f24800c00c0341e0000c40c040d8030700111a4034102640b0140e00405800c405422645008a8000d900401341d04c3c003040482440c1c103c1819071300700c2c100400d0b0800c02450300250f05a4070300c032300071480810034040000200d82c681500d8908940d91800c00b01d881d04281000c0d9105215690b07402d100c40b034011904201d12800c0b01c02c420104038001c14044a04104001c0c15014400c0c8508000000302032160340080189070983c100100c11491a000400c11034500a12280c601e0002d0340301c91458034007400d802c0060001d1130861034002070846003500000d040101c10300106031070580000350814820015500040404142c1880d40320ba142d41c84a607201c0c580c0001101000c00500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 994158498 1250 994157248 994157279
    0xc082502030129010c05060c090a24030522170415020105010f080f0d0c0629090711030417010b030102160b0105060a0903150b0306100509131a07110304 67
    0x3c41c2c60b0810000200c006403154002c003100504580e008000050b070540d1000014001d0f4400148080301640d41d404640082c00f0000050a00382d40f5540c0744458003a405000c1c0305e401035418000482c00c02d41c05800109038101e44c4001500c0c1000900443d0806040d890448026114010803410507803040140079010700020300c94101c2034008103400050700003000c81d090100c081688040d05030b526000c001201d8910030050140c030300c26a038a80301004000000b1054840380081c01c003030882d100b640b100300252008003d004209110a071040598601340110850b0150785040000880302102448024014a1141e4003641c0640c40080d01524000e0210b00079290340344181e00c0b12070b4507a21001842901d009058480c404604c40c244148001180c0640c03190742600405c00014240d00344400003403a046059403081400510810140040c3c20000001c079448600c0c1012904c1083c266903031a080c3c1480c0c190384040003005200801e0802c0e204880a68080e540c000459032102d41314840211000070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 994159748 1250 994158498 994158551
    0x60903030206060411091212070605240310020d0603061404021905100e01050910091d042001021603060f0c031a041a04020304050d02010c0c0825020301 67
    0x1480c00043c5140f505005d605200c25504c01c0d02410940c601007848084030800c1070b001c500d8001e11464940c55100c54000e0402c0a00804003c02c0c24141004c89841d480c0608090f0701c4410524006082c4c0e688000440035180041150b0041c0e461500010aa00404e11340d000140b20754105107181c184850505035286c0242d0007101c05c40340100e03080100c0018076a15108003a00f0000b050101030f011809608070340e2081006040003454070720180001002c40a0031224000400c101b84018465104451685000c10300704560024490409454089114650242d100540305110220402e20f034030a00460889890f69000000041c0d22407401c000542100009010001c3c5401d40310f0148a200f405841040c40441480c1401c40d007882003803101900007400c043d0f07003a911407605820310361240d01c01103101d20300402c0034123105101098001c1c02e65102040c5401000881c41009002c81c0506003240c20114980c901188600071650801c000d002c2508400703541540f81c1104031611840b0b0805010705100d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 994160998 1250 994159748 994159753
    0xf0504030c0e06010825180e0703050414070302010903020906040e0604050105430e0d08040906290c100207060218010809070b0306030a02032a0402400609030302 71
    0x6560013203500356142210209052280840310406019009182a55003e0320500300461010b44823070074480f2812068a04d400002d940780204414001c0b0038541d090050441e1028004c02441e50b00000c2c20720082c4d0201901c40d08201e00480c02a50381e40d485600c0420a6605482013407078281000c41c02400c088400000c0c0e6041e44c1d09e1b690340800c806181c107107070030f2400030740e404c02c00650903420030000c1d8070342d0096003803000729030700480756580e00090380d210a4446c0e201c4a54490515100205881c140c0d4411011610310721214150142c48070044200b2017a2030309039a444541c0000400d1510100f0141c1200390b07413000590b0800e004c2190010b03e9000805140c22242005000044a030315108079100030607900b09050520481c03401e403005580000005040f1a0043c16540020b400c14486a499101b0820001140c8081200c0c620b03a0518800003294110705114070082c03c4490a1124070703a41e0703030f43e0440482c04d00000c032886401080302c034000380744000a107864882c050544205800142c0c00361 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 994162248 1250 994160998 994161001
    0xd0203102d0506030705040b03090f070b070c09020f090d050304030c0308040e0f070503131703010f030308010b03060307122a08010e010b030a0605060604030506070e09070e030d0f0504030c0e060108 87
    0x90400d00103d0b40948091ba603454034051400080a0036a040a400e2003414003a400403480744000400c880c901602201d10392658410551411100040c020391021580d00e00600c01c0441507500f20042d2010104240d0385240b401135180740050a51041d500002c100d010365030700200c10300c0505000380083c1c41e800c00c0c02818a45400802804041d0101d40d0080080c00c00c0001620101310034000841480c45100101d00c0b505011098860540090f048440f02003842a420810f25501076210f500407c20200c5103807450030201c0c0881d4507124039009410701c4080302c42e11981040040151443d104040d11610440b010500603141d03800e00340c03403107645481d6003807a441036a00541881180382c0c4840081c000d019940c02660342d6000b41500030000340c1c0c440000d2200101198052040522910303065803080c009082070010800d0f694000b410302001c100c03000e4180c9c140743c3c038001051030240f5080e085c40d041405405404940e00e100d143c000400c0140c0c08400040c440381e076100f220b40102003d03240c50303045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 994163498 1250 994162248 994162259
    0x7060e010e030d0e0a050402070b0601031b05030c03180607030b0f030106060503150604050d080403200d20040204030515010e040203030304120c0629030708030d0203102d 75
    0x910795009525545070300009409264140184c1e43c1e4035000c48041c02d00650141e0360000981282c116010680e10321913100200501e660341480380c24a9484800c0d040d41401000031001421404001d01d603c1824000101007440d0707039111020219803010007000c8514501d0021700003005410b0002240340580380040c10b072484e515040c0a600155001a03a40da41550745044420300f112840c080101c5c3c0000d020031000c1066221141a41c1d069401904a956940d24603d0075283e042030303c411011450522146440d1070340d60380c2c0481100c060f000140c1c07415010b900c1d81c44c0c08405580781c009980c0184006400000c119010480c500c02d6850303014901c2d281d07070b0380d0300500241503000ca8000b9415081000010005202004081a5481245009038828807655070b010203d44404007074141441055a0b4141c1507030002a070481400810b5001d0402580f07080005541c9000d180280c0e508103401000241741c00383c590700724800400f803410400c00143d0015900f018001940c037442c600200d140070b0f01081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 994164748 1250 994163498 994163507
    0x5070905010b130e061003110c0706090e090a080a08040606051c031b020105070305030903041d0103060e2d0c061803100b01090509060d0f050c030c040e0a0b070909060807060e01 78
    0x100d25001ba0250038481c801420450051800f000c2c070040c0120180302c0c84803c180c0401280001d81101d4454440c918103005419000c0e0100038040c091682c0078518500002c1c9403c0300703a4003038032400c3c00c0a010680341c070300d414800b40000741c124540100c60a10640c82d240310f890303007042d00741c1d00035250aa118552983c0c0e03049a4209004041c2c0892002c000a5000a11a20065501c0711610307041d07908103521001e081300c410051140c01d8a405071103200600074030046100f80b80702c02500000030091020384610b0b0500e441050382268805000351540350310f0480040c442680251001080c03c1d6803200416142950700703840b040204c0c0680f0580c01c8000400b0124847c11101140c16195400d415242030104001100000e0220382c0001d01d48110308000b89045a4007a40380d84594050b01c841c0c04010241441c105080500602c40c0b400d2001840d0759802c040340d0b0607001504841240c1490b40c90400036247d40c0c5488d40120b03020381c6802d000040c00e80300402c540d800d8850b81e035104010070707200070011913 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 994165998 1250 994164748 994164751
    0x332a09010f08060a03022b05070315051017010908070b07080106050703080a021602030f06011a040b0304120e09010905151f120605040e06040605010f08150405070905010b130e 77
    0x70381000e07080c1014809850800300e02c1c07070703254014192087c1055420400f10310b240300030740044a032940000000c2c0204070a2400c0e141462402880070880d40ca8640343c0c41c001d00c5000d101e10401d80000005684e20500c0a4100c1d01f0000d80010308159140c0642c600181915011190303280040c0c0914000b0405070720031011107400e607070183d07a460b44640741c48e41c00000070f5001880d00c0500200c1d591550300103880a03c43e4150b506100e20203000300b98981070340070440c40003c101840010800300800d00000840005980c0c10a402c50a61002d9032800001940e10700c0d5400340841c1c0c0a959034000003a03415094002c03620038401c0d05194640e08046a0900c0003158104a04e0707240c00055940c4104264440e05040d1000032000001081e9603640d480441c0841e543c010811700c282e041038003088240070281c02080d00404081079400342c81c520705071803692600c011000d030f4058540d406011074144842000650042c1540d14820001965982180d00007584040469011503002e8400040c03050060070015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 994167248 1250 994165998 994166011
    0x71d010326070b071b03080a0b222013030611070803061903080d02090a14030309060a05070b01271512021f030c02332a09010f08 57
    0x4500348540781d0b0f103601c0300300c000914460800011180480c0c0181c92a59590b81e414080c1d180c0c1c242500300001d83e00144e40e43d41d031411740180d610243d00441c90f000550079100c4140906000100040e03000c0401114803030b43d00c4030b000c40b0700020030054140311002100b6000c43c0d03c01c0da0100403690310304180701c4603406601006007407a4001e0002810b142010b0088050f9000c00382042c1e1580c80e1a5601d03061190420781c890085a41d0100c1c02900c541080c090ba04d0251105810640c802140c10700060383d640710b403210385409203402003011a805406481078880480c2e104100074119a111800f007034140045000d0b10740c0090394442d40b03628a031024440d00e1101d184a402c8241086c0c00c2c01020a40c25000200880e0011941e07081050444048403c42c48428a15580031a4101c85104020320301100300c18402807004810704c80c0300040740341540c0c005651003402c078405a41d0b0380e00e004040314407075040100f1080f400380500c007001c0321550100500802c10f003600c80382070700d40c01190100c0d0b440f00101c035407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 994168498 1250 994167248 994167323
    0x91519030621380403030c110f060703020a1e0e0f041802120a0218060a0501080106020c01030c050408031602040e0a0f020d08160507181e0b03071d0103 67
    0xc421014030381c0c10103542c581074182c5140030f1480800200c55003904048400380c00181e0340352824000d50364480042c038802980c5000405003408c900680c641c44440141038482030550026405207128001e8004503581c8041e507a4150740e10444180241c040c030300a000e01480b4044100000c82c2c64078062140c030055800006080120503581e90034410303240c1c1b112404080d00d114a4250b9801680ca0b00c0303170f060344454405090300c564100308007400641740309070300224140300700c990040c0440366001440617080070b024030380402c8a2040c41820390303c61183e41c004440901001503c400f010b8001f0031180c0c040341c401d540030030407003070303260420398035244600b50003030042010003252000361800c11032a000341401444254642520701928a01c00c0c0a0010211459004080c0400c410300055440ae00d00183d4040f042c42000b0481003425030203120500320400d865522028410151001c1002d240070306488003e81483e6a406c0c4a412040002444221203000d500040024090141d01d00c14091040d40c038407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 994169748 1250 994168498 994168523
    0x60708090a03080702010b0a1202040f0c0804060c0c020603040308060310060b0a0c0c0b0a0206011805040327030b13140708070b0d020d0203010e04110108010308091519030621 77
    0xd003101d011401130051002c664a079480468240d555808400c010190000d880d25046560300c18882a68a2029004040da142400c03280d00a03070000c0b0300c140e00c02d611000020f01e0044050b02540c0d01c18502c00c3c0a9000a80402080304040c0c00140450048030100c040b6450b007009076080d2400e440c09806142e0481c038007400801e0384203003d80c100307210791442802014089922008001c0450300650891170059000e40010004000740d601921500d0a540d0700c140154500754074050440780304145022403904001c4030740c61000e010280301001441c0d201e100d881e400d040019007807080740e00303240341600c3e404108910600300c4040084c078002118100710140181515207200346101790415604840200e408110008084850344001d45c080d260311886503000b0b013814203160988020704889a41844144001400810070300810340360886811190740078580d0f1001c03542c1e5414010f07901c840b0b008242115244440d80d0300754210000381c0302103a1196010029400c0722060302c01a081c1c0207003540a800b030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 994170998 1250 994169748 994169753
    0x1180b0d0f02041703090a0b13050603060f030f070501110114070302030613020f0301230f101205041a090d23190306080d050f0d020c1608030c060708090a 68
    0x41025000300400d540050903c0d58132114004915071059660825420000e0000070900c0d024842c04003034201c1070222402e04044118412001405019880c80351501100040060343d40d1101c9040006000e03007a640c0140814a005aa816aa01038103010a000c441c24940c07003038051040c80329880e9482c4a490301516900801d80080d44042c006c185c0022000240d84030f880c100d4002072400c5403c40581d00da481d8585080000f008003c46400b580450407604052040c2c0d0ba03110035000d050104442086911001d50003d032003010001c20140f510310b090204110910250b0412444406c01140307805c0c040b680c030f00780e07541d41340d8212144000114541c041d0a00e0301103900420101c940b140c0001e0f2174608100c02c20042204d1007843d000302d000a0319224188007107901808451b0b400111400c0c094204219000703440800c0c019110344680191703020075800d80e80a01002091801181c3c2c10008000580341c0600c55104d41c06090410b81034130a01000c203160300d1050540c20b01c030340251000350010100c42c0e17 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 994172248 1250 994170998 994171001
    0xf051008010317071407050f04021c050a061a0706050610090614040321020c100e0f042a0e0a050f040c11030409020408122503050705010f0501030201180b0d 69
    0x60840b50f05100b00740090000169200031004142c1100b90092441910300310410118080100740c1038007403401400407161540c20001c41140d2040302c5203010034a9507426481c040204079179031004130b00b040003403d08043d2007002c0000307005c03150140505009943e51242840f0041c0001c040340000a440403800f080f8151281241c03812481a050303004d440d141c0e40f612091940d04440441c800c1202420840c001042e40400030582c0c50300d41078407a0500720f07001440180100d00090145401507845605445869a071030b404061504120101880ca0540c1c03041c0c1e0240d4003410865035004121403145801d41480c104500404541004101203e00d28004003484090580d1030429420702660629a60741700b201030000d84098400040b0043e120f5180841c068601102d11440301b0b4010001c12080110314520002000f004030000100c00b034030500e91070100d07030a100d150406002c4e94600000c86044280c1c0e50001412203000740d0300c04401c001101e09444c04000113106200b41000c080028030300d5500c15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 994173498 1250 994172248 994172273
    0x301050d0b070c05030d0b18040804121104050c130e250507140c1513050d150c080402090c190809070e040b1611070902130b130f0510080103 62
    0x141c0b9015051460f103a951500d15000b02a00c40103440d121105990682400c940907044249103e0640045080a48890210b44540d020b00c1c0c1200058424400c00e0100780005484001e2010300100181e04c1e00005203056a0015070303102da01000c00f11000242d00142d036804070b000c0c040d1a0318a0801e8185000c0d024002c002e41c0d00c40100b40501032141d00041100c54036207040d4000c00c0c001409260f030081d000c11808901354502d00100007810302907554807642e4100c0140c1990815900042240c000d4244491048038014440d0710060410000c0d1101551080040d8090361084d50507400035140c0d2001500140115030405200407451844205004d20403004030741c01407801800e94010311f44582c000d001d074080880b01550380e100010309100c0a80b01c0441041f104010500e0148089120351540b66142d00682c820300c40420b402107644000e070301c804e1508500801402c02d1150340c41480d0152080c0c2e406140c41044019a0310010000e0141461501e81407100c2c041d40c1c0d03600d600c2e801e665071100c2c40340c1d6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 994174748 1250 994173498 994173511
    0x50d050a0c02120709050c12060603040c08070f030320032a010c05071209031509060b040203090c0a15171003061104030b0105030706090e06031c0e040b060301050d0b 73
    0x201d800e0801584461401040160f24070001e00b10160130007010100303807031010b80280300d00c1000300001c000011905c014207030407040c00c64025070f9a48490406118400c2290081e2142d4044c02c1c00004213035400f11621400c6920945600b2001c0030f26070700461000030130842084040d00104500316000a1440440c2d08150321082c403003500c400c03105400f0b400c56850005690104100154020510039800003403038034251513240c008000c500b10340d41d07450030b95015030014080f151504102010052140c001c4490854007800840d200c1c039048141d00e82d5105800911400b41c6441c40001c12404e801404600d2021611340314550180c0c803c42d06030515410084c098000c4841d14480440010020b0040310380d100b400d03211264695041d41004000904180d000314441e40c0180d2040000c1c0790850b50540450f188103c403411147e40f02d03004a402d0910f0203250b4990a07406129642c0c4158219181a5401a040e00c08100080b0b128050100520013801200d42c042258068200021340040f036140d403009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 994175998 1250 994174748 994174757
    0x3010e0c0a2109150e0a030f09090903090302100e06040513020706150f140d0b07171602010b090c0f0c030d1b120c0e10020f0304181107050d050a 64
    0x245590002e01260500a00c1d101c030340c03640c0101d0207019084120b0b1316030180c40c0408020003171420031803036a076a803040c2c030040c14402c40081010342640100c148a004203508402804071002e03500c0d00424075480c0340800c920840800400c02c4255200e070800051055010b1f06c07080c0f505040500300b0880023141c7c110a0000c0c1d07001c0101c0400900ca03805149007129410100c00d102c0390800390402d1412401c2c0e00028401580c40100200c0380e6030f45905030292503000001c0c88c02070f44408108881071440c0740c0b81c1d110924800c000b4041d2441d00c0c0740140c10791000550003003021055420401018000036180700110f29800c0c01105462601c20008201703491f85401141d2078900e15402100c290781200800204803540324507c803080356040300c4442c21420040208000042c02a107000d05080701d1110f030540075811000311080500d000f045455644007800302140d8a950380e81c00494140d6821004c409041800e1000c0003100d0455002580c107481d620801170300c44010100c108072005e0b0040c540c40001c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 994177248 1250 994175998 994176017
    0x190807080a18110d1505040203011404080304110604091e2f0a0905030f0a02031005041505060109091a120304080616020c04020f03090607050f0702040e0114010f030c0b03010e0c0a 79
    0x6890317141001c200a40400041050700c1d05004050840d43d4640c1c510b540700c40344104000c00168020116944103074000280120884050081907942c00740d508000a50741c5030008a1a074010340500110b0f140480000034400001e10607100752a0b052a030031707004900705035000051180c51424000c1e00b01e06170395281c81c1e5541a40c0d0b4000078501102400040d0964200340800010f50034184480b03408070108450902a904040da6181000000c2e041e0b410001942c2c0c00204003580c1c881c85000000304040501485000034140307801512100d900c131784a10802c0d108000241981c0c0101c103450448028001034050341d52444003520403010500140e40860203001942d111a9640c1e00c003500131a03010340710075512881d2a4440c146000d0f4041c00e02c2060003001d20956500315002e504903086e01d9030654003c03a18590611940c0d000d13000b100380c0071060112010000c21503032600c1d1010001c40740180c044004555a030407495038184800c2c02001016400000004d4422a88034000d01c11100301d0f06c0e100e202c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 994178498 1250 994177248 994177253
    0x29041a0901030b040501051f050607060b22390e03030d0507020c0a150e030a0b0a090203060c0f03071d0a230109050a030314190807080a18110d 63
    0x108400360400c543c03482c0614144405d105003446541d5129040b580c00051000d403000700035181451602c1414400c2d180012000100010754101d2114600064104008144c100b040d54040070384c00300c0003036030382407522406000c020282a0986040d03e01100844010b06086010f8081e85450045850500100c00e20b9140180c508000030241e40e050301d80001141c1c00c020070000d060500040c0c1080c82015100d02c00d212076201c0031420b5079016240d0806104003a102c0001c0307800c10200c000060202e415000410048a160340c02c0092074030f100700d0996101d50b840c1100e290013400ba082080030045800d000094481d03002d1011203005513002407180c40d5281721080000d45064a076041484840188624020108400320102030b0340102424404007280c20170020503c500b03882d01c03025042100040c00c02c420000c41e070003264124240075a603107021030143d02c40507160038020340701c0303d0000303002c1d800107060126070344a4109000010600640c0c04841d54440c0c210308028400c0c2c00360f00c50308104101d0b00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 994179748 1250 994178498 994178509
    0x203131b1706150909070b1c060f0602010c020703110d020112023f0a0506010e0a030602040e15130e160f1403010c140703050405100507020429041a 65
    0xa103007040300050000d407405020442c110540c001c0030320302031107010090040020300400d103072041c1c4e001540010740740c0c041c00760b03a401c0f0003a40e0f640c2864020320b40030f8003140030030140c00c0103429582075800a0004240e541c0c1c0480e62040240300c040d000341c00d14003213003800c0e00d00410404d500500516109241e1840f182c021801c0343c2c003c200e5112001f01c03490041001510031105060448a24010101e00d22100c0b60625011100180032410711030740c1d400040d440c0d81c011810a104100050a400c01c9a6242c3c6400ca000754003500902404111000c0002c1090215240c02c8001200150844100b00ca0381507241c000f8240301c4409850138001c0d5804410395010709a0004000c04040d45054070203441c000d14805400320040050380280d060115040c110fa80210b21280c2256031025140d55031030f03060a040b40d090040390022540985545100d0054a80c0940902000b60088800308038006050b030320040301040100044810342001d01c000b49080c58164412039089014149040d44445007000268 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 994180998 1250 994179748 994179779
    0xe0a0209061f0c060606172d131103060c0924120f1003020a1e05220e03070c06180803031608090706021009081606021905040e0c3a0f0203131b 63
    0x1c503511000803212040c00000b03d65642c0ac03400c1900a4426818118194a000c0c8904030005004413034012000c00c0041c0500a00306601a448000781d41b10710401080c1c0c440c0401c280c413049404401580499014008060064102ca50042c81c0c2c02a941c50004144210707101e0113502d00c0d1080000c2c0300000c0b1a00c803800440300441c043e40100329803051028180d0f04170b80c16203c0c03075201a0320a011010006462400503801e8404600b0300c001d0007203109110420914241d04400764130702000c020b0110f0400c508100d004164a21703103c0c0c0725a691507c080701e951703600d40d100d47c2005a004150f075030300b0b40e4017540c01079a41c0b6004840311403401c0381c07601080700d014a042408561490380000c00d800d00d181031000c140004a000d207051454145400b00a601c0c1c2c00010341280c4444000040709601448910421040d0a100c0300e0f0b210400700300b0b885089100302c0c00004001c07941c0e0501c00314a1541a00b482141e00c10115003641281454a030748401040c500b0200384121546451340300400d184040c4420b07071703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 994182248 1250 994180998 994181011
    0x601090f14040c0306021b1605010908030a020d0302180415030515040b0103151e05040b0c0a08010b070809090108011a040e0a0209061f0c060606172d 66
    0x4104020028541801c5440321036512214442000601c0000f4140c001082c044035001100580c0300c460311403010541441412481146204d91044040c0840f03c0040c00002c03120300362220440d2650b01c0101302d80300e201d0488000016006503c65915841c025400362550418410b10b0449580c500300c04a0122007000d0725118442c40401010810801d013000741880108204c0306900090400d41d4401d500e540303040c000100101656100e91061004a6202d0319181710080c07400006141c0c0301000100600c07003a40c0544100305101c0018100d050f080c8100c40083c01666100d25076030f840c00389000c1898001243c111000b100800c2074050640d151501c6c2c5000c0c002c01c6000180f64004001100d84001d45a1003181c0180d09001d1a00809200807508050341130b015104d000c0c055403074000041c5403240b00401c82d1b0001290000c6035036019400034180e18103520410f4104030035625802c0075610f403040703e81300e01d0b54800000d000603010b41c4840c00710440c00a0003842d40e41c2142c030400c06060b04c154221008c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 994183498 1250 994182248 994182251
    0x30d20040314060c040612180f080d05070201110a0e180c0a090909080702010c021201021911010506030a0f0303091e1a09030d18080d0b0324070c060e060109 69
    0x410040403d00c046504841864159483d040c544000900042c20b040d00c255030803592000210620008620f07000040e552000e034040201d01d0741c3c905009075401081c0d02e191018501400039a02c17038014030901410b103501200c66810071200710300407a09030140c0404190003402e1482150106030301d00c81020700681c1d0613407480d0785402c0502c070300814411544d406400460b0501c0e0740040490a00c9086030902d03074082c81c0840e0b803034280e030010900c0d24061004200c8550700c0060540074540c0408006075035010503550704030102c80400303101802e80300c00365811a81900200c1a9a0004032141e10001211340700e400c01045e890026116151042140183e4850b5500c1254540c0100304510050400f8101101e00c12075550604001503a0b0742d01985d001038044681e1480001c81c0c1030f02011090070595400900b066541484980b41c0004c0d1148034400c500921841401000c03112420b034450031002c440d001d40d41600e5070350324000c81c3c0240c02e1010603107603183c0e10884000c50b0007050050b01c1c06801c07034010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 994184748 1250 994183498 994183523
    0x604090c02300406030e0a0c082401080601050922030c1a0405060105060a1206092f071b150e01090f080318060c16140901030203030d200403 62
    0x8810080c00003a0701c0c50b501103092241003500705040d002c25903043c3e494900d40000c3d0020100c401615040000f0b502500d00d03000314034009006400003c00c0140e0400c1d01004130a141038034011f80b0042da50031701404100e40c205c030005002504121f071100f070388407073310140101002070038155441e862418150180c00045150606000b4000c20101c2e00e208025514031002c942d01d01a16203944560060040c80e00c14000001ca85503098072a038000c07d90410b051000b044501e950310b4100004000c04042050490030100a0b100c681040110118003100410017582c5040003c1c0e440b40c41d0000341c240501802060340e00081106520b05168140584a50b116460741010b40c80001d00105001d81c80b8891040c11800240807044000c019100303281031011030741c0700d0660444005405400fa002c0b00450307074841c0c518220050452030780401301316203001c2c4c0c0300301d9602500814407503c028240800380d01907200f000000355001c1e041c0d0cc07041d0341c15044212040c030180302c00a0800d61398400d5000b17548040c003030b04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 994185998 1250 994184748 994184773
    0x2131203052203050c010c08071112010f0204080606150412170304060f0509060622022101060e0d1e051609090303050906010821090406030804080c04090c140604090c02 74
    0x4152001800c01f42400c4401c2207850fa5240302c0c900c2071a4009040400f40340110040351290a80c2010b48103c2d0070090040c1007004012a0003034200380726181c8248039034004a07400c5d040401340c01c50b40708a0840c095141c1424490b0b0303070480840401044401d00070301403400c00c020301028080c41c0100e21841c80032440740d640028a1080d51006418190550001c83c14030580b5518442c081c030010b849070621021030901c4015400084c041c10011348a020342c0c40d50303c1d20210720480811416a165511007011031800c042c240014200840b000030700e04079424681e1410b132000304513200c9882d4445d004452a40d210a1100c980e085440e510402225803617010603400c1507003500410360b004105400503e140d6150251260752288500142007007000c540c59900c6016010108441c03117401c02a00520002e596840c10802d6940300c2e105009060190b001804901d1405000e944055078001102108a81c2820119159400e4040616602100030040092103502c180110101c00b990307074014100744103100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 994187248 1250 994185998 994186003
    0x1050607050616210e011d06071d06030403090305100c0815040b0d080a09080a15020a1709070e0c160201390215070515062b0311010213120305220305 66
    0xb100200b103125500140e14510f07d400040b0769030b01105515107900c040c000c054510080d19082402c49402c4440041008107150b00b11807600116442142102c2070241d00c0780401c01120b20381810348002858900c041050502c0003001c84004580040c000503092101700c002404402000000315003c00b40429502211070b04948044010300842c0040c1100d05407a603600409425a2139160742015030109440b0310f214070a1040c2038035007011888008550515030341d0155162010320405140e08446400034640341c400c94159550380400f01d24030216060b1640c010b4580d03074040b04d00d41c40320703409070481c6442251040c241c105480020845940442c10640180070031141c4c1900c0720303149003004006000004100107030311042ca410000701800c1544a9800044d1501c0c40ea400c0740f100c11401c4c00701035075041c10091829080034404c0e281d40c6004a50242400d00303078040c1013420440b00e03c007100e0400c000804001c0c400300e1a4400d02d0944d28115904800c10054002150100c0b4003078041c0c8410f00812008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 994188498 1250 994187248 994187261
    0x1d010c03020408030f03100b0a030f05130f11042009030709060e0c0c150f090d0e0d020904170406020f10050408041806030203010e01021201050607050616210e01 71
    0x145429460241007400c81944d03482902c01c075003144040000040e60740c4000404103c09070032442400e555078200e11100030b0280081c28940031005203401c020600c2110703824800201c3c950b01c0a881c44040c041900c1d4203055801c600c55158000b80c40b9038540300c0e00c2c060b03e1003400c2c42a40300000385803134030184002d261900306a41c1003040e00701e02c3c100303050000611030003101d5404104d1805259540013003007c918140a80da0840c5800c818020050200d040f01c006101841000a40d0440d4480c0c00340e40c40413208905141ca1007a0442550386001016082c19205039a115004140d00c0d0a07400014038070401c99803007035004000603000b02c88801d151100c28070901e50350180b42c4400341700506090300d501c15a03200303920503074a42015007803051031000d445410040085800034002c201940d40310943e01d0107075220310118031240f5019070000c039031031809405455001703030040e000385015a03843d80400c0c404640328a04801748650742c3c0001040c07243c182100802031040b0031020a28031001c0100300d00b510b01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 994189748 1250 994188498 994188521
    0x30c0306092d031b0307020a0905151807050c07030b0f1e01050a0b090f031203010503011811010305040201180602031b0303131b050d08040509071b02040b01050d1d01 73
    0x110314000c560002e40020650b401030440004d00c0142c0c24501650300d28521034203800030b40101022074009192900e640c0310901c200c141040500482440303100704030b5441c2d580c252900079241d042c004904114400c20180ca105680c84d011195129120b443e54602e105003220b0f52340b4640152010848503840d6080352040c414004040b140c03055040000085007440280200540300c01c0100301a205036a91074000c501d40c94000d0300ba90701004114107980382c641c1c003d010340e5020390308110701c000741651549030031060399410020888100a1180044000d001c0150003641004100801984a000030710411b4005190580013140d880f9114074400c00e0882c601390001309a500b080c01007210b060040c135851141c0c1940b01c81d8242d030840c0c80107400e036500c6003d82c1025401100c5451514100124000208103455007100c031b01170560340302c0404840d1034a802d085d0109401100d102403005080c02d40020700c4101c01410b0060130032005203007440c07c540d607650a207468242c880b102000040300070b22030342c1c1c0800c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 994190998 1250 994189748 994189813
    0x31d0d0e0f04110d0b19050f0406090c0315050102030f2203170712110a0311010608010204081609090344100e060d030822030c030f0305010e0403030902030c030609 72
    0x113483d03100300d100c801b040e01c229402500005401071007039560ba070000b409805a5078040010078190000100202420450b45034410400e91002c21b15600010035103040300800120140340040c6224a04041e6011690b100604030104001100040700400040840c0c0c0b4007100b1103403503401508000c1c0514210070102c0307040c0301ca91100350030700004c0400c00709105901800d00d1030117249030100c460b0051400f82e001403000d5101050100d01d10102003140075001d41d01046601c003940d11070340540219a1080313801008070361030031030032042d9840305407800140400d0b41d0510030070744005254044846026202000b0400854010008080203000d00361024100e068100c0b1024500b10000c00c8440c0411000035061221000c001031800038a54000e1180a0720300b418075681c0c2d0300134035010344003c000000460100c0e03900700e03101c80c10520038807450f412289032030400d40c0280c42e1918213500074009070314266058050102e0000c80380d2010080c05000760042c500401416a0514000b18581440780d80c818518 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 994192248 1250 994190998 994191019
    0x7060e0d170705180f0915180606040513090f0b0f250516050316140f1b01020a0219051e09010603050903070506070e01031d0d0e0f04110d0b 62
    0x115803180075100001300115140080343c90b40c0700000c94403096020082c1d0304c8071811041010078030b01e600c003000214a003991407403500c44c0d000010088002046512580040052008004074500400950001d14810800040e103800c2074465615411b42042c058481d9404c0c40107100080580381e08407540107000600e82200320152851080401c0c05e0b5083c1070081007008980d406810501606007041240c1c440100da646010400c141c0d0307011440ea81040d41d04203010303003064440e0580460740040a110386400340c41d141108001001107030740c041491604512a409003400144c130f0380c1c401d10902c1440700742441d0600e07180004000058070010040640c04444040d9070b100c0c0d4a940c00c115041d40c80c0c60501003031070b83d10350140c40d107180200c90000d021807203840103201005070028544800020281d03401d0110981c8140c100500050700003c1004d140c0c8110102d1402a01c16030502d00110401010217010681000c002410b45a40c10712080c0306d218005a40c1a80c281c940c400d44824031410784054110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 994193498 1250 994192248 994192261
    0xf0102010219031d0307050d020c01090b0d020f270906040903050f0f160b010504151214010b0402040602010524032e0c0c0b061e01110307060e0d17 65
    0x620b2111800d001410303110000244140704c1044441c14500110341166204e0000d401c28903550445001d041d005805100085c182e154455036890055410400b0964644908640050002c0d8080020020b1400e001d00000c100c1503c050003c44042d0f00032007001a29100c943c0c1001000f60028104510691410498100180d084010368803581c1d84a0750180c2c13915183d2402c40140d209030a092040000e001052100b0081c44407000c90594605407010455226401080d00000c801030254540701c0c5480c5880c0000a0300c0c031403045280545060012580d5a01480820166000358003c5c02c0941d440c3e404000c8c800b5090b41e019150b50729140f00005100301c611003c81d44401040000703180d80a000d00000303400e9004c1b090070a40c502d01d10070040000c418545c0d0f00030290382c801641110b860000b00042496403030026841941468070340500303000802e079040150358811090074202c405000c00c2c0100720204803184911510500358001810b40c454000000034031840054605a405100b60404d0028 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 994194748 1250 994193498 994193527
    0x140103053f13030b011e0b070305070f060e06280207020f0904050a0b0c0a1101090213090c030606090b1005070c0501030b04140720060108061b07050607020304050f01020102 76
    0x10003858000364640c0c03802d1401940160782055003010f808061035000011720180121281825000c40307003404014070b40c8454510465104011000c4c5c0010003d00048003c9038500b46d481144030320500000460b580d03042d0485003028012540b03180001a030803400709040d0b02c0c1b8150180c003090305500444c50407480f6400114429000e540381070007403100c00000b80030030000300207041d0500e40101101e545071600088859555000120100c009000ca08020380520307014040c005640b0381c0100114030000000c8100780042042c420269481000e1000c0080454000c0c0b05500c007030b140c420004a44807010745c02348924521180f9484013004410040d03d0003180c800402401034900910700410400c50304000540545000141901c1904100c8207101602e034000c1101c0c00340c008211460f501c5201c4044540d51102e500348600c00140e000b400004280c05040d0314000380303180da28041d0504103030a50b22800d2401d40111548d0000d82e00c005000d001501e0b00f181805c8101e0720901c020761806009120414 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 994195998 1250 994194748 994194853
    0xb030105010b0f03090f0109060b010306061701031407091503030810291b0c19080a0b09120d060f240e010909020a020102030103060b0f030a03110114010305 69
    0xb071400807022035440002486811411b00b4160300134441ca1032341e82070080080240d1040580030038500400042c22901840340c102c1030101032420710a503a072035909c9011028102c500203c10b01d02a140d004200000140b040e60a26100c41320703580c03542c03411482c020704904006003510420114511b0200007104d400d900140a00b440802c11003001d4101e4001c0080a00541e0054000c2c1100f00d500149420b100103a00908081c08482d4042d020000561130714154050303004050351600880300440c041030084842c1a04010908211072544041d08042e00c51750704512820500b80ea16894200040b050140c6c01d0b1014040700c0c2c1c608205201c00c50082c124200001c410030b0207001a0403d040100d03801010818014403410700290354400001d60f009000b58424013048468500d0b0004815240c00c01c1c400e0502401d02c042c0042c0301080054a0681d43c1505078070642c141503407900040030201c0403000003035000314898401800a400d090720482c1040020f0344a51007003600a84140c5040e00c0d04c400070b103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 994197248 1250 994195998 994196017
    0x30f020c1020040b0304030e0a0e091006060e1806030705060705030703080603030a0f0e030705030f0709050108010c0f1404050d0c0503190215090307170d200c0424080c01030b030105010b 82
    0xc018004540027041b100d1442c1d42c8002c280900c2c0f9401c1048102010038820010800304104002080d00c902051380c4220b03498a0054000c1282c2496510100c60900309903004480201115000c9030745100081c0310341d2049904035481d800101d03051007055000740070982c200b44100d0146040880c9800018840010200b2a00030840c1d1100d8010031620240041e0340a00390140079101d1102e8100e108039600c208510402001d18a04000000d9803c418403854588081d95a18038400000d9604215038032030114001580e0780c142048001120f5440d001e0040c500c0b07205c1d002c01100580341c00c08150030205038000c9428940c100c5822100181c1e0f59001c1d00540c40d8000801c00e03110481c100c00310b444c04041d07400059003511306842850004600040000b40c00d15155500031200307a03000f0244111403900c2900c004c580c1d1000c0c030300c00352a1a06070410130840890146a48001d09a2650040d40c4851644000d6064208250042c49960306008200d441c4c00140d0007441030b545080c500f407045101c4e03001031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 994198498 1250 994197248 994197257
    0x2060304020603270102031f2303190b06010e06090f090c0c0303041b0b191209080313020405150f090606130e190e03030601030f020c1020040b030403 66
    0xb182c01139201c03140644a50aa81d01c1d0030210350154a80d070007036000341c2d135002c000c00300c003904005480c2030b1024a106440b0010002400f20482d035481d19100c90030440306950602810000788201c600d10011081640c0c01004080000c1c103080001420122045000c03a028800030086650181c580909000400609032403800c01e5683d024101d8000b40601024612180000828402481180c0010700c4040c8521806112804e03958081044d2a2248003100d88000221100710102c050143d80c07110015410140c000c652005d01d0b980340c00d0381d0350044070440c80800c40e180010081d030400e4406c040c0d0100f5659012241c0c03444402c001103101010f000568464004140060aa0f4481c0300076038111081b142000103115896400304004140101c5410800100d2400d00040600b454010603a44400c0031028614580f1001c2c0114041d0016901d0031240139000c01c000d0804660400901d08089056200012090103c400c1824040c0c42442c010340e01c41d00600050144010000c222a00258507081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 994199748 1250 994198498 994198501
    0x91704080a111917060108012a090b121618091d011e0b0a050901121a1602010608120f2d030402030c03011e0207030e030a051c0c02060304020603 64
    0x6804861103008100484400e01001642ca86503076104c0c00400305107000c1c0c0d441c41c6e0300c1344401801c941440707501d102294180300980b2092141440382107650301c0d152404440190711802c81da8160343c0030904c03450508059a08200c0100c41c00080000443c90a140040200184084060305008580a520712860341e0b04071001c008000703110344280b44044240240f003a0070000000110028400001c00c02e054104800c141c01407905030b528806554004003400034503428a080c42c1c150103182c2104035103198407404100140d020070f283c20361242c010303030f54494552044040021309503001c90307116100943c040e1012804101000c01030ba90041c1800030001e403204030389540c2100000c804a9155803090422946407803008000740110311650081e0308898003072042c0b80c1410f0880c0e041c0c00c1c40c01d2010007a0014140c00d00c0240e0010038106000e8034002170030040450000e801c2680100b812103060340240d10011020358191650304415115040c014410f00c11074011903521722004000a114180000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 994200998 1250 994199748 994199783
    0x10303050a21060e012d26060a0e0c060f041403101a011d0d060e15130506010b030f070c03030e0604030903051e0a020d02010e0d030201091704080a 65
    0x5442d859000d8000100340440d5943e1492814040c4080c040c0240003040c0f0350300c0700680d050f941d0902c880244220344840340c03980340c10900c890703580300740382c8920011341e900b05400d00d02030381080303020300608464000040c1340014803c01c920344076a000c1d0344d0303018220038800844c0604100301560112140714114002030302d81200004c3c1402000c1e900c042d6814a82503007500802c1c0e24100200d0050390a0b25024500304c0c00003490410a106058480c2e840b41c036030504400003540d00d40081207002070340011070301094590940c09818401c07c50310460702c0d02030101c4d4103049c0002005900c1c0100740004440b072642c00c281910200b104e000921150910040c2c40400017058425841a814601480140c45a904180c54020f04007400e5200584d203038800c0c0c1100f04a4440800034035490325401c1030041c44199025400c0c08034030070780d0074410703410320180340818416500c0d0880740d0b4403000c1c4079a00008107005a4030b8496140025821005400c00f0288418000700d0350005400804a40080c403182005003c01c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 994202248 1250 994200998 994201037
    0xf0f100c02130f0605040b1309150903030e0d090503071403070e01081c03060623090d050d031503080d05151906030f021213050a0602130303030c08010303050a 70
    0x20100250000d04039030b440015000b0503031202c0d0700c3c10910b00d001d200700380d030307480c204025542400c1001e03500580b0710b9015501f211030781c2d108580c528071502004103d111250f25040c106c0d80444030035000b00f501c52943d141c000342c00b4050200e4071100303410030647c00c50500010a40c0c0c1c0e405400f50359001803448100903c2c1c0c0e5020401c0000809a009506419685074000140c032140324088219444a001d070722103030010701900812017554203030390390076100c44060302070440341e9400440020b003207100411032150940ca4420742803201a00820003040c130344142100081c22600d2040c800358079528a028140f0000300c1180803a03c02c02124600483c0d5910740d14055040d642110401d01d1b400341810443c0c1c4c200000e1040b80200710385440d1402c0202d58040e2004106034814900c5414440c01c1500014102280202d45006200d020b1400c90b07045c49119612a4101e0380a2119075500c041060350030001c055042c0200300c8142c074180b4090710301e5403459601501502540903402e05000c000b15004c144241d21 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 994203498 1250 994202248 994202267
    0x11404060503131b211a042423070e010e060904060609061202030601140304031e0818011803050a051903060e07030c020c04021608030f1b0a020a02040203060414040506070e0f0f10 79
    0x148c03c02604034480745c054070004011081082206503440c4240d810f5000105404038800c500a40310200003950841c01100c1ca41810305030540c0c00602880444080d0311588540c03800380441e5150864000e0a150000d8681140034280403802030041080018a0341c0c04600c211401e41c0400599459846514080e40c442103000c0c002c107e4004091150008e4551001c003182c0103000760000d40840c5080030042c070f0700b038400c644000d811080001d03801c040020b20410040032036212a16005052514490000074080e00c1d030030300100000e80310a0280720030381754900c1e466084607482c14100800040709001079200c143c0b05180303921442d0301044421543c42c0c503410310401c040e80000c900da581d28040344c0e2844036a00540c0d003102000c0000d0300d00d800d40f8008400f220801410742d0001c08043c001942003002960004200c0390b0015240c0760f4021082030214040380c0150f00c0307180905010300d40040010302802401d000385110b800313605070603a0940c80ba01142441400c080e106020b2600708030b001624031461 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 994204748 1250 994203498 994203533
    0xa030f05091503150f0102010902010e0f0409050709050108010f0b030c09040c210c1d13170301090f140c0d0e01060302090403080106020c011404060503131b211a04 72
    0x1000020001071840040d01d03882000d6080b05d40300312009079440120308886481c4400bc0c0860100c201c60980744c0780c04002d840007001c005001103090542c03592481e0900b40603501840d80d80d0b80b80d00c01805104d00c00c0c01030910380c0d410600c0c10070600361001c0001e0760755901c028165000304a83e4010406000070604d01b403010700350a6856542d01e040340513014401c1b40200c3c40541d03200382401404035800080040d40d9071401c903034072400d07819a2074000000031007002210007100c1e1240300710f0400e00b10140490142d8000c1864900005008001d1400702c026260410040c0951942030030810000030031600940e405105106000124181c1070311402e401048035410103544070a48bc0308220415600c0390754281664515426178990710702c100019140c0d224075028074120000305000a01669205001441e4045860032840000111545482c00303440c25124040c1e0142420280a1101521800081c145440c0c165164119060980c940d6184041404507a06c0100600300c00305042c0a43c0b03400a618842 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 994205998 1250 994204748 994204789
    0x7050306040914151803041a0702030a0c1509081f0906140610031a01050c2e1107050c0904020a031b150c0b061009030b090705030606030a030f0509 65
    0x8031590300d0f0f07070707030b03054101091a44007a80000a58400300050300c0e4048041403100850515040a003144142d01c100d007050884103405201c18005a035040000c1e08501d806104a258514100841442c204491901d40020f0002c5100c040200c6038000039803402c1d4406040e000180482d03880c2450014202c2500094001400c081050000c0040303605214002e038021a12280d0180003807c05600351814508262806031180303202c85001e5001da8014080034070300a0940e0301e003440d041c10b030101554400c1d41c03030f4003178101e40900b583c5560b85e58403881601c00f8071501d025042c281c0e44c1c1d42e100d581d800083c0c0190f0003561104045411501c0c0c0703841d210065070344008442180d5200400002c910380891092500115112001c081d03413a0003003012010700c907000381c0b02e0000c7d41d4650040c00380724941d6030492020030215000010101e261158654050501030000c2d2801d00d1900e01014908000500381078482d0300144a40d0000a170040132003000302443e4209a0307240c417840c0c4c000484c3d1481e160140341030507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 994207248 1250 994205998 994206023
    0x3350c03091f0e0106090c0207061e0815030a12031a090c0703050f0313020312071109060609030d090305060f2505090d120305100b160204150314100212070503060409 73
    0x19106500156103076406542280c0741c07162b80c0e041c219102800b80c04041c40c1e42d55400c8d13144501030300c20080a54003292040e440501e5800e18004a40380000e0844151480703455908003040969040c0110b54015540490468001280c68002128070300e0140106200360400078194040602440c280c940e9174654540f081e450b86403040505084c110750039005c038840e0003488103024004c4012403c0e10941da40100b0307030304011481d02080c8901d207480603011302d41c031802c184002c82090781e04001050301000e50b946c40303051092440ca49249008030141c007034000003c0c0413040001d0b21007081c0f00b00e0f4000c1c04908221601c0c004203401611a44542036205800410811040d0140008000001d240c05482d0b6000c1002e6528450702140206041c0908900c0d840c0c100100882038401e0a50004d00600081c00001e005c208910170441c1e0804547c411a13189860351821000e440013030050030900b48101c2d00035403074142404401500d564006105105209021000c2394554407107512000f8a0303548038080070640c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 994208498 1250 994207248 994207259
    0x110f0a0b09011b02090f010305150106121e1107061505010816140d0501031211030d0c0212030f06010212070804030201140706110d0c050f070b0403350c03091f0e0106 73
    0x300d06c8240070913600d0f80b140c03005481c4500d40711041c240c121200c594448184000101c0007034080c152042207904007a184000016001d01c03544100300600d4200ca840300d681d0034052901c0029603c020f2903185903107000d042c00304201d98010140980c000940c2c0350044160f00d10301c00595081d01800f0300c8a403038640c04610150300590301d130300641c140ca001c2c1c0c4001c031000030701c0c8404480280c038001c40d092640c0c100380640d922102d52500801001c8001d070041d1000d80a000001e006240c00840d424034a88244905000c1d1650b01800b0b84901907101d82c594600c0d01400380c54459191080d8071000f030400043c00902888070108030292403800d5401305c010301900300032102c03101242d040b0818a0749114a04410040c82a0052007102d48420f64101d4687c1094115161510700f00802031064082c88140e6403111544074500c45170a6000c02d4126803200b02c04001c0a0450f0f20882c02891701c1200c00e03040051060a20000a00b44540132290502030300c80090091202d02400c002d94010f0150742c2030a501040c0e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 994209748 1250 994208498 994208521
    0x12070306020c100614010210050a140c040501090e13081e03040302010504050105100503060a0e031b0d02070603141303021006031103060a02030106170a090f110f0a0b09011b0209 78
    0x183c00780390140701660b242c100000103046115921030169000041d9044c07040281c1d082035620407111480090034001d80c100300d4100303003011200c406a608001a0502c1590382111111000d42481c42d00c002142c9400c03091a881440b04c440040c003982408503501001e84803494102490f104800c11701526030425103030290180c1003e4034102c0781942860005030214007030000c17410882d0750042c0101410348400780e02c2c50041501e0348100c44280400c102d001c119055480501250940180040068044008009080644640081080508014214840030300390180c850b0040c420314a9110080101d01e800c1e4504400c25440c1000c560620600000b444958091455038107030039010755445a403044a00380803031000340104004100c5140182101480c14020540d0100c94201e002643c20740700e458030200e01a144c0300880300020340d078030504200e0401c2050540d0841003a03c07440601e40c10001d105426019140c14981000030350600415000800342100c0321302600504440d81e1414004000030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 994210998 1250 994209748 994209763
    0x90d0308040b0a02090d1b0b0f0319110919050405130b010b031317090301020711040e070e01050f131802150a090b030618010b19020f0c12070306020c 66
    0x110b001c02141c2c000703095040d43d4001c54082d4803000705203000038203055803207003a0f42ca600c0c0b035500600c48102601240b0302c0101002400c001c0c5100c0d41c21512882e203030a00541042c00c450f4030720212414181e50801c05c0501006403510700100b12110b951460f8000c03881c42c011602c0760720841d409400d11083c00320354143c1900720381419000c0d01c10b03006a40c0c0c0302c41e500c000034817060302c40078084421803d9140100d003d0928100441c8101948203141580320030000b1b003660041c00b402c0c0d42c0e482410300c00309a80e250034031481506001c09400b528030145450241400408140f081030b00407246148000d00550b18009102221080300c03d0400c0407000c1000c04030401014614124000c4410f01101c2001c0e1804005694000d0841d07914290781c24281039003a401904090000c41e00502c00440340d1810101180161b4041c040c1c03200c1c400d40b00c2d10200482d000140690410360295042401412010000400c030740c1c000d070a081c3c2e01380c0d0013489403410340d51a0901030b500c0901301c031740b010851840c415004680d20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 994212248 1250 994210998 994211003
    0x30204020f120a1a010207031515031b05010e1c14071205030301060f0c0c05040c050d2a0c0b010e04030c050f0601060815031e071208040503100b0907050f090d030804 73
    0x1381068500c00c0016642c580b8140000345c182c1203c4c818829816480760030003c000240001e0000215540366a5066a100540d80341042000e00d40d00a1106507401600030034841000c4424080c0c0d01c80b00c41c062108051405030240c4808500888406d0b01c02081007034800900780031400408101c000e00f001a00c9400a00a2900240000c9000e5488078481c0e640c0c004030640007440401498941001c0000030300105105c1400d00a040c000c00d000384089100f6420072000d581c1d1812242142e0000880e20000300c102503c0501000781d00b684081495810381a054805d8100b0704c003600d4030345081c1170340e01c46581ca5000300544100002000d50650105440b81242d181f40c4a0b80b80342d0f20742041015054404140c2c054040c0c2c400a220403480c003180186004014901050310001074030307000784800c0d9140030101aa0300150006041000382410080107011104040d020003050006400080e14143c000d40204100178000c030703844103d002c440007100c00d041d00042409402101506d00a808500d04803000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 994213498 1250 994212248 994212281
    0x60a1415120709061403010207050d080a0908040e040c050618190b0406270b12041505070504081606090312140a03050105041a210c0301050106020f06100609030204020f120a 76
    0x5c01078074101402a5149c0941c01000352a0340c001d24801126480c40040041c6003203a03c8a914401084200e0010005840c03000030756440e511349400c2210486407194003090080c1000c0100c015100011980420264002c4461458000c520305c5000c3d100842c540040c0d4a00d90001400a0300e2500b141c0d40c03500074108121802c8a007202d503988003074031200c14861004080000c111040d003810dd103a070041d5005202d1041241000130b201008001c0307800c2103841501103840040c061100d04030070007240c03131440f202c24203c254a9082603001081c41c0081d00c0000d18000c2c4640b1402042801390b000c81e02516020540c1036291881031030001c014010030300c1203e028901c0d1540c040403041e4402d0002a00761005003410fa61200b910005c1d00b040c1d010006c40c101e442c059203038a00241e560a00541e8003d1880758000c051120030036a41600304203000c3d065411340c3c06090b43c10000349821405c030030100d0f070b01224010b8681804a850000c2c0740b2580d054040349003254010000c211000d58030007141940079040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 994214748 1250 994213498 994213529
    0x9010605030c030408091210050a11160201030b22091103010207032f0111130b03040b04020d03030209030f0619110403061a0a0f030203060a141512070906 68
    0x5035030522080c0c03081030220504000280c0410b040800900c100c140103403480c00107015003040c01d42803211100403160801d4507407082c41251703c1e550049410300344414010900c0d100c0820040700c220812020000e040c0350b29401016000e079540d40c440e035508400800f034444109445010740000300480340045408115485031200c46040510a6441c1a030341900d030001507403640414104110304c42110f0419401721403001614202c002e00130100c02900c2c03a0aa103485035105150002904030540004003048403d100700008565400d00050708180c055840c0b182e10062030508a010703200c3c8000c81ca801d407042803043c01c040e81c00021410701c5014130030710618aa21203004a28103480012144100443d000c2c841800840e89070741c4520031011703080405e8109503c4200200d5518005503004450401e00c5603800c00c11343c101400002c0c2e01494242c0b0411004802170240000d24074050039002401041115864135519408114a00100080125a0b2440d6104811000341c1150f0246400710064501c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 994215998 1250 994214748 994214759
    0x406050a090b011409012705130b0307050d030503070302030a1803020a03030c052b1d06160504050114090316120515040308040311190602070b090a020f1e040e0c0901 73
    0x10581c1c0c0e03210816503807070905205a03820f804401529404039103210090b07c0001070543d41d25804500d02160844021481c17076101740400d410500c2640c003060155800c002e400c40000e60003400c40e54091460304005840307442c0c401082e030080880107032a0240102c03400d65007040c1134001070550f070a644256024803102520440490311390240c4c9080411403200e07103081030051121614074101c190101d8100188001c024a01c00100c1820f1950310305440c1c00102c14404100301584455080d03000d81e007403070313443c051a100009022945801c0d4001da40b40d000308990405550501c400310b104031901c6440070030a0344400c05648118507088045070b59106e107140804ac2d000c81904883d2180c0d400d9101c00340d00360f445450513142400c560350414000d00800c0040a2031031664040c1c46042405410010385542c035602e402d4182c0b42d4040c200105940c0a40c2100005030b84a12803411044411b40e0728601702501e405060340803051001e04943d002d420900041c0c45d00318001590080082d084030000311030399845 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 994217248 1250 994215998 994216037
    0x1104090e0d14160318240305090c010806030c0405070e0f0d0506060609010908010c080402090106020c2b0203030d050a050f0c0d051008060711071502030412020406050a090b01 77
    0x42d0801c8440070801d000206000c6074107003400419902904110550050f002c00140001541d0b40015a04c0340001050300310380b421000004c0c0700100581400c01c101d0509104003550350050041d10741c1000001c800044240c0c8080c854030340e580c1000341c400d11580c00c08820250104880e41c41e41401071440415030038092070700b0120850781e650858083c00b21b64032100c0c14495160310404102d8144103072a00c0014802c0303001d01c80d6049031809995440c0d0142804d01c104074180b070041e8000000c41d48203441d5031100d0381d1001c8012102072124441c0c46400c038507010178120510b4641d0400796140c08007003803015003001c107030b00800d2103005040000c01aaa40b45540703610114015591704e541e02d4814031074101d400380198000c0c0d030800c034034810b03580c03a09a40301c840d189083c4003164500c0008810f01c00c3e03005100001c001c580041c080c401c2c10a290202201c0c0000c0d905e003d0f0b4407a1485c0c078241e07046003105549459125801400014140e41407042c2c0f1040c0440140c070021143c41e000030064121203946152a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 994218498 1250 994217248 994217267
    0x61801031503080403020402250f020405060a05031528050a140c0708031504060306020909150105120a020405100c11010512060904020103290f1008041202011104090e0d 74
    0xa900f0b01e04003401c58090000a4200c00f001002d011140c02c4040321001c84031400100080c0306012040c00144544188000d5400241c9114041d0040c19000e1149030340124600090243c1e12401d500b107a40d40c50309045811a150009900c0d0886058000c501c8100d540c210b28400c00d190003090060351071900151720901400c603920040900144000400544020300558100c02000e000b8007980103180b00080c200c03200d0341d1080750200c0d4006948220f5003400b0601642c0100004035500840e9002c400180031032142c00d01e8103414091034000140006c2681e0306031005001c1c042c1542001290416018121404011060700c07441405211000ca9612403c03c0314041001c1060310240703625040e0a00010040c041d104034145a11030350f12007000f144120000d00180701d0240d100c10f00b1082d10041c008003c000005807800f400c0c01c401c0400055070480b6003590000e81c00902950503060005040380100000485100c1c0010f00040c0014210a80c1c8c000c1c10550300040c040e11440015000240d824220 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 994219748 1250 994218498 994218503
    0x5090402030a08131d0c16030311031e06101b03110a12090801022b0b030a0b060a0611061609030b090a0c09020a0914011713111503130f02061801031503 67
    0x1810448600c03000380c48407001188230320905001c600944081180c8030250000c84010304814140700c01181660074044489030024402d440f4002000c03480680186269403603241c0101003c481c00d002c40805104040f0506064110400d480e85100249001805a0700246100740004d0410102107042d04042c801c940c152185601d901642402d801c1d664030a44007100e0001450a58441d805032117034405016188080d80300c0c07143e0304c84a2800030100201071840360088020803000c03260b240000d4000041054100794442603074000301c0b80c00c2030102c4452f422900010620700c590014002003040c0055072141c1c21740b00d003101445990304d650000040b8001c030300001c8005841c00300304120000d41401d0f003a02000d018500f12940080d5002042c152804c04d5030a521003070b540080722001d002e45032030306030f100c000304580710b8504910601d0698024000030300b08514050250540da8104480703000040641c2d58007070440384d150f6403cac0f098041d210380290031079808681024000b40140298580040a4aa = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 994220998 1250 994219748 994219771
    0xf0f140f0610140c0f010c09060503040f020d0c06120b0405130b0a020f04030c050f01051606050901020d0e030c070501020c06040314031e130e0c0405090402030a08131d 74
    0x255140100b00d002451540078078240b0000e0b400404554a02c5001070422201140c0140100004038031031a084504100c0e2010405c55403640c00c5c040700703900c0021030390415084401c02b105c03003200d400050507600310060006d1007078884003070000b5642d4020700c40d0303020010f40c6101080070000c408140405e69030110f4090117800ba8403140c1000003261030511540005004000500306949141c80e41004d0780b0a400603522031492040803c614a41054403aa8001c4203280c02420b0405002d650304c000e9902100082c41c594441c0c0c000343c84039100350f054520b01c80c80c165052015100000708180c50364440c5440c52814040c911012420b9400090403507003060700a003841346001c2c40c50326004910001114010002c0c081004189030800d8441c80b0040301d000c1c1002056030f1400c0d544010740c03c8442d56409003100d04070a608018249206200b0b45048a0003134a0184079a46c2c1c502c006070a20000300002014004041688c1c5c11001034402c01d901550099160a00f03500014007881c200c50304112000c11112 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 994222248 1250 994220998 994221001
    0x170418230a050a0906050c0702041a0d031d090403030b0f0a0e24030a060c1116030b0408070c0902031008030306030d030c26070f05091005090607060f0f140f 69
    0x100050b80020303405007100c140001da00b041d5a6485003070301e80a41d11640640000328080e02945031520030100a20260702c071000300002e9000101c0d1180d40d16010140610016210700d00c0036940c840d107280042030000704803141514141c5000780007442180c65031030242c0110380c154580c2c1d0130540121000e88002490801703880d9078004180c14034942c50040c8031030494130034370041000c0d1010041054410710625000c14086031040c8001c0000860b844038140700d60101654110003406100c402e0141c0c2c4d00720500142c260750380c1c240005588201c8000504c04c80c002800020041132540c0074501500840654203c140c0e0b90761070050fa030380001d541c0b07a58581c10042c600e200b40ca0090740070348681609030824801043c11a00d104078004102c450100d034101441c0c003040000342d444503032104041201d080450501c40e50f0008030301c01c1c00040d0794100600c1800a80518140c1e0b8590030786043c103070302c80e0062056100d0041c040780582072100350798241e00d003807030800001d04200b442031900c16544038540170803a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 994223498 1250 994222248 994222261
    0x803010f0306182004022106010f080412051b0a110a080a0804150c0203030c0a02043c150602070302041109030a03030c180e182817041823 61
    0x20316419600541d8446e60820840114110000e500081c13013009100600741880c203c40050f124005030b4154030204147d04040000140c0c004804a440040520300941c4414094200304600300104508070568440d00c044001040803050060311003090030b4410026080d9109013060384e407050100018036104c814042403002603003001c04011040380d10301d098042c4010a4000c00d04680c4410741460664004212800a5040c00d02a01002c480e81710306d00f003ca42a4a02013a000071900c00805003c0108005081145442900440c11100384504060364043d51010080e580320382a100c102c0c060707410428058178200c7c003882502d1403140040c0c044c2c0060912a0390480c0101640c1e44458103000303100100349040c0f1154044040a405010147c0255003005110321903039540095007070a190f40042d4240800c041d0140c212910340120402500101003289003640c4200c000c112520302031480801c00150740503e2811104043d40c400c0010840100305004a9021007041d541d002401518800441c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 994224748 1250 994223498 994223543
    0x62403020f060f0406050d1404031205070216090c1803030e090c1213061a100e0a050910050a0b04050102070e0a0f050a020301211e08070803010f030618 67
    0x821000030849858409003100d0f1105a4000360440300000740042005012102c00e4811004108400131011416140c0340d03030014000d40151614103510750319000800c2e1814000c016010200341200901103056480e03c821100800c0013050000c0090544e000d11001c101c04920008241c030b0b0140d6410000101420070301c610103001501c6550404020400403d110803614070043c01281c0120b502a011403140c10b21806499141666420b407006d041201102942c9020740c500b82c541c028145070441c410024005107100c0c40035031010350092030b050100f040d602c018002600684074200c07140300c4019140c20281e069802140a924007507804440180302a924614010380e022500210100d4000060b600810903a1010364018140075000300050240446031030b82000c030324942c0e8660799003a0b001c039150354540407103203800880402142d80c00304041c40509008c48500c2038200403c150380b0750790b405528410032001e10042c1c441510700090000440c5411807a440d1250300146200c051a044030030060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 994225998 1250 994224748 994224769
    0x703111014090d14010204120c06021b0f060c061e07050c030720040e0106230310052e05151c050c040801060e04020a0e040302031903062106240302 65
    0x1301c0c00010101e1402d0380302801d0000b040034100e030074241c80042e8000d180010401442e6000041950490303021200301c12100c51065415510031a00340c407080c110702012a14901c1102e020103094041c0d84200b040400c5841c0002160f42c07101d0804a01641c4d4003c0c04031118010404c0b0320f0f080d504108258008074920300300e13403030a0040303030a42c0c040d103020010001070441d0104900342c0c0310359456680401a4511591020784401c0001c000120016000c200098441454030a4a10066522008950300740d08400061400e041e0701d401c0101064101c48040310204401d05c00d0130701ca403440c800c40b6121020088156034251480354030782c6590103806070040c800352000030b10090b40440180400106031600340580c4008244000386051603003003d00600940840d141c011022440d010014000025070000894244070f150644c1218503000300c01c1c046000c0c084690103500028544c1455440c03451010001c055174610690040080503130007011000641c00b07442141e4034184514034104050301305020300c903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 994227248 1250 994225998 994226003
    0x20d0c05070513051902042d1a0c0601150903030e1206070f0806040b0105041806090504081b0105040302190501020c010e06010f14300703111014090d 66
    0x1908502c1d1554045040d004007051001c45080c0c0760414840f1039026414507490092151105601d02810181080f0768500360100110f080301c5001e020b01980c83d18030b000030703020707200110501d852004d008a507021550000d5000c00b01a000701e030000100702c0c01403407541d81003c4113070700c550100c0c52440e10142c83d0485100443e44d00300380600d15090301510144090352042d80180c440000d81c03850200020700720380c2c00400e4507015500e450003000e10780c2c1c1c0020551341111181c00b000400079642c00c5900004d003040e0b50010038500d00304001d010030400d120000d091451800041e5030624960280100d09035101510b029003d0303081030b4003040e0808081441008034a01407c005454061202c0c035903401c403001c084011360543c020100621540b0140d51036a8001c000c2c403c410454030300a800042c40c00302c80c1d020012805240405210710404204240a6036140701c03800351805c0ca940c90078082c0101c0300c07000300300388a2101c0440010000d4001e4510b542840e50001078541400c44900600800c0038461409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 994228498 1250 994227248 994227253
    0x3120e010e0a030f020c01090810180c030803040605060d020a053a1202060c04050d0c030506040302070303080c07110d06060e0c120a020901081504021333020d0c05 72
    0x41c003900200802180398064443d030b4881080d942220402800d1842c01d000113410401000c404104910703001842c811106200e4400240c50340040450741014025041c00520f590300005001061040640c040c62007103028510511269880034100a50454803a50017544903821106c00e203e142492403207030640b0104d000b504120401554032100200e41e030b44059500203000c0201400c01c016442100440e2401580000c218504041414000b00c0c01a4061603000d0560040c10100348a11811640000c5802c00300752407050405050082d15110240402d4001c64002800b240d03512040b0300488805903040500ca80d5819084010400b103110714150544040d52a2000415035403040e2203014001c03d40c1106056860aa1400b03100740150002e005080703a070f10500101c041740c0d8020001036805040340d50714004581c444000540280110384688800c101c0c09203000c40e0240c5560b090041282c0d60b04c601c0c15003030486494400c0c11032004008503005800c400d2030040c03107a001c1e40c240c80e01140304105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 994229748 1250 994228498 994228511
    0x702010c03030b043b06130f03200114070518040f09391505031b0c030d0609060b16050309060a0e1014160302070e0103060e07060203040303120e01 65
    0x811017100200300038200e031030b000541510100003290408010704140d1018110724507150a03c900c2c0301403008030142199088004a03020503220711200c4036a4143c0c010403a200b18101810305000306105c0c40c0710100075080f000030400480c0600e0590f100d0214041052501d11252414000138164105803071702e02ca40c88420741c900007100c00c04040c040300c60f81400508001b20001c0c07048805da5000d45d40c13000641540e041808084410284042580c11a06045a50f6119122035544041c403100300346180c0c0c04003042209440c80040003c0520900000c810310509031960100800c0303800d0307881100c0031007601300191181400303d1010400c041d070040050740d040092240104116902ca4103944001903900b503500e164900c0c000ca09825162168a0110000e4004d003096914600c02e640c00580311603072440100040602c200410b0001e005178810305d01d05560349180038030140541d4210004980540b5002080c45480001a0307130459402d40d0b0340c40c641301c036000803a00042c89075003000c400554076000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 994230998 1250 994229748 994229771
    0xa2d05011107020102070f03080a0c050f0a060b132304030c0506010f0e0915010b03100503070e0f31020f3309220b030d0915050702010c03030b04 64
    0x10541405041c0340c2482955100140b000904042c0c8903003094030800302d00c9001780301242219045d915025943d0a017100704c42c0142c2815440e1841c0300a0103511485000c0b051006c102c06034102600c02c00064662203102c40e10406880140d0f000b140380000c000490b82c0c042504031801c0c10009821074020304003400302942c140ca402c0d0500400760807003000c031281c400042051201040c40650302441e020b000d040b624071048034400da42c50040c03141060000011000c104000c3e010070f2440300600c0000d04807151190b44561603035208104441a05d1100d190300d0002d507104018406075004940c0100040c0e002c032441c02c0c200d80c508290a201032b41c202c00040b45540031501c0f9030342a484c40d845094410b0000e856503d000c2e9050880c0e2051540c0c06103014020f00324103890314030b00328030181c0710080d01c440f00000c40c08100000300b13090550650306200316160800d0450b0040400300036108100c111000744103810380b017500c3e9442660300c024001184c010154020a100340c0c40010304000042000c01d05403200b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 994232248 1250 994230998 994231001
    0x6140f27060f1914090906060f0c101d19060f0c020313050402040f091125060c0201061d04050709151d01060c15060504110909090a2d0501 61
    0x1207120007031850002d411410003842001035010f007815440c118210071000c3d00040881d0044400090140d000c810214510741d4420381602d0b50a60074a5030f0588451030701d1031141d0355140c200440e05c0d003145440300200d505c80da2926012500340143c00281040c1c40c121a5030400640700c40ca09a84c0b60750303500285c0c00c024025005110b82c5d5003140e07000f55150305100d079990520000f142d12407445544100410041401101184811602c0b03940000820882e4030b454081c50f40301d1210740a0301484d04d02030b80c002c0e10205d400c1d031070861030103000104600d000c081c0f800da0881d8202c0c0540c00003100c112940c0e074100c10018518690140c0311f5400c2d80e0a06a690313501d48180e5200c0c102905844507280780038004c1000000c1645410741990103004101d516091018000b505d0500001d0b00d4150201403400c6109034580000c0028034001e0310400007402d00c118005050303048515280d100f100d4400c04038011580c0061015070440c1c06c141e9a04256041e8045540016000a031072055171464045460114601b03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 994233498 1250 994232248 994232257
    0xc1a1005120a020409030c020f0102010e210702121f18060b0d050f060717150f03120a05071202060f06090a0905030c070f060906020d0f0c1b06140f2706 67
    0x252540c05841046104000004409c0040e00b41103a00d40207410204000000d00604007031441c5140c040340246406411002c1e1080240103500b00c44840c90039000e50074005401503104103407150319104001d1104140c011707900d600141c803500f40c40050100c004a8055800342c1003040000380035800e2440903603645420f015030508507505c960000c00c01c10134000d070410041e40c952030680e500c0340203d1600040210191560082441c040d20782c00b040301d000703a03d0800080500540b038074007203920740c281c14000825983c81042c0c02c07602c00501c106005020790000034900d004160720300c5007001d0366544034240020036030300130400103881d03894540b00d1000c44e000740010100c5e045402d0141c075600307040c070181144541c2c4a600c01c0c4100043d580d004c01040b81d001c00c6030780c102d103103e2070501480b0030071071406c64580c90300f8000544402d800381181c0c07c141e4003070288507048800f1504d507081e42030b05c0806440c0c03803409084070080c21450108200c04400400501440407115090b00c5200142511004501306411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 994234748 1250 994233498 994233503
    0x3030b0a24080606120103080313080d0203100e06090703050402040b0402160b0601090305120c1e030c061b04030803060315041a0105030a03091e05030d0c1a1005120a020409 76
    0x10204030642280d0350000b6065444002504c1c1c4510303240e0b840e018114101c40510003d8990760021011820f03000350b95040d40b00785034210107035585031000110080006e50050303a039900001075410700020a664050b08142c403551008100105a50f0740780c0c1c040d0090400144100c0e40a9604d078200302e0150741c1e51010384a01c0b0302e80c0c400c85240c00c201d880d0500d4210030203050b0382e0503c40e0313640c001c20000b01e0003d04c10f80c0016000720300940387d400320503d151804c0d4082419201c0301c40495107a00003000700001921403801c44008482440c1c0341c05100b03841c4d801c0c1c00042080305060400c414008900c002c0c004603004003001d0101c841664048040300180c040c240c900310780401082400700020501800b207940034120841c080c000c1c030700d4195005030200c0d03454407881001d580c1c40d031143c2c01c0d82c604910002c8000d2101a003540c003200c0c404540140041c40101e011112181c076500c0c000b05e000c0001e54198032800800c40082c000900b803204100000100340001031a40c231841807444016125405424417461 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 994235998 1250 994234748 994234799
    0x2040914160503190807060b040c26010501090b0c0321040210080112061a1315082a0307120f02041803080a0c020304080a12021c0c03030b0a 62
    0x40301c8a24411007200c165010902c664003004074840d50203204e07088401002c2d031006030981c0d221480d1078100050301c08034004c01d90180c0380c643c05440d41d40e0810307001542c4502c0040c22032035064451614046035182800303024001060001e080c41001b0750362004003c620701103000c403800c1c0291700c500d802c0045480b400100307400b02d00c00d0910085041100c800302c4d00451a00301501c20b503040810013010080400b44c040c2c481a00e4403005074006111000d00c1d142d45c4c1c00500a03907070100e00741045001500e078100002d450040c00300c00000d54008003140c00b200c452600703040e021101000c400d0200000072040d0809525003e803074000140f007000c010014000341d20444000613101d00c6401000201c580c64660750030310900104079140001e034000201603000300e541c00001080056050100e14500030754001c0c0d03102d845050221400e1000c1001140111200740c1e003102c490b02882d40d51106448200c2d085480461403844243d00064045e0300702c1402c0c20b00103024103040c0d99550a0300d000c40161a5980c28800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 994237248 1250 994235998 994236013
    0x30b061602100536030f0607050f0c011406010807090302090606071b1e060503040b19061806030b01050105073519031d07121a040c080609060f0c030402040914 70
    0x43c4c1c24040009040d8011805081204180e10a8030f4844100500800c00c00400056400c180690441a0f070004901e2200030082104c0b60310703401500c60704c00d46180d80410030754000600158400c4208500b900e60150091216481d541c09002540d007100c1c500301d5004400030542d642e60014244040e00601415100d0710811009218481e01e0504582013402001010010000400c00d40d940f1941c0050b03a010b4003540c40000f01b055500103000303541098080c00880c00e001b59000d405904000192070103040c4a4a003640e030f903001501d50744152440105880080280400801c54a100e022a40080454a003480c00c411824072101ea44c030480b8403103840541c281d1440c6c042ca81c5440b4049100e501c00c2e11520811406541890f81c8884a110380b020600b646c2000004021070311040382d11043c5180e400c0c0c902c600305840c1c00342500342030b4020004180305020025240380c04c005402d5005000d41d42c40129141c503090041c0c04540c0c0020000d13a00561139049803000201174132000701c1021403041c06420788 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 994238498 1250 994237248 994237327
    0x60406141b1b0f1c020c0105030118090c0b0405091e1603090515090d021b1012060807030b0705090108010504051521120c0606240d0903030b0616021005 67
    0x120509600034000c5600151b114516a6007004c21a81950344004100d01d040e181d40c12904007604007654000d002c040701090014558110f40701401c19110226500451903641d00ca208600c0c400c080c00d4944c860f030441c03010440307074084200032220700c00482c907012522408645409203022081c580318030342010f1200820511100a000780800140c3c0780c03010340212a46882c042000e0422500760a1103103081c074142420720307405441c1e10500070f6880b81e42480a25514120141c641882e0b100c2901c220f007450f07000849151150084803c82007050310382c2da4450742030009005c01050020a08010340e00340c00710401540c3e48200b036040280b05c003045000200004030182c0e5042c500d6429008440316414428ec99800401086850344a00c00780c4516403d42480002190300c5c122540003040f422500080c6030100940c107411680006000e80c4007403180d410101e007840003510462071100d16941103e12031000501d000f1004494040440c60301c01e04081e90400903020005282103400d19820345041a100c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 994239748 1250 994238498 994238533
    0x20726091f090e0702032a0606031504120309060212160c150b041b0c05120304021c0201050c07080f0610060f0e13060305060406141b1b0f 61
    0x107001684082403030001d0807a1020386900d600703000e040b104441c2840001ca20610030004d441c0350400c085281c140000c41282040710702842c00c0080e0701503001c1c800000704a07003400142d85c00c1c000210001c0e40481da03079a44544281d02d03015801c2504158039a00c0d8240400e41d00d002030300511508030340c81c2216040000050001c11401c02c0d451041c403400d000700c000850b1801c180240c0040302e030305005c038070301030b503000094005c0a400f00e142181d1102180b146038400d40c011030042c0caa6225004880c000c940d01c0383c100c84980003c40d8003d511040315100b90301011124a0f5003004203106041403030410596120041c1800101c0e00000081d9000480d592849030003000501e4010300c14400d9072038814101400207000540306030055003804440844034000d40c43d120380301c0010b52030400d01040415100e01c2c14503110842610156007041c03d1001811083c0b10307136202076002d980e070b00c005d046209205441d000450b800480111808518000030049003510a002c901e1451052002805122010021610 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 994240998 1250 994239748 994239769
    0x905040212251d0a0f03030c050709111c091410060e090c271e1b0405010e060c01020c0708060f0402010c0b04050f0f030a0909050c0702010302072609 66
    0x1074544402600c2e000078507070803a4805980300c050180d24080a0740e0729010601560309644031540404190f4000420301d903108903c0200903100c1d03001d542c0f40701d42d0382c0320080543d503403414460350600040101040003401c400404004040003400440c40c0c010b191142d60180c9011800403003950011519114648a54441e01014004d00e4204c00300c1400c003141c0d00396032080d0501e440750266002240000a01e803030145e840340041c407920842400c40c0740041d4200040c01c03540d501000da0401d03c90109a113191002071183c2e000305072080740c81c101841c210044a03910342504160b40c05c004104007a0040f01c1c0300b03000030506452441d005203503071171501c680d0340e142c098010803000c14209000140030042c0e90240d0700e09d80c1d4941149440c5890384450a2550a062407100320784218800c0c020100050308000c4090403070071106464801059940b020b07003c0980c1c038100c03101030b9152020401d0100540c00795000d08145c0c1d02802001c1100746030070b00b080a440255108080301400080707860b00480c40e10b40c0140307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 994242248 1250 994240998 994241041
    0x10608010b1002070f0b0c030d05070e01030b06190e130906151d070509040f05131104111209030c1f0f110d0905032b05090106120f030905040212 64
    0x2030030103600d04031015140d00c01d03500946c400601b0004a00b5902641002a50f021504a94003003040d401d26140113410051004c81d11400700b800c10b400e80c441840c00704c09484181144180c040c10f14294002d08489500118184907840260f40e45014020080b41c45038040c0380341710300c200040600441c44038448070341c2c0c16844000800ca4040101610140c2d80c1651904807a580c01c02d16121000b440014001d08803032228002d44900e882e0070072000c2484421184e0402d8003420042561402042c1840107540c0808407080a2590400006020300706032240552311910020907680ae1804117454107003042005694507402194080844500032032a111308091032150340010041d640c1c890708008107602035a000c044901d07a480c4847c006025080c8101c5043c20a082286e10ba101c10a8894101084d680751840d4a400e1800002441c01001441160b090358a410312680301180c5503917581d00d80a041020490400a203104000341c20f840b10f0001c0d180d007150750840400c02d80b6004d000700b065820304c04c252 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 994243498 1250 994242248 994242253
    0x1b070507170c0a0e0703090f050c0a0503010e0d0c0c0302090718080c0a0b0a0c0813031a0103051c090e0a09050c03150a0b1807020c09130206030f04050f010608010b1002 74
    0x160186588050a07441140d04112480205642d945019002403503070540c00340c12309400d04a074000f000300c0820780010000c001c0b50384c1c41d45507480d0006c1c10300320b07400c425502007207034010200c21050705d0160140c2d11286110b5898400303015100c3d800300c2c08290b015194400802c5010400c0c24800c01031060307650144c42c04200404040002100140c91103c81e442074038088400060141d0240703100310090070040d500864102e13650034545134448541811880309440104900109411080c80c0c80b480c1c504803030f000030050210740504030218160300f0750b06030100300703012294a00080440f582c1c11004c0c4035801d28080049c0c0300f11903080031400c0c40340100e8854440c3c0c0281c1c0e2200d56503041c0308140c6030010811b80d07000580d42c03040408909900c010403203040107a20a0030400182d01e600042581c403d200c155582c250903103400411151000210350025844001800012022003200b100e46030310a024004035540c0d011000181801c44005d41c101e8409a5194011340240c4d040c003072140c0704641e034035100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 994244604 1106 994243498 994243513
    0x708070e0d05010e06150a05060711130e1c0302070312020d09050303040b22030c06020f04051f0311040803091309171e030108060402091b07050717 65
    0x502140001b03103400102c085003001c00c5034504441014040303c0c10035240f81c1e13511804200c07001c0029082401046804614000750050030b0113064618060900c108111040c8501d407502c88054205045c010401d03440001d070b0081c540054941c84010046e190145c54003040d000d0201d1880c0070300144004420b200c00e1045241c6075074002ca00b42d0a40c011206a0642c200e00d155058940203008900c000c6540b00c0420156002030401c000501e18140c542521000020b000002c002401e00410b12652a850280368041c800c04d030001402c9400c0a0030103142a5031160303648145100d05000756241036102d1000e03040c1340c010021056008940e5220200b00d101207042e50b801c00190642d00020b000a0340c0346546410341103d041c0d95600d0090119a5a50f4091015406001e45200d004200c80140116440c815102426100e0301c0f0701d02520032107280105141036042183c0c1c02ca0481d410008 = true := by decide +kernel

theorem cover : BRFrame.Cov 994064748 994244604 := by
  have h0 := BRFrame.cov_init 994064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 994064748 ≤ n) (h2 : n < 994244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
