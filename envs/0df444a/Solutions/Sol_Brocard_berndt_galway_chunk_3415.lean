-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3415
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:36:09.593994+00:00
-- url     : https://prove2.me/submissions/adbd48bc-025a-4d64-898a-9d9cea675190

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 614028776 ≤ n < 614208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 614030026 1250 614028776 614028781
    0x305070e01081e0603030d181e030804060f0230062421090601170a0c1a0c0d0e040b0103180201140f072d0b010e060301060f03030f03060509060f040203 67
    0x103031562041240420496050020500d01c200c40c40318002361042c0030b403803010004100fa4120745400c1424150040c0452020008140850455400b041e01d044c0c24110052800040c40c110148000ca4100080c100311080d00d072102c50308103000c1a558001c0c1040d10612140c400c1c0c0001d0246116103281e801226003404620714115031200c01400c2e43c03e44400aa11700c86090280c3c00d15202c1d0000d002d012240306514907191022040000e01640c600e030443e9204022600780407010382c4000905000c2001d01105001140a00710140180b0102d070710540c0714441903810010610098031807400885050510b48030f0013084503030602e95481d580b1642440d180c2d040034035810b071041444c013030858501340030b00000c2005010000d510100f01018080da0014406c2c141c60407619968184d26528001d0500c041a401048022910049580c00c100c0040000c034009413110401840003545600580010380200720007200c0540600c0f81d14040c02c01502d40e8803051400802103449060701940b40c60095900100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 614031276 1250 614030026 614030029
    0x4061e14040b0904111f0f0804020406030b010e041202210a0201110f0408060a02030907120816060b040b030c0f1003020c0609010203071b0c210507060305070e01081e06 74
    0x30000d00b448000301040c81605003401c2501c1485ca007146154000d90041185045048403080354450a24031a07440480e121407a28049411034406041207820a841e80404000200e040341d01c1340c007808920302000005d140606001a100012449039000d54105c0415401d610041050014010305130a20042d650080c1c140101d0041c06891072425200ca00070a00504407405400203100f2261030900310307140c0ea25110b4a0408038407080c0c0c3c2c40a0150300c0710104208074204103074281031140c0241c1d503213428951401030300d040e2106000c000f10392881d6100803040309483c00d40b08940c2d40a5003078000b0314030100c0300408640310500303a40840340b1a0303900305d071044210b0b80301350119042c60030150141d036180d05018040324040d40041e52117102103080582003c03641c44000e082500d504c1d4210101a607120700d4805025406920501000c03203003480c3c512060042003040141c8801040b007640e0005903450300400040401c5a404501410080c0840c20f00c500c850240416046403120800351000326100d050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 614032526 1250 614031276 614031281
    0x206071407080c04150e06090408070812010518040b0a0203150604031202060c030c0328090f031209030905040b01170c1c0c0813020a170c04061e1404 66
    0x600c00c0c0c81541004284003101245040b40c401007980c09104016200380020f040c05003a0040013600743d24100001c440e864141d50700d94110b4020b2500a140844035100c906880d8440c100b109413000b151030040090f8200b108020a079488220070112907410142d4900c01e40c1a4058424480b0320703004004035044840b6200e90485901c4001d054070f54890703503880c15003540798400c114000580245000110400e2070041200e01c5500c1c601052451965828200446036000c174a41d900c03170064010203c09240308a109a100302805040c014554503040c0c60001e010003d40d1400341544c90400c028440001d4105540c501610b81c100c0e0085003104021004890031011003d0100800784207206010910500710000c141240d024130041249601076504403041c0e6040d242c0002c006a586400190342c8a0718180080d0f02c503200901215555aa034035507010341c260035083e404400d80280d00c64101520305031013880d008199440740c0c0401c0d02c51400310090914010311400c003201c0032401310065960360f281d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 614033776 1250 614032526 614032553
    0xd0b180f0f0c0a0807200a050c0103090507030f030e04090503070b07030216030819140a200301180609060b0c16030b010b030a061e0815090c0609030712050c0102160b07020607 77
    0x1c3c8644455040b9541040d507e00c1d5040080e16507024040e1200019403003800340c5481c86420100500300c1d00e06d90b5403020105425503805504120b03808003110003035603940c0110880705005100071078031856103080010362868003502440c1403510400c101740603510584885642540c050030000384996414200501020780a1100342003640740c10060105001d1f10000c20303000740030fa81c2c3d00b084207003d00c1c0c481c09003a208070342c00e041030214240f00400042801401f0345d001d0704a45400803e0440c0d6460718941500c0e07258010345030905000c20740a00d881800c0201e22003070605041c0103481180707580c0312002588818010b0200401000000500842d8903803c02d600804d1441d0390284100201210300c4091507d9001e00d00701e50141c1e2402005010b61200401d0007080b020b8040c1c0191445a001c00030300b948600740e00c81c1c050190316000501aa600c440d5108814054400340080101d9540020700340101d011401e850341042000a00151000d1015207002c140d064542e41c0e0750304a9070501400303d010700e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 614035026 1250 614033776 614033807
    0x40305060f092119030f0905031c18061107140705100507050c22090c0e1303020d0f03020c0d090806010807050d0204020d0b180f0f0c0a0807 62
    0x180d9041c0025081d90080040c030031400b007810340d40700911031115800c0f41012614480b00480c1d05201100507803101c081001c10042e501c1c18000307400c0f1380690007481501d003181c42c10f641541005c00d1507284d406404001d8071400826280401041410340007540300f0134079108010b0405543e0700b5075a075210000c0750480b03003440d800500d94004000c0c10010180e8400c1540120b500800107141421616409841650802640080a0300100401c2024840320b0406d800714040844c9805800c003210320550f10400c3e9070540200c03174040780d9900300502c8201802014100c4440040b2024403480425404035040001e05906d18001200c4107410100320041c1c05415070f2140d160242c02c000e0041540c0041280085a540c0d4068481ca41e91f1122002d4860100303110b25a0850806824240140351a07401044d0a44481c0c400240109100c404aa5016500d524082980300c0381c03801d220307858544110b440d5011108410300b0b42d09140620b841e6485020b0501d0840921a03034001107120240580c0600c500b6205 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 614036276 1250 614035026 614035033
    0xc01030c02280f060e010c0e1e010e040903050306041a18100b0408030c010b120706050d14010b0714030304020d02011803080d090c0f030305041211061908060301090b060f06040305 79
    0x469060400003851030402e0145c0d01e42c6489a240c01c014026100c0d5400d03000c004000451070031000350041181c808070540d550411006016140c181c1c0d0f110321600e00402e0082e44e540362a40b07011000d01044840c060681d00c80300240e580280a50b0740d86101c0e0001800304008008d4a9031142407500241d290950081080c54601240c041000480040601951111400203000050850b014082c2954000c0d00410041c0c00440c0d05005c0d05000b00000c20700c03401c902e40006603690108000001c004d00a0b040070042440014210084c4800040e51101c0c98000304040c524505040e40020840000180000d06110201080041c0d000c2002002c01c02983c00c0060680c0d0354007407111000040c45048011581c01041c21000b094000040102c802943d60640755030381380509000c41c0d200d8803000e4180803106c1101d0030698030102d403204005040200300380070f0a60800c0c1516540909408001045c040c02070385400c000802158212804903044402a542d001c1c02880d00808607125200d2600060301c18030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 614037526 1250 614036276 614036303
    0xc1503020d111228020c0c0612010303140a0801050409030c1524030b060904050709110301170f0c13090501290a060203030606280206090c01030c0228 66
    0x40c600c40042071114018000302100c3d6580c001c40303c01c44e00d420611044005000d903003103480040c02c1d0f4020f0511103180c01c02c072510020207000061190748001d19504038003c0240c010020940c002c0799400203061402800b900301480c100c0020907401052051912a030340f2941004180342c00760441010040d0090030151a20440c5000d603805002c3c1905a42c18010b007001c025981d48134010040c2e000da0380c0c050b0040c052902d07a807080180078440a041522103005548001402d00d1141c41020701102032424079a84a626140030062100c2004002c1091900200006500c0311008030350810010400c0f95040104c0d0302105844005190041d001000d5600c1d0010b035000b0030710840340c1c0b1001400038924100c81901c10005000e2984171030b201e124056031040c40803817610b00e080d0700a02a40c69005030b0008682c0061000c0d5000041c2d84040312000d601300310240a0440340600c4120005202820103110404404200031742d03450340000c0807003e8030550402455900c0c10152001103050b0058104001d20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 614038776 1250 614037526 614037551
    0x3030f01060801060c05060f15030a030c0605250c05100606090906050102010c0c140111030103030c02101d040f020415050a030c03050106052d0a030e0c0307030c1503020d 75
    0x40800c0c09a000840c2d0250000500584070321043d581c415807040c06885662203658514200d0300028101b9203502111001d4005151000c000566032140603a0b06c2c1640e198890501c0c0c4103c5070b000c0d003201c15010080d48900381c00406080124860002840c1a9003180c106040250500f440200040070241c109040000d009904c81205800c1d03820005040003031030b5498005a00b250287e04152000c1940443c0c0701d4041400c401c0c5070582c5108034400071640ba16a00003454a66000f60002c0700400c228015140a43c20f0a5804c0003882d48681031016812002c810142800b0529403840303413055441d103220000280e201e8043c0d8004011300c951540b40c080320200081d18540000c0c1c42c44000030315010354801c805100b80a0181210404d032602d91501c0400845c010303204040d00c462030b920b03080790040041003001c5d020003044501c40036603000611258600c1b445040048805065100764080401400070800d030040c1d54007180d603420810b48004a441c5d005a0190103014881d90950f840d00344004270341c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 614040026 1250 614038776 614038801
    0x81605100b030709021e16050604062c06130203010e01061706070810120218100f080f0309121e07060909091a0601121a09070804120e0a0302030303 65
    0x10010407030aa03070045131200d654908a014101d2164411600095a040032101d84002000e0140e0741864483c3e284000b41c6855140903420758040380c1d80c6542e0108241c810b07001c0780640f81c0003000d400c4161140c050505a141d91004042c14026440c60803a040008559007544403e6212092100a10540780d41721056281d51003c41109201c0d40241c0c0001550140310710352203841041c0c20b2210f44140782c204143e203003c0b08000c040880c0c00c02c01044000194029516a0341c1c41030040498190100d030801401c400c44070011b5200c24003540c08414103001110010058540ca0441070782c08000005040c40d80382c6c41d12000320703240241a80c2000f00b032440e0030343c08038100c000d4400c2170b141c5400096803030f00381d007088034191403026014600250704410070380c1cad20088441e08103405140c203ea801400c0a040300c1100e0785000380d0b9040c800580241512400d000d04601d90142c01414085818501526031034000d20340d506060041014901c1070300c505584420040c005150081c0880340c4070700d84150304074039 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 614041276 1250 614040026 614040041
    0x60b0f0d0b0703180506070521131106070b0f040c0f080c010f081302040e07081e0c040203071403091203191a03030403110406080a05070609090b0d08160510 69
    0xf90511202c0301140105005210b110b0b50b110000380f000341d1718070750122501e030000355008000300150b040041c41d162075106528001c80440823505150b65891a00744501250380300301502616080c0501000708801d48416903200481c60382c003100c00d41d550304c1c003085074038196044900c0141d0b1a410218076403c000400421041c02a01d0b41c07503040d881c0f8503040c3c0c2c04030403ca40c1466000040b08071007006081c550041a0a0360440d411a10890780300c0b40503030b0504180488455800008280428a0410411019072254015030b030461a5042580d80201010212a07503690007450001c00300b803a981d008c0011040e07807a862102c240d142d04150245404c68440c411905074400d00f408800a07c00c409000c040c0d0320700100034005d62406213941e40c3c00c3c070007210f03014038194030a030385400001d000102480300d01421441039020b0000641003150161030784610340c00c0004414944441d000c850344030500b1590b00c0641207104541c442d41845c42038401300d02ca290000b0b1841c003c83d00c02c0c2e155002144c00648 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 614042526 1250 614041276 614041291
    0xf0504051501050406031e02042d05011a04150509030d0806040506091512071503021909080d11011515020f030f090f011202030f1006020f0a060b0f0d0b 67
    0x24656640d4400300005e403030013070002411030b24040c003002c450459020002a242c0748064404603424034840241c00c09207030680c0101e00c846d024106000d545c400d5a104240c0985028140740c0795140e9440181900f038060b5004207019400d50304140241c0d03a01400c1038074503005000701181c09180140000405040c01558824080c904040101d40c01303141032603ca0784100002307160821040224001c00c03403100c4e000d05240c035590042172004034000d884080241141002c646015949400310390740802c015506a07428803c0001c4224244039400021540f800c0481c0c00c1e2500491440c2d08503410f038010030414140017464658820002880904001c2c401851131191702695580003860160036120302c1040551186098200010940c0740380010207081c0304101850302403140c589940350703d002c0340d04c20345018940490751810003151844070002e44010b402644007800c1d600c0980c4540d103a9400484600420968a0701d07800c4507261520304184083c41001010020f0b0b0509600700f10048280540300c04c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 614043776 1250 614042526 614042563
    0x6020d020a0e031c120b03011d210a140d09030207061115010b0c01060b0d090203061803120a0f091b120206190e10261603050402040f050405 62
    0x30b918000c034190030140c41c1210016035000c0301d01c4080b9100092030010028465841c48130901907102441a907039448417684024040d07189041200303180400c1d403c400c420086000311900100c401180036103c00e42543d081940c02c170100c8800b00c4086018003841101d8151400c0c5d103031024540e0024003c01220356588503200b021400d08496500d805080703880215202d4014010400b0300454002044030345401c0c2c4c000540540c84840119050344580b040a210b0b90701d0f2030445d81985000e000081d0031011141c84000703201e041c81c81c1c4c0b80d1640141c0e044010300b001443d0005000e02415044460078100c041d40400c9034001da46483c11090b40100c0101415525100c00442c3c402c40382c0c0141c40380700790010122401e00136400102104a4240c00e9442d08001800300303049110703100c5000d04400d504080d00c070540d0455203031041c0c000c040c003136000c0c0c513900e8401c0388280169004503480d00b1507215801d24011030700b80d0707503800800e007c1e00360840440d4040d1710700800c02081c000040b9040c1d46160449000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 614045026 1250 614043776 614043797
    0x14070f0206060a0501051c05070809010b010f08060d06200d0b0a031e03050f130312140313050a0c0311120c01021f0902130b120712110d06020d020a 65
    0x12aa00e90007101d007643c001080c40020b204542c0540041c02d1603180001d140b10030704001c14000d600341c803c00d035030030f2004c1800c40d0140b118501007030142042015007860b00b5007144c0403031000145000c0c000b5102c18000c1c4035621440d024001070781c112080f14040d0a00c8140d501001c0340305850f880e4442403a0264441c82d1948481c124688020050103c03034000f100b5104040c1c41400d81c1d0503001d03001e081181448400c00004001030307403410152162100e25580b81c0201813440c14000b0400340b803110b403e002c001903000036103052104035084e00e821000d0603420341c1c6003003501d282051070005040e80c0034140d0640014004204a903000d00200782003402c0e2400c402c106016a4041c0d075a40c4015050307070250f04540640440b118044035006280e43c0082c0c800b0494080c1034001c00e100906498034044140d4071068211402d0400600012090300318800074a00b40d0715111443c0d04600d450500208205100c0c104240e4a580e03102105a9094002c00c0441d5200d600302c0d111802903001a014001041a4035113 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 614046276 1250 614045026 614045057
    0x170c0a060807110615010315170703030f030b131e18032a11012a12091223191703010b1c0e100f0b040b0109030b0c0d1407 54
    0x10f0341405202428405e107003140c2c50304015005007a100c212511407100501002a000d94441c2d0769450881520f80501450381c00d508004105240341c40c991400c3c10301341070302c20540d500c4440414112404c0780c900042c003104c00825115490500584444403542410102d080300e0f440c454100c181d4a11a840b90a0a52026542e1811700e221090034a00381071003203d10038010500d0000051174220051420000d810003440d214040c444146030780182c030b10803c0c000c00d020007405800401d00c0740c80c030f4100304010610300500c0782e8038284100d030000c000131070366018070020000d501d01a00c00200e0340403d4420414000712070b440700300c40c0100c00369003004d2041243c0d03c07055800d0003103c1c165007800704c0052810208021280902c0000340301c914180341e503922902e00c6240d00b070043c103403000900e14000c079001d480100304101ba0b547d501d046600c0380349410300da820f05a800120342c100f100d511460800840da1a030b031006c0d026000304048070318054207021140c8010040403030030754411020b40d102c41c460b034141d502 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 614047526 1250 614046276 614046283
    0x108060603010b01020a0b0604110c01140703060b0a031e02070503120105010f080a0519050c09012a15090803040303090203060702160b0702040905120a020d140301170c0a06080711 79
    0x207820fa015800115a6070041045201e10541c025005030001c14045008203a4000c0d40e8080c07000e55605941d143c50741c001e81d80724401001e0300458646000d01103503040210001d068859000200c081c540c0d1000c072641039180c0103160300040c4c02038401c1151280c050f824031b0358a960003003a10207864000c0c100003060719230048064001c80c00d1650340d02c030050364030310300401d009040c090200c28402141c51848800d405150141d0b910545801240e02c0d1a809104000350030146130000d1415068070010103c1c20070094840c02c40d025541101c0c0c850340540c2c0342d0403800010004814040c042d0381000040005154058000c580054030a03811030303c85640700001240c0b104c0080c0c03a03081c4080443c0d017081181c8070f0080c0180c075205000600000c5c00f10317502e5840c149480f0032041c4642d00c5800210f072030341409070180b1409020a1003401e0081c6103541102901960b88014060140804059640340c520b0500c100100c1306100d6000e4801c409050b101c8401800c0c41600300d42d1a00000e0340141c07940d03180740011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 614048776 1250 614047526 614047541
    0x6090503120f030a0504150515031207020d03031515020d0e0607050c0625140f06040c0b030703090501021303020405010f061704110a06050717030105031b13090308010806060301 78
    0x60b0300241180c940365403881c064400940160380e40c140c0145100c01d08519072180c2070050840580b41c0c03125070803000605050112181001c05020000e100003409a291440c94a40103a81841c000070448408104401d813039490350440c2201e1070311080e9080c01240c0000305100000c9035074482da407240d41150208135052144100007401030300005004480303402e00c000034001401c1d10030200d00798109009d071800700b540b0a00300143c1d2036515180d105014800280f0040d03070480d007000701030b02642c81c042d101c0d11040c0400d4030815000000000014049502c6607000b40342c41035000b0000e55803141c4c55804a166501c040c00142c0c451032901d000066104001c64009007142c80700d03201c000024100701100460108000c20544850960044a040035550340024001900481c0c990a4880130103051515640c4040301d03020030040420801400319580000318128500c0c84a0449001d441e098030100750302500e81701e03081400d00e040903c4d0100709508100f0f4241618854400c851040e138460040600f61641e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 614050026 1250 614048776 614048797
    0x901080102180d0f0f151404350c070504051806041407090e0102030a060b1905070c0803031314010b220f0e0f0f030f1c02070f0f120206010503072d0609050312 70
    0x4054200b80741986031200f48804980155850501141e141c1c01207050781c000c0740c00c60ac1540001c1d0061003149401c1c4165600426501d4100e4403240d041d280d51a0707504c4010704060124034000b080514040000c1158101410541e1414007030303101c010a03168040d4109a50f0614902c0c140300707020500c0000c44065036064a44165124080c02038160140c90580c407059003550140959100410344401c104015800307a100d88089080708541820004803003240c1d052881050307414038075107a10a1340d90036021503100c1c04003524a41c1c10111003440f070009000341030b0031044860526000ca0810b8001082465100203400181c070b40c50307410000016128400c00c90000010001130140741004030034200b48450088860134010301d082002e4403070070720780305481c51b0480d102100c11000508020000b80012251517090008090550510002a848455a0050001d018558801c25003074374540603003080c015400b180803440e09600c80000620000450103018003034481d81d9503d0350b0b001d10713182c11504803582 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 614051276 1250 614050026 614050043
    0x209041e03052109061803070206040312020712021e03100515032103011208041701021c02070c0b0c0102040905091c080106020c0d030c1e020901080102180d0f0f151404 74
    0x6d0303d00100c1244095042620414072040c03001e0001602c07100c0041000d9030107030700c1c103c01c21005118001d00d440d0642e0013001001c2c0840c1c1c0c49030010389505008815844015100c400c0d032001c403001203464580301c240d4483c180c41c03c0c0005c1c44590f001080920351110001d9013964407907903841e00300c0e044008404c8581d030707a42d04040004002c4540490081008a885010620f2a00d56550021403440071400c00018003a50b0004200b5055418131100f101040d60a85003175050a8454071000703102400c900c51844000c00002c0c1100c0014400c0d411240608141541004581003000c2c440d6074440001102580212810110711402401002e2040c12140c07a50700405c4076001d00010300c0118095a0b00413800c1c071011140718000190700400340c10070070100a0940d9440c0320540100407002c0b0043c2c0c48103690340d10402c414a0854034085040c41440020307135a880884015240c80004411070003000b0b080458202d46a808000340e4580409105819902c10300100941408260450805482c0100b2141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 614052526 1250 614051276 614051281
    0xf030324030b1312091410050304061e1103090613022206090c0507030e0a05010219020d1a040c08070f1806090f09140115030209041e0305210906 64
    0x1540c0e005841d80c05001040342d03080c0445603598840b103071541c85003201c000c41e000b02c901b0b004601005403480784082c42141c1d8003c41c2d002444002e005071001400c0034207910b80311030540940d410110240c116051041c1000c014845095040040c0b5400554225516004100200341403000c070503040e9022580040c01003121240b25441c42c0081180700c1d0040281d144c0711100000e51510610a020441c401ca49490b517403404d061038001c0c09200c50f0007542d4412941440c061109980c00961036004c40e490b4201070030000c5031400000c1c14004592030042c8414003071428104074120340690300780600e00c60716851041c00c0c0c5440400b03031603104a000b1200d20700001d00c01013040845d000c0c400070100100321030005059440e50910300a807903200f40301e090a107460744e410078108016069070511750210070300200810305004548142320009440301901c81c001d00c501103400e00407121034070641e02805640e402c44011a0b498081d0843d0480003140083c01a140044484c01c0302d501c200ea4862011400500180c1d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 614053776 1250 614052526 614052533
    0x80d0b191d130606090b010219031e050403020303030c130806060310020d090203063d060c0203070902030708011403030c0c1207030209040c0f0512070506090f09040f03032403 77
    0x1490549072035048980c010106030141309610142803c2c44011480f030f840c45001900c1c0140e6803100d23545440a8060f4034002c030394041804501480101c03503c3e0810703849440200d40f103018980010f5450300002040c00104501e0500070803810711400c10380120180d45424454440208558039a00758120303100d100351611441d8010401740c00b020900084d90611074000c00c4c5072000450300c00c0200b14494402c004d0420400811061340303c0e1900c034418a00c1c000b00c488408030354180c071416007400130a038862021940c0c1449000c002d84142d040854507850503007401440e102e020310549440003c0000c03100b0680c2070120460301040a0710008000c810980303c10300001d40c5c440c4041070101e000b10380010005039120309855011301c0c094400031001504141010f100325000750300c0a441803c0421414001c000b0128220044800403902d83d83c0369003c1101040f07090100801543c4e2281418041104000e4484000c01c8a58040d0384c0800a184940b042c000e07080244c280340c210704001042082001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 614055026 1250 614053776 614053829
    0x1815010303142109460f0605070e03190209091507020307020f0a050f0f040e070605070510060f03060507120203042108060a0515043c0518090a080d0b19 67
    0x3241c1484041c0f45c44600d403034030b4844000035400f104942280d1100180714409d40d2202c003881540c0c0b000c034040d0a4990380b04030700d00c0181d1304200700207000e074801d14000390784c0e000c050111580401c00d40b00002498a405030700251603a0142c241244240206501d80420782400b4440206441001c0c054510b001000c00070408604810f41c1c03220f41c000d45460900105070360522091004003116124907494800c10b1070020f00301400008000d540c1d51a10304100040003540c0500c1c403c40f6084600024903132900c407005c44005c0003002161200c0d40c000001c0c88200724044000703484806000e09400d107207024081e4115003261040d180c5e943c1c8600d1008003031060f8540a601090524040c03c580391a113a910140d0020040c29a00105070448584c502e15618640301c06103c1c81d8003000d450410103540c20303c0002102490100c4144904808220006813191410001c0c0020b0300e40050801c0c1d103074207999000c0340141030381d45002400340c8407950300303401002d0200c51f1140c00e03504098401800e4100c0c3c940405030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 614056276 1250 614055026 614055133
    0xe0105090a0b03121201050405161b0b070903031e0f050c0a0c0303030e12190c020f0904080408010b09040f0f0206070c09051815010303142109 63
    0x16180e41c2d082c088030b595010400001690a981c0c2c005071a0640c030700c50000c054038168001406241000c0070400300116048035030302401407900b000f2400c031031074240010644000400003000341940300f0500155a800030a60421248170b90b8a02c003c2c02c580c02200061155980000408590820222901c1c0e030300034000f43c01c100a03650111007081c51151250b8100b40c0c5c01da40240c1c08030f03903213181140800714140205207562643c040d41d01e00d8501400e00c6404010142c0000900b0461000280c5085685501c0c0307450304014010003400040c107041c14180701a500038498140740b90f18140e079142007414075004503841107030407034144001c02c0b100c1c2d1615400e0104099080b41d102008001070400150011013110140042c4d160014452070920404070403503549040e034801c19480359448102980c0c1902c1c00906482d410306d40140d80c0d01010716651400c0c02510014240f00c41c104162481c1403000c070303603010300c185620400c403480e0f0140e0301e0380720851010084214417600200f207031800d0400485c211020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 614057526 1250 614056276 614056291
    0x314041d25020c06091215060a0806010b09062b0e01150302060405040e0c15070308060108060f1323060f0907080c1c0c020607090b04080703032001090507060206010f0e010509 77
    0x15030a1b0580e880e0780d82800442e541101c070150703c160500800d810051000406030103a43c0c02003200f5410000a03000314080e00180340d01c40d00000404107550026035810055503e0b005c01e44c501000d003200d603040d010304100c00342d61690398a451a0745843c400e8440c550030407250060b000e03c0c50301d0304000c103101c0a4201e03030110450f944101c41d122111601c40c85d08500043c203039415110789a003603d01d0004c0020743c015020504025002003440290b90f40c0c01448840307140100d52480c885418107031130790050030f0701103080d90005145056140c004c0c220303030750740314800c000456031001013010b01c0040010142040d1800400036240c031001500c502540c0c40289500c594680065145050520307003182034440c1010307810010b030055400c1c00900c80e00003245d800541502810741d42004d081501d440d949041c80e00c40a420425011004801101c040c00a034032500d0200c8001c1c0090001810b200e90f9071310991203404010310030034000090071351010f1107000950b0780d60044c803e0b659180108100150780c0c09000c22 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 614058776 1250 614057526 614057539
    0x8060a0f080607020d030225212102030405063409061808030d180f06050601270905091501080106050307050114070314041d25020c0609 60
    0x850a0340810049400070440c900c0108450b107071064009082c482c1010180007454010311a100402c0ba5400d1980c0129454010074050350120b424a401c900808041d51b40a58070030031182409958084940801c0640304520400131103400080d0343c08074803007200d028080342c00000100307820440075072104000100200c08141c00c60103241d00f9503244404201301e10007041082408200d00742e003100180c9100745245a4044400349845140ca031a8418120070112a070380e1500c4c00d5800302028040f50880c00d401c18041284d000c0c0d2498440e0051200f6180240400e0350341c100310604400c02020540003500844280c94014909070064001d0000a40402024015580c880c000100700407103480c02408c50f00004030301240740105040c00c0c10000d07005981040f46804440311402d051074110340686074540f41c211181c00f20700c0030090041c0619023100c010852803e26a29100804d800e4071401200c0d400904907403000c0c107482c408040342d000c1c0b01c40313070260300898418041403520300b006e043d9900c03018240 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 614060026 1250 614058776 614058779
    0xa1104050d0201300911030a0c151808010207060b030607120b060c032a030c0604080d060b0d060513020c10111308072117070813090903110c010f08060a 67
    0x203080f00185401c01181c0c0190b03540c174491003030207900000705655102c10750141003001c103981c4a03070a9441040c06080c0108500300010300c14188a0030008901d0850440d0640b0350a444203030080c040d43c8000000d403009802c0c10040061441c010450600078001a02d038500401162410030000c3e0500398002a4081014001e60342a80000c1c4014044d00340290f24428208107444609103c0c6110f150242c2c0e01544140700700305104e08001007058019400c1060203482d9107100f400140601001c1d00520f00214000c203003192907200540101d4143c034004c60f45100d0a01c0c00042034401c83c0515074820180d684040d02d0700b06c05074132a5120445810315840a5490142a000484803a42c2d040e40500056031051108003d0301c030450883c0140c82068101000c041215600e0700328813a10000100300c558200090382004106182040301c00c0c00b03440301c118860040d6100001c0b030003488070000079004103440d40d14003005018003013012a00001f058640d0b415079010604107d4880c9801400030b038021450000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 614061276 1250 614060026 614060087
    0x50627090106200c1012060815040b07140d0c0905060c030d0608010209010e0910030209040312180506130804240f050304050703080d150602060a1104050d0201 70
    0xc4160107007607152101074840079000d60300f0803122506020038015400580c611101541c46550b145a0001d10345040e20050440001c82c400818566100c0482482803607440440c2594401409116034000c100390121584d6035141a00e2819400c83d908074484005c00c0422958603c907800401d4480b0356250178020a91154003050341039122083d91083c5900110b002a40e600803400b0f000c0240c103081c07009504013003203000060a4000740144082c480c010010024000c4c00810015000454004200e002281081c1c1006041e6101c4080100001ca040c00ca1507220746141607841081d15a01c2802002590780d0b856074848406100e1a007110740b00000c020000741c0f2102252020152041c2d00b40f158403001d0359640180100105010490070720400303200708400300b0000308100003200d40002446548101b032000c180002d1444002c508050003070310301d0101e4407590000710980302d0000020b08001e1407840f460140190302544c031031168054103a41840d001540f20b070030300a5524844c1030100000d0512500b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 614062526 1250 614061276 614061289
    0x91e030e0111100905010e010f0204030c090507020f010903030b010305070c0b0c180a080102040503150f0106050d020f0c06090f010915020a170405031c0908031602100606080a0f0204050627 83
    0x4d50345c6030344441055260140a100d80b070310b031407502041145000c0c91550742841603070144c4140031420741c2d210001510035000348500404158100004c01c00311821f8a001b40003802008255030020b89000300181106006811103000a0b0704083c83ea88540e0700c02405850380da00541031180800e0203240110095120b592028001c1c0181c0c1c000980c9641c28202030516200c0d02845000c0c600307818006014081050203046810355100c4c0c030b0629a104000e0b500c41010348941030024605260018408800600225210780200e4601081c1c0700c0302c0101908690a0340d02d00400500181c1c0a0126510901506e5004001e508441c1c1051050054044070507210b0b021b0495060750b90307801c0018015986400c65226100101207108208116100c6881328a02030100a00c3c842c4085903038022074101e0790080143e00c060100280041c00650f84581c0028120b94003507800c44000e038104180c51281d1802402034030251103006c1c06660400c440051210040c005003041e0f1901540401c045510341d40307403030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 614063776 1250 614062526 614062541
    0xb0a170a05010f0203010501120905071224050c0d0522080409050702011401091a030f0a030e18060907030e070b0910020a0c060509060405030f01091e030e011110 71
    0x490150801400605250b82520300002c140304070a0300c100014001c9a801030407984056050510000b0003606c90305d049450503a040d0085203200304c0e16140302080182c40720307450f802c9054648804110312203041c480010740d001910b44544000f0140a44018100c0b281d011503846020b4120140410750700c11400f02c0c501407a00d0041d21045030002c0c1c00e111198607405100d80041083c4020089480c900141024850741030144440d03940c0c807001141400100f61103140c0d0492401401d4070303500da01134080541d440074400001c501080706c0b402ca401d06882d21110003104030074000e205084035580c1d0002c01c070081d0001400a800d07d40d42d84210882840c2c1084501e020b8109160820b54030b940400c10402c0e003081d05c0d203092085500c0741c02c01034009041c20203860200d94481c20484e403180050340c009101c82c01250030030380e0184240c1e412003c1288054100c030820703600031002c1c00c0300781e10803154004220031a80790180104e44100d0004a055100b043c1500c0854401826039401b60402d400420544814 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 614065026 1250 614063776 614063819
    0x5091504030f03051e0702180604020705120904110909010b0a0c050102071a0105190e0c1e030402010e030d0e0d3f110c120109050a0b01150e01120b0a 66
    0x414450f42c04004010300340a09a42c8200381404c00ca1b103540000c0c00c0c808a1051452480301c0080465072680b0b80390107540105910100b034a07003208030700018600a41186c0c01044c40f890078000b1a681c41500b0204803109410040e240054982c01c4c008086216806000f0400811603c00c0104000c101c0a1000d44a0350b88120000201100c000011844565040c1c010394402c15505d294a0395036a240600b0000311008030281c0d40d40c3e9a94a100c01d129801a5815881d0042c2c0d020343c1c40407100e18a4008600c070ba0f2003621400e002410701030a16a607480d1150900000c1a0554a2800c0074940341c50007100382440342c1010288070482180a5035150702d05a000c1b0701000c4102502142030b4034440300c2000141251400b9103038940c0484401e5a14954204440c0c0566a440740541d0003000039041540c0c1180c00000711194001e032442c01c1c28600209102d0340111a420300400d14032170344243c030040503811050b984c0c000004041080c02c1c0c020700b101011103a011809250000d0760151401001c40c00054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 614066276 1250 614065026 614065037
    0x130e03130305100c08070206040b1512060603160b0a0c061b03050a1d120f1306020706030c021204032009130209090f150a0e010911010f030c05091504030f03 69
    0x40c8850343d40280c9036a0414135045c400607108110b03929500040311075005400005d5261039844200380542d9250685840a0304032400c0c0ca4190340c44030303000420600800c8250100e4503e040c41d4010040030701c055001d41c07111040200511104280700da00d001c0e075031a004820014113050a000203c044561200000700820b449404009403034160380b140b20b83d20000031810042602d01003110a485040e012400b4042130743c0030500a40304a00b410036070b6001c0900c61103c0380510b460b10390181d03580d0303450700c039040010741071401d90711100d0302c0031075040030b0085802d05940c2000c0c115900c006081350100b1120565210220040b04160b4034100414081c1440310400102c11681c1c2c0140240d402d80101020007950010286c41d40500c000280030010b01d9000ea56140540c4400400001421001001d6001e0790b0170b000c03004c0d090000f02d80c407680c074450090f01c4500740c691a051041d8140c9405142d4403001c10028818098142001b065a084800383c07100701750325182e1240c0d510801480c0408040e4001030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 614067526 1250 614066276 614066293
    0x2010209041803170402030616030207060204081606090b0405010809010f0f0606092727050309121c0e01140d0e070501020f0c0618270114130e03130305 67
    0x6030044c1610756000b10701c0801c1c00451a003600881d5a40b0005004503010385504c00085290310720a41c1540c00160f884042590303519951800c1596a0f00c80a601c42c042c440d5021001444c1c0b4001c0702a142100c2600b440e150803e841c00c0300540c2c0404006042508075501c505c0b01e110b105040303200307600c1c0c03480a001c00010164244400207020140940215003c6480001030b00d040303500003002c00c014815222004211003146814202c0881c0d50400d200400d0f60654081038108200800a000740c510140d83d00310544511050096072103a0780684c480460307a541207202036491190742c1c0c20001c82c0d4181411949400440610722107540047d6601c6001581c0b51115512110140050f1000749000d01c0100560722015000300e803180000c0c80e10a00ca41c1c0e0000d81e4400310050000c0240b58660300500303220a0f070f140289516a600c1420207800110240d280010540d6000304902da81072200c041c282c034010354a410040001480880c42c680b10501c4148009041104540518000356200d003000d042c075035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 614068776 1250 614067526 614067533
    0x230f16090c0504050409030c1209050301050f040f030c210206010f0b03091504020f210c1230040b180904031707120e0a11090402030d0f020102090418 66
    0x5051034120a00107414914010640c03540001514141d4000715000180c1d1a400d1405807201c80c1c40801c001d003999031604250548581044a070801c95000303a0003030080e541c4d60103071100d0360101290003c010151105000700070910540302c0301c1c0c00500c6a00d807401003250742c958242003a84460000f2006a112000521440700d5400b1201c0c010110210380e40e0650405440301508c60310650389640041c41072800003020341d136500c4038681a61002030001000305254007111010004011050132081c421504000c1c070034107010320102c4c4200f100138003401c1c90144030078159042c003080307690819503012000503445c5a450031400801c010800c0101d41640c075640d01210302104081048420310480d0b8034410000800c1c0c110f103078900b000340280c8030a10643e40f0100240c1e520540f11805020702450300044041d08000007400c05009401040304030022441c401c1040004402110021b40581002c9440c50764a405000b503021404014000507080c980b0803008102201c103800e04250f024100100000d052 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 614070026 1250 614068776 614068813
    0x1501090b0a08070b04060f14160b0f0114010e01051207020309090108190f03050d0908031801020f0901110f0a1505060f0307030b1306020403060e0607050c0604230f 72
    0x1004100040d1503ca032030020300840c140114400c0c82e003800307a00704646107020701c211203084d01c417000c0035160354a42139803200101c1003036004281200d0041c6590045204c1071440103000e4121076175000794540707120903880111052044012481d040c00002c3c40b80703c007140e807403104840c030402c40751f8002c1d40c50300100000c1080800040e8000d980a40007a45c54040140c0b423484841c0c043c07608403030014081c0040c3c0c50125458840c80c01c0c150603251804158074100700490b802903014a40c0051406104020340750707000e080b885002d000300d08007a000c005040955001e00100050110b100c41980c07411a280c403402810801103a404a0303031072084100914103030545101d0359410001c00e89040812010620201c0e583e4000d0303001c0030f03202e00c07040000110040544c140c402c42e842d602c501300b551103587e24a0b084026004038040a0707903a014100000d80000d2241007036400781c503488002006103480d26240d030040407010000c041c1e40c1d00003903402a103c29034104601c0042c40c03084002080701d448a00a031405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 614071276 1250 614070026 614070029
    0x2181203070b250e120114040210030605280e28052a04050301020a03020403120e1e0f040e0d0306210b13020a06020d031413141501090b0a 61
    0xe05107408103840010b00040c080c00303400c1d10281030451010404e0400101201a41c01c6600c41079820002038070244881510080e0145100f40c51041d10400c9001040e03085c2c4106009a9030000c0c0c10038001c10500e22403480c40034501000b20000c406c0283c81d10b03007030107a010701103440600740840607500c006500c0407030f900302088007000002000319041c51240600c8040d8004081c0700005034125080c0d0391248001c00705d80040078002d00840d44e54a5800d00500030750402d210664060081d05811781da2180120410b8140e0782000f42443d1900400e0300d260f0500d00c002c600b4007500210b0b01c44185c0710580f00c3c2d11941c030511079840020000e80340c294000400341c5055800c000e80d01d800101654105950071070090701c000343d01140f0389100380d0300d4040001d02d00c000caa0020794440d212440014800d80c0104030640c000701380365818000c100c882c2c40e40d1207040c64107a407003265180b41800715201103030680303413500c401914120944000011008148502c40420703000740401a69851020041e880c10000010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 614072526 1250 614071276 614071291
    0x60e0d020a050d1b0f0e010308210108071d070503160203070c24032703020c0325060224130c0803130509060303070215040e0406020d0b04090506060402181203070b 72
    0x40205003421005203110340c0602c4020001800862402c2c2b031806403803100078000b0840c04c902d4040e5070750f8020441d40c1d1900340c070480d150390010030700c103000400000700814400c03030151701c800e032468880c0340903018801c103c094035000710300051040d880083c40700301d0100002c02d080c0075070300d01401c011000d004100d0340200c2c226052621344281014042800742c5600d104841000c00d000300441d40d0f06080e400d00d500300d070320141d06004200007030700c64035454130700f03024900d10108401c0080c90321000305070383c0c0b094140c083d40d230000c40c0307210140c640320703804a421507211006039501940d4032074a6440514100103908100c00d035820201e00304103040b041c542540f00920089074952020b06203000031a8503403007200c5010b405950001c010031040101d0784201c800410700109603444928043c10004029001007502100550400300c000032140b505009400d02c01d40c120010b01b000d601e454040000a5020305480c10b039070040b400c080100c40c1e5505800d01c0d08251202e02450380e500701841c0082c081c40d0000d03e2034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 614073776 1250 614072526 614072549
    0x203070b1f050d031d040b090f07030501050d24060b0703020a0501111e0d110d0e0c090126010b060c010e06070507050303040b0408070c08010b0f040204060e0d020a050d1b 75
    0x1940413980c00b481c201d203a0f0040d5002d2130082c294003004107020b0001070440c0c3e80c01440f1201030018200c000340083c0e01c141d40e03d580410480c0d0300c0708100300400000a00c00b070000018403901751a560616807807109410116040010129038420300c041598024000c1540540c1060348107005000080c05902503512001c3c01082c9041031901e1254072000300495a000c80c0f04001c100f400d120180c5610050404044200d9542c61b40b48040543c0d0240c40c8400c2200304a01031080e500741542400004581601c042c400050702031001910040c40b00034000845400310342d00c41d52035201c2a101c490041940c6000c080022501480303810085103400d4000d0801c40800408009200102c1c10100503241c200f680301e58001007540b11411322011030b004490010f07102c3c071404800020a074205500000c2c1e60703c819038409900906400c1080101e0043d44101c80100c1c520341043ca180b840d040610014461004203903c82064650303011403280d00e038a0310f00b2070300078210001c140c020070604030400b4000c000448a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 614075026 1250 614073776 614073799
    0x103150b0414062416060906050c25111314011d0f0105030c130b04050a090b07021621050303040309061404180f09050a030906201b010203070b1f05 65
    0x720a07036881000c8040860b42043c24917401001a41d401000079250044800d000b90305044040340c80320707804103840c414074410244030425803520f800110341e840358201e005003d2801085c070900004010310382c50316005c1c079074411003000c03800040c10045001c0c0280d90b4080249412042d44800c0320b10000e802e54910502e0803004102079a00015102142241a1081d000c004003041c07645014007640382c02c26034800d00b0802002000076042d0f0090980c1e5010342d41e41c82c81c0d0b480f041000d0341c6800d039801c010b40000c240e44e601401156000b4419208190118500040c040d242c0d0b01c945041d900161011000107000e0001080600e034420301c0511a00e2000303035180d14003444c20000e206400c00c04d400840c00aa1208000786050413954010b19501e42c01030140d540b80d40d5589402418800c0600964000c14004100c01c0e10035900020742903802c042d1000280f4206421407030803511040b80244080c110311081248030700240350902090b003c0c0843d0004021092a0014a008010010f80043c0e001e906000361 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 614076276 1250 614075026 614075089
    0x30a0e07081e030415050a0905010309200109120605040b0108070b0301090b06090d031101050c0c0606060f0c0706030c140a020c0d030318230a02090103150b041406 72
    0x18203180082d0040300c1c0001d40c4820030003103802c5000e20307406020b08403014900016010740000003007099050550710780503101c2d2a20010b42c210740399183c000d82195506440540c800c40340401d1080f2070380050414200301650f40c81001c2c02070407842c20807290507854500b80010808400d030303914054442180030345080e605042c82c0c0c0074140414411540ea144e1a6484280140c8812080b00c2404002420051040c001c5090103020b141c00302e40e005620350300e06800030300e020240000341d032240407000c009058982c0f0340b882041090b40010300d11401c03400d0100038106084c00e04010840c0108030a8031701241ca00c0c00040080c1941941e904420003c42c0c0030040e98103042c1d40030400208864045501c0e43c95804241011001030084600d9010a4031080300820b050008014a95241003c49840c5034110038542416540311111040c000390801884001403000401c80207401405240c5040001140081600080d040e83c0d070540010000131000d109200380d6040001c1421100c44156410f0751501400d101e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 614077526 1250 614076276 614076283
    0x30b09010c08220b010611060114010903032319020d05091c030221270a030b0c0f0406030903110d1d01021f021903180308061212030a0e0708 62
    0xb01800d42210581100c001c1c45030700319000c0c2080f540c000410700550b68489034003030300c07552018107056070034071a100c0006050707508214090594a4180d4135a0a40307403441e5170503180012810311090780c1540000c0103e10001e00c03840070384415a0316082c810701c06044460080d0425129400340310402408200c0b01590381c0399110ba03403a14600400700007911080c542001c0f824003403c40c1d0945420f1491410704403808041001a0015021008008550140f90b581c02e410109142c04000e811001603242003001c60b0b170102c0420307030045000428925101c45800342d03030b803a944160026008656103140301410705a10443c4d8070607040d1000010500d4441d42500546000e181c208102d02c0388010148030002c591080c02492403207000d0740c1d9000d0700c11054003a030700b000e50805e2441b80c0d02417801c003080300042031007805200a084000810743c40c001049841c00c03503100b40000c001541080445d0b50003010b00e1820008107040ca809902c005450707061800c01042070f100902c0c900f410b1540054000c0c891100d012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 614078776 1250 614077526 614077531
    0x90c0a0b03060f042405030708210d0204060513060e1f0201020c0105160e030727021c0c12090503040905040212060f01050405010e161202130609030b09010c08 70
    0x50300a41d881c0e59039030000414103800200c80603006820840c0806815842c0094026000c8400710401007041d2500c040c15510a0280b1400850b54464203161402244091040780f400c41c02c11403491a01821000100603a401076206c2d600144c4001000032031540b1b411884400340140b490b20700c00313120811000075421002d034a1000080c00060f40312484081c000d60403100d80f41042e10091007186040070554441090341c0b001c20000c034880c0c0882c2882403a0114680094a1308441d06002d04401e04010301c00d800e0342d842503290b01950030464a22100082080b030041094504000305811840076002071000c110200503010441c14502c5071070000e01c2c00301c1a14140c0d074219a00007a80e64482c00011880c4840c040c20440e2030083d8400d11088216180b04a4141e8078142c0d010312150340d031500e50200c185c1e0101c0f01041c0b58440380b948442268860071501221800c0780c8005404c05600034041014100e5030b600c4000800c410210420821640140083d803007500840200500000701c0400760820100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 614080026 1250 614078776 614078789
    0x30c02040c091805090d080907030609020307031a06190501020307081e04030f0b0601020604020d020108071e03240806071808031809090a170a02070923090c0a 70
    0x5889089458500c1984400c00070f00740c001c44001503c50300c56901009150a49040086014150310700310128040c191090140c1e131240c0061103400d10b10b4031004010401c200089030700d401540000004192101d1001030001d100550301c071001d0a01e0303020060001c10300c0c40c80141d0802086010005a84c011055030038aa4000c7e0304d04c4c2e07035403245500710f9000300005c40e8034006000e4041000b00510a8103407540960610130401581075403100401aa0b5889003103c000b548a00004440001940709400190700542281401019a00c1c03102e5200354500e2491050700000369100c000010700e19540480061a418006a03000104c0c11301043ca9101c5c940100600c0511407007031390f45003041041aa0401c018115201520745400c21600c01d505806000e0089910480001001c190341c120042042e09400345c0c0451024818000d481c0906481d400200328002503015104000030981c0d40c0e806a400f0f0a10009401c404900e0315402c0d01d0107001d80500740440b0b07640f0a0003503181076100c80b040300d403d42e01c0d03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 614081276 1250 614080026 614080031
    0x3040209040c080105040b15010c080406030f3e040807031205090a0806090c0105180402030601051606020403200307050f01091a0301030b0106110c040f0216030c21050315030c03160e0601030603030c0204 89
    0x5a05a014000d850c90303080345142c08522030710780807a8400c1c0c44160520a206110105168041041740030200d024500400089804c01c4100300005130201e005801741c0720306410001d0034030b0b01c41400100c881c00d09034081d01c00c60b0450000c0000b050b00502031905005001d0030802c2c02c2c01002801d21864000e1000801c0c05691700002242d0180c3c0940d0640e907400d0f0030903030b400200c641c003490580c0c0a900f2500c8121180c1201c18130194641c2058003108540400c00f0b8000c0149500e08010400071854840680c0e042c4587c4060100d02c0b8542c01b18082c40d10b18101c84010780d69451450b141c0d20001b416032118080022880040415440c040b80030015007101f10b0700400c5440028008600a11400840701c81ca038410f082c102003011b8000c842a20028003130401c03440b08420403120401c1e050a59902c0d100041c0c002c0002a5080054080801c0415000703011203400130002804280b4114242010403114544e0740c8040040360103c1d541c056000000786824040c843c03079940c000e0040700010400038403440c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 614082526 1250 614081276 614081291
    0x70305090d1a04080a0320070209180d02060114010e0108131a091c030b060a030e10020c10060510140a030b06160c05040203040803040209040c080105040b15010c08040603 75
    0x2500300d01800d0196010000781c0b50f03042034078211a50ba40580020004a42032880d41c4211004000341540d920f008400860302d00034140c0c3c2000381c031200081042d15503810309601845240d004010404400c5180e400a0a4039418000d040c2c05c070040b01d428503810400801903444032070740e01400d1513801ca08110361911070110285048512654003000c1c2404030031034442009030105000800403c110040710b010a903440c42514100e003940c03142c0300d00540048080101a16451080d44040c1c1115180e806580f04007000d1141d802c2680c0c803040c40e601491344441d424480c004218800c400040408852200040207a141c01900a100304070311401d11400108070101030740d002c2d4001188d0040c004180303540d101c40d003c00c1955009490a0240d0701c03502104800305031405d0034400c990181d504828201c0c119070300c5600f000075110004000301d864a000000c0012804424058640540d11508206265140541c1e0028825052070310301410400d040e141e040c003184582c012207068450b50314001c035815 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 614083776 1250 614082526 614082533
    0xa051c030b192105010c0c15060608070c0212060c0912010c0c060f090c030b010609090212040615032f180703020a0201090b09030c060105060304080a350105010f05070305090d 77
    0xf07100b40c600241c007035400d1410611549070300020014025220780e0701d496036402c6c01c09150b800c44140e4000c85002c100307050013060246000e0040d00d4035541c802080c240f42d1103100c0d01d18504048081d590b042c0880400f08240c10380d80740070585409500b8095000300a28402104001c080049486000c2c084c1a07841122910482080d08490a8280c01400600c103d41e038918206403034040c24442d001c00500070b9007001c0b4800d18140221780c02e00c041250181103a8076151201801013005450040180041047c00000101908032a4185000b02090407607071100a045114a0380009001c0c0e43c4541604018002190700050480c0d030803000074a801030300d4214040d0264014042c1c035a015000d4600c040802c4224240000140b0707080540405482041e40e076402880814002604c000384070100c10700110090500c50a0300d81d8075030b017400180f581a001c00940c400d0410f401c0300d42160944031503d005010179604042081c1010081c1d203007640c54206540c41c02026406000e1016104c0d22964841c80b0030f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 614085026 1250 614083776 614083829
    0x1f0e0f0d030b0d06051008060c0405090408031e1f06030203190905190f020f010806010219210f021b0618040209030111180d03090303050c0a051c030b19 67
    0x10b164412000c01c600d08086c41c1c5d004c0440c0c07841c81021428482d60001503501c21000d4151004c80b84003030700002094680340d13103807070a42e0002854a021588040302c015200c40300c004240c1c4c050043c469481c00c031091406a0310404480b130760402401e00d4010824000c518840e03118a4405da022184001a0840303146881d6003443c0c000c4803580d00c02c0008080302424004200c7c0780383d180303038400c4405101700c0c9070400040d1050942110344070301680203100b0030400640e0818481c46c1c3c96205401d156400c00a1b4000b580080000100001c00120300c8090042626010400611421000018141e003006404005001c520906480728190407169000c00801e032101e0301560401c00006000f406003084510940000da00502c11400e2035011280d10280745041a500c00c450b00d9401d80e035022403090035604d050b541d075440420400382c07074410450b1140c003088091001d50340d10341d000721006140700410580201a1184008a50300c83d03081c03a25565000d2198220781422030f030340410b40c034001c00380b0f07000f0380c2e1003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 614086276 1250 614085026 614085049
    0xc020c0901090c090906050d02060c0712120f030509030d0209060702060d05060307090b1c05210a020d031b0c0302030d050108100c0216050111070302031f0e0f0d030b 73
    0x20858880c400100d540c601c00c3e0040141034000341c0e140780711240e46110040586d41d082c03003150740011841c48400c016045c0340c001450103441c01011141281e03a92060740c1c0b8002ca9242e41a5050600e6641c80003080394001c0c0580b2561808cc50240201d08154501544a1050a281c403402c19800208400d540d1112004c1d140e00680080801e5100c80718140e01902511040313514130300c00c0c0100000494218803900c46c208502c04060650710b207140411041382100c21800d030003503401c0c1c0314185e9920108078034100c0301c803c02c480081c180b60b1112035045029161800d119212002d150a03d0403420280207030205410199140b464203844603a80d508088e41180300340149200c50508040c00400c0b20600024401c40e40300e141c80c401c0007941d07140c1c08102c1c0c03101e0103800e0102903045582c104203c00c2d0720844c8180340c050000c2060b1400b00d5501d900007450000500c0614074050703403201590f480c10929219900b21074036840302410002944404840d1036040100307003041890341c1c8290349156034988415103070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 614087526 1250 614086276 614086279
    0x18010f060e0105030118080702010c02040b041a0909070e0606030c09130603020118211e05250308040b0c07030c17060a15030308130c06170c040605030a0c020c 70
    0x405403a691801c50100090103101d00039801d003240350041d0802070895041e25a00a803e250030102d40d6801100c49606112085e030b0b00503202e0700c8010381666107204d00b10740c011240740248a85400c42090010f041c000909454180d00403103410001c031140c15000c554030120032100c8603070b0381e83c460021403194060600c41c9900804021030407203441c02d5039071000090307034000d803550f003080f0214180c950004680d82c0908101c9540049030390000d07005040401181c00e1140b4900601c801350726070f900c0d4001440d814151030551243c0000f50485c110040000c000350303105414402c0490454440201c14850f521a40348003440001c2c485402d00c4040c00140c0113154003107400e00d060703903880c0f102c5941010b0f913445d503121a002d2640441c510140034810016402d4601485c5988140b4545007951404002041500342001d441d0104c00007502000080300074140c10f13200c005100b0351035109010000e10042209910341010041804501c1d00502a681c1c03000440c070780443e80e1100c05404030308000c103940320079 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 614088776 1250 614087526 614087531
    0x100e0c0d0b040204150f02281101090503030319110306030d23030103140d08250203071a090601150e040c120f0522151d0d0203040302040e03030f18010f 67
    0x200c0350354030000340d50080c800c590889048650041c1490103c05800c8070084030000c46510308c4c40001c00d0080321860301f607014100b03411031a60b60b001103030650340121907030300c98581091804100d007100f61094481c0458820085415803401201003992004028101c3c1c0a10000c405841e04482c400070022404e034000c421305a48a50752864130001400310f01c82404824060031707a543d0000d511500c5510320882d10520300301d0032107003100c0c5010000302e90441d100045000c20020140422202030b800d00d603c54a0301c0c4003005518000400038101401038000001c1c0200c40c02c2d02d003903003e6010b115450078881c22180002e01c40312002c0113440000c0e52215000140d0b0802684802108641c0e20261180f01c1d0385900361030340c401e01e29400c541740c040a200245040140407a100554065501c403426500d5418a6560034405000c2e51034030300302400003000c0c0107034070000c0c1c1481142024080c41c0031101559000f5030441c01e002c2c0a001c42650000c0603004ca1030104c041d004108402500034000d44040741404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 614090026 1250 614088776 614088809
    0x606010818030c0a0b070e03100509010b1f1e141c180c08030a05040b0901090315020c0c0609030c040c02120a0c210503180c04020c06100e0c0d0b040204 67
    0x2058035500344003410b5842d09030700b10004406d0b0b8020f24212510410007405410005000f80c10341008200251110006640e980c11456a58a4104800c068241103141e280c50030b161074500241700c0b04a03200840c01c0032118540da510140d82050150000c0460800450349032911104403048600c45007021950603401d020310614410411220b200005000e400703c2054a038950803d903039203102e22001600000c2040108010078001d00000c0d04111005142921942d503407907d40c107442d01c1c000b00d03100c081968002a1143d04590410801d101e205050b900541005240000a038503040e081030300038019a290a9690100c610900034104400c0c3c1508a9039100c0d08040c3c802401600702c1c40040303928040c140103001841c5204c41000402c10010781e07072a461552080d01c4249501460341c2800c2d00c501c1550851b542c40d644038006021241e1441e0001c14062409000424011240d51b00030707140034050308140301d41d105151040b2596020740e006d000c00c03258001c1c8042002407103554031901c03140400015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 614091276 1250 614090026 614090047
    0x180b040507051201170c0f040e030301081501120c0605030907030c150e180414030705060705030601230412020d020405010b12390d0c1e0e03060601081803 68
    0x10301000d141820042a003a030305c805840b42a042c0b2082810410703440034908201c40d141440303200d1070340403010b130005c42d51400044109107140c10a0b003000312190000ca005c0359030452030515150040110840302c2610310b1154483e45e05030303001800340b4820850f00000041c0c07400001c0180d5002140d015105141f02b5130b4894500300814014000e103000035400070080703490b038074004d00c005100404111280e4055100da690b40c0031841e0441c110988640005c0c041400030070001c0c001c46100d0010340c3c480b00c2c1d0301e150480004082c08440c0309200000d141d514215515003c40e00161416500c0d00358002c224840540005045110b1801009601608040010865034480d1002d42030402c284c840049441d120040300202a44250b2014120915039007800d440072224079802d80d8241d0740350f40e05031789071410100000c410396504000c854045411140b140100c1c500b65000007824105603d0100080142c041c0025100d00c230180106040001400104280c225914410942c400d110802c0300c0d95140103c0c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 614092526 1250 614091276 614091287
    0x30a0b1905130203190b030f030307050310080307030207090b0103091b090b010504081906090816020a060f1706010203090a0f0e0f040b0402190f06051e090a180b040507 74
    0xe1a0145010502048154120780250f1780100300b5040e120b0120310a6038041c0d030052444c0045140d1610600d0181c0000917402c2c00214011680380c4e803596502c0c50044080403600059a002c80311541c02000000007007540814103a0940e849a00081081141040101d014090220000d41404040c001d4030000803050740d0900e044500c031900c180503c031031003401919140a980b103468056002104440008544c10f602441c0e040d201e40c50028400f4038603282c14504e074201c800090300c61501a00c01000f540b40218000d001000e0030318000064a912881c010071074283c00d04000203461041000c10080d038000c0c42075445071031003c1c00130601140d84800407c490b0b000c0380702e01c1266504c120301203800c000300c20404a00c6a030700400c2a11054440b030307082c4294200b094a020b5040340700030401180059400401200a00c0290b650a1b02c5e00790006002007900c0100c004049101e504020048481e110b80d1488800c0f01c1c03100c00700c003100e112450000b80190640d1240e00e540a8940402c0120150700311 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 614093776 1250 614092526 614092529
    0x9050f0c071104200f03010f0906080a030f091d0a061a09120c06030f0f070f09050906010c140a05010e07030c15050c1009030e010809060a1e0507051902010b011202030a0b19 76
    0x200b881d0a00c980c0c0d270710b401d04110f440c54014040141c00c0004c0803c00b0a0080160340b01100c3c062a02002e1140d42e810640010700c2112080c00140304601c043c00710000302e0b40100d5004c0c00031100c0d541d050a10f550b408050341d104815416020b82000c0003100b000b030b5001c0c402c3c0d45a9180c0549105e55a00d004000c5e141041d01c111101015aa0340c1400704003074030701c284102914513109403038090348035040100700590030310001c021f181000100e044900001e80d940c0801e026070603e0b6001480b8904181c98414259010341404485d0341d4810007080001c01c2c4055000d004440d4907601c4620300c0340040d88101d8440c401d00301a2401482084800c5600080c10790204500c50700941e2082c03c15010b08004594615081e01c818100c0e90000c00400c1406950f9401580c007074040c2070481503c0440c0e240d010055038011a0201c0200341d020602401c03110010104e01d46c0030655100801296903c0000a003801c000361401050050b408000030703025000d5a44100d282d10002400c44015000880000c0c403414010f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 614095026 1250 614093776 614093789
    0x30f06020a0801080a051209130e0d02010c05030610051606060602060f01050d0c14031f0212010503071805070c051501180b0f1203040f09050f0c071104200f0301 71
    0x20342c000511003a0100b80011141e5101018010b0195442d6400d540f036017212100390b52108128201d1800709400d84540140403100a010f040010341e0180c002e0700b11003140302e025051200070400c0020300e03a6040100000800241041d5403594025036466000c6405020000c0c1060318002e00820800d80010710548240445c4141c017000f6a211424021101100b100003051610200b80030300912020400003910a0302c00340c102d800700c2c0d1004100101c0d410414041140140d030011701510070b47e01300303082c0e1409030100750014110b040c034010070b108050101105c0c400007250b842e00810b9881b441212030400043d00482192a0441c100c4180e0a03d041c0a100f048274100b0214130f49040c2d0981c0340100c0c2c4402000501000c5007510400900800a8040490034128041044041108100810300130054400e4220010f850319283e62400b800050251040742d03040c005124410000e40d003070114039103041d030039500820342c00b40c42c0f84424824035403101480c019600115030854903056180246040b66503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 614096276 1250 614095026 614095037
    0x12090804170303150f1e010e0d0c0f0801090c0605070c0504110c0606090105031902030a06020309060106090801050c162409061b09060c140303011404140c1909030f06020a 75
    0x4940017042400240410b081c4c1e0001003107100c010146450301403c42c002070040c10030b202d90424100001e01c0051480a0440707042407069000d11240c060010207402620500008100d80d125903214080b032913100e4030889081100014404082000c8503402400611006d00144103015124a06400981017040300410302e2041c00c00290180c9084401b641c102c62005d4060000c410035803011041d00c0504a8043e038051045010420001d52070348003e503c9100343d500648101d506080c00180344000302c2e4812800c90b130504041c0010903485038100c03800d1015865480309100450300d041c00e40a00700f0026014403074008a45104002e40c0c07508000e0040d403051400300040040308006d030040000b61002d0100003850f0610510001d405510f010b0b00c928018008041808181410240341d580240c0020a041207507540c04949030629005d4646030100c411006015803905840000c40780c003410002580720b083d0189201d540c01c0c09445040003854008112005003510f40c20070002a41c4401811000142d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 614097526 1250 614096276 614096311
    0x402010323010506090619031416021b0f04090c210f0201030c020a170406031a030a080d140112050f03040806040b062107080c0f0112090804170303 65
    0x251400000801c1088010001d4040d908020503c50560800707511190428002c000a4000040400c8000d100b454155004030b061025558441e1220f10050645c80341e023a9114140d44a55801043d4802c0904500d890561040d9021002517013140d602c04145030083d142014007410320421140c0320064821048070b50407441112049038803008803c1d0310280080400200e00c0d001980f00e600107140c524468411542001210b03100d85614a070038046681f017603200020308120301a0580118a03402c24900786164101c0840790100742c0396444200e000302541000180c810b56803000343c1c80500c1380c10002d551182c0942e1070303080e501c0c446036090500355442d201d004402c03d0301e1307800001145c00b40c643c09000b0f0130880c0c03116590900180400380009900022030b1905800c4c000c4030b140242c41500042c0300510f641d81c588284a4104007a0f170880f2400394a602c2010a940d98004202000f8501104000281000c050400d840d55004903004580c020556011140382d0140001c040c4d8059026079410a0034407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 614098776 1250 614097526 614097551
    0x3120e01020106080a02150919090e060a0209030d0e2202091e010f08040602120c0a0306090b0d030c0602040506070c0303030b06040320010918020408060f0112080d0f0c0804020103 79
    0x2084005d200039405005244200c0010807690041c21411201030002c08110f0b401881f448200812600328001e29640c680d05c4600b20141000b13015017040120500b1031400d240000804e80381e1000720000e50600404d5500f030304c1c0d1501c42003035641d500400b0a1020380d44e6803150015401a5000400f00341c420b5005504000d20700242281c03144509034140c4500c0247c4000d200107865039007004009486003503080c844030140303001d1041003d02c294030141c1c1080d91424034850140468a290300012002494900120381c60f0703c8400180480c540c15091034405a0550b150103c00b9102c0c40c0c05c51078210340081407200030000070124420640703219850a1001c06a098180b0030580210b200c0509248420075006280c0c500401c10880359410614018000070789402030414503240305000081e8a81d03000608104400e4240511508045080f56034100355260126150340c00c0318504010b0014080041c010510441c654000d00b6075800f00f41d400c2c80079110380d00000e4154002118240e0105c0e04000362110314 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 614100026 1250 614098776 614098783
    0xd09090509061308040306060b03010302040e0d050a0c0f1e1a090d050702010513230405130b070c0b0c030708070203031605030703150909020a05060a052203120e0102010608 76
    0x40c050260040009589406000496020f19502590009810880840455000c1c05198050045941c00035a039524510500c0122009207802110325041481c908180381e5001040703403e4a42107180c801840e03c52410031051104c0204802061920704040440760002c150003000c03103c80c01382504100c0710342602c551041c04002206d10300b1040d0415041100e44900460250074402c0c010300d0702c5403d210f0b602102d80000315490704000780c2a18504407000120001d0368800c01c030407105481c14411414080511910151480c400501406130003001a42d0b440c440e01c00c0b4403a0f0b5400442c209618181540c4200096105603648000103041e040000d0145000000f01ca01401d00e80c1104100d1010040d8221442d070005000041015283c0341000c088041000719140941042d100000340843c2601c100100300c1580c1e48100d020b40418055800600c3d0800700341c45131265050800c03032055010500c90b00044490342c100401607100013010107513095000c1c030344a0102800f038000300545501c68161558 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 614101276 1250 614100026 614100031
    0x30c031a090703150906020d0906150302030a06050a020c120705070f030b1b041505091314150d080706020324060a051b01180303050a02130b03190e0d090905 69
    0x2003641c800c450420014600c094955600100c9050004005082d9590300d4107a9006c0901851303541c1e02c270680d800030310202d4403c2600b101c58035100d9000c81032540d80460b4488800b41c00c050180d55a45002801408454046402d0b00700c1c032310242e448851440c034500d4003c0c4c00c00341040d641c3e40700b0084007140d60041c03000640142c0e90400c0b0900c07050b9540500b1101e808602400c03107000c0150502000580c003d10200c40288200d141c0c42d5551218090020321070380040c0b01e50054451414008852007241001d0a41c40d048100c0a800d002d0643c0000d010903000f501c0410000c4c0b01200002d070f85000c3c48880d82c05540110401c030000c040488008540030307001900b2500d00c42e07001c4070030490910302d45e0246005000c210302582010791812606080c0c9802c440c0380c580880c20201403048004201581440707001e43c0802c0e4814210304010240c410f85c40400172600804524240010102d4406101210f000c2c940c03041c0f2880502207600b010b0754084c1c840074000074000c0414514140412511303094000d40d032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 614102526 1250 614101276 614101291
    0x1b0304020a172a0d1425091b050702011b0f0b04120906020d0513050a120c0e24041401090e070504051303140d020d0b011b210504080601030c031a 64
    0x19007964280e15442106540b1240341740c004e1044110050400c41c118004030241c9011046420a040c501510241a41ea80c8192101168913102c000c0300d401380c11034141c6040b0780e020b20f05003011400307a250100f11000c0301040503040109196046081011058140f0700c11881a0510744000500c4481a6034942c591f0142d603000d41c0141801c804102d2161020b4540300843c0592110136945d52030205107243e49a401c0354100001c0c51500c4418170291f0f10b4403000030706283c1c01440301d6140007a00310520007100d40e000085500720358540110b580c1c2d6a005080d1116407000700c81c205503541d000d20030003040b100c03d26408074003550030002298985480350900c00c140c031240290000301c00d603504407081c012845020016010a0254450b100443d2010340540d06484400241c11200400098098981950107009444096100b40006210f25010220a0036000e03e40541d928039848165139074040c1e50031000091080e20000424440018000f00c12a17001d00f4000d1021400000200b55943c021201d05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 614103776 1250 614102526 614102539
    0x30a1a030f10021e0309060709050d030e01180509150102010e0c060d0c17040c03330b010909140a0f02040e1518070804020312031b0304020a172a 64
    0x80d015042c840d00204041c0440203566a0341050706a0900c010b500152102d01455001034204142250068480b038094441112050346102c060360f0f00421081c40b8120079410041c0d800401104541e07540440b40103860010036160151508000b100300105d011038209005608203240031000540c00f00307008030000b00103801545400162880360340500300d104d4594080000006004400088507041c0d0b6000f18030401d0b500d41d82c14554101545018030300d903080d04040c204a034031052021120410340c15401c801c201c01140f00f00303608005907030400040c3d00c0310810070305149126840300400701c0c0c403c0c400c2281c001d040124013801400700003203015601441b07001c84904404a81035151000c141c01400030020010b480b02c0a80c0c201082420030b0644219012070410410b01003103180a01000000001d800c08a0741186480d03041510445c0e194102410308035400000b00b0290b48506000e040903090320075082109600442c1071031380e20104003a0041c1030010030711038041001e030240040c108000d00200314 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 614105026 1250 614103776 614103793
    0xc0703030518150304060507140d0923010603150b10050d060915080606090403020601120c0801051f060912060b040f090b191401030b0417030a1a030f 66
    0x5880507401442d680b001e00c9405005a10a81d480d0818540301244070f050043c0c490800e454014161040034011006010a203161104510b1000d0709907032041f40c004d103000c0fa0107001400c11071032003580c4001e10003200868031000002c4920541100c41140d1107490236000a0790031030100700460340030301080f951041402d000c1e184217074440c50142000c4050006c0c00104556600c4001040b11540b40c04ca403403081010004000d440400d1010680c000000e581c1c2011078682690000c0d155a01402079a4a0080b160030540501141016000182c4443c500810103400c03d6481c02143c2c46581030081c007a04a080c00c0441c280c0d10a200781c2c42291070041848846004650310f00780a40147c046003174000360b4449000400464074010711003490f00bc0c160040700b50070214003103008100c80d5200052100d0801d0541c82d0b0080102c031100d0704481d08994805002e459910b4106100c554280b41d115480c3e10100510102501941c00041001e4602a0450442104d0010701d0f48030010000303010702c681c03c0b5010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 614106276 1250 614105026 614105033
    0x3010504050702030c01181101020d14030a0627050606070506150d05010f0e06070c080909070201110304060e07060f08160e0a060c06060524181c12050c0703 69
    0x1c035039040b00c081d006132400c0100800350182103035950391030030040462001250b0140040e01110401e1903c00b0300c0030302090040305c031000d44102d0300c41c0f0114400500000029511540070b0744150003130441c1c00600580001c0400a50109881c0e0b46080d40050740742c500412a0761900354111208240c0c02405000c55540d10ba0070801c40f81140451541c000c2150541200000c03020310848007210203020000445800764200700d0700d0704400a15030418044090010380106d24098140c5038942c0301160031054654807004224050b003120240040107000100030300c070410200d41c0099080e02400022103042070341d070f55001c07291f00c90041e84900200d42004d0104401c01d00103e09110250540e0a0044500b00c00c2d4020440903141e540c40b050024558681c00010080d0034000c01c401005c013101c01702c01c04540800501d079403d05482000391880c00001e05011000c0000303480b0601098002c2c14015a44007445184868081801d002c44114a40b4016041d001d401401640c030312141c010000e18003941140e8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 614107526 1250 614106276 614106281
    0x10e0604120e01020111040608090d031e0f0216050f1002090108010509100b0301080d03050a1b1b06060306020315013e06090f0d020106030b06090c0c010e0c01180b03010504 76
    0x4960f04554a400701e0031150410306005000500c4940e40301c00461403ea540c15082150b5500c1c8030040500b000d48280c4c0d0344209940729540c002407880001100180c03020351000a104801a400d12048505c00038030034000c0c041226020011a0070507228501d81085040d000ca202c0d420703c96012820303440045c409130800072175007139000003444290080c16840d61820082900240e03c242030542c480007021540903414003406800c114500e2090000c518581950740701c01c85248201401c0040f0100c83c3c00a041e14444140c12054008108001481d100e0810b07002a40c000c0304da60407860703d038a41c1c043c0780354070404004e240e40468008107071010018441140c42c400708600307000540e003001610b502180906004003070003a14140010f02e03c070507040080504013030741c0c001c2c40e4095916042d42003010545290409034001c90460b0040d80940e60740500b0b00b05401800d0001c1510341c6054050250b255000440105102d026265448040d06d010084801c501950103061046c0100380b004010034103164 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 614108776 1250 614107526 614107547
    0x2070f2907060e0309010215090d05091c05010204050f1e011103070b01080607140703090e1801090302150604091e0305120403181d34050408010e060412 67
    0x60850501d010103940340c50041c1d6941000e044199000000c049a280d0380401220715020b600415660161511020090721400741d4012003050000c0002d500380c065840c0b401022040e0701003042c0502c1c4c24844d041080c002e4005000b070381c0c041e5900c102442124500f0252800c0d80b03c032a4000300041403644401114060100c5240c505584418044840000c41c405100c1c1d020b81512801807241c0d103400c1d18010010381920080744064482046040c0200c6e602c640208162440f0102040e55510703900804030024405500c41d542d19443c00011a041542c04555000715030102c501c4024030303803034010810003201c0200c1401450002d440310400c2e00901800c035920a407501a09000f41084c4240201ea009180219000c80009400740411641c01600f100301c900038091184200d04081ea01c1d16103010040c4000d0718100440c02e0088802650b0f151612100701b15201100c40c41c804c05041c0100581150414010b040055080001d60b4810340310000381e06100d103400c0544103580200030202035841030301c031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 614110026 1250 614108776 614108849
    0xb0d12030504261624020702040f090206030412090b0c0d031b0f0c081204030f1214180a051009140a030f05280c050f060402090604020c10051602070f 66
    0x110300400301e0717869503500705c81d46860710a907025a45907035510400084400304022441414502100540542c840c60152031b8842d50044440308100c4031100140c0390b02d1010b512400b180c00c000220140d10b1407010078800703241441a1021321613180800c3c490503141000d52140c10004209042500c0814491444818140d000303040030742c5440440c01d40e05900100c00c49068000c03230300e0402003040c400e601000410070305001d0f80303040202800380007400f840035101a1051010b0400c6000e0a01c00500030b010790012158000126003012400018010203000025001d450764615200b1503071540002041110105604d070b650248000807003e000e0310181c1042e051001224030651044402215000a950403e5405c2d11805064003552402c945030000740b031a00b2a00c0d41040040c0001a198007407425080141100d01584070701d6018901c87c540060241c00d010024244410b124103004680d0045004020310ba09886105454000403521245984101803a0a504c40301920010f400d140c1c0d00000c2920 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 614111276 1250 614110026 614110043
    0x16050f0f10050a030f020c0d1b020f0d060b09011e05060f030109051008060c180d2f03070308090901150804020f0f19090e010c02100b0d120305042616 66
    0x10000d8020007260047ea107881103a80c00600c180c0030301600240d0b030b000f809e500f114124141040550100b206481c201c1c90103030051007101800c0c42049001d40083d00c1e072a1010f0032415040d079540b1000b20425400104035100c010301d0a4020500341003010454401e803904514151440c2d10703088032803005200041040c945d01c2d540b6140498101ca05204050041403a03501894480c0d9040c0140e0081007100c01c1f141d846501c403a901c206c00100301050041c45040f4202104449825900c0b0524041c4000418103502d0b003c0c00381c0c0401004407060181c02c0303440701075a0350842d683c1c9883c001131012010b0360606000c41c03c07101c00030b0014a885000300300b0300c2c1320103001e4103070f40900c0d480801c54010125000030030340301e010310081c04800c000b4821809052800c0c4001d0240086560011f5140d603111503d880403162240403400e000c3e2950f080311445190301c40c0c030226040d07450340310060050005880c12900d8a54080e00b42c50340441d2900030320040c994140103649010920707507a00740c1c40688118100c46221 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 614112526 1250 614111276 614111291
    0x1b0b040311030d06081b0d030e060408011d0c030303040b1b0426011b09120c0e0117061f06030e070b0d06030b0603070f0302060d020c16050f0f10050a03 67
    0x8030602c06800154600c40d00070031014181802d66040c515441c60f400300c0c0340038040200e0740c541d8640403105030407a05428642c0343e2034110408180706125941011001c0d40c00c0030640d040403503403881050568452134003036900340101c040070507032030b40b2094070f0151a1207500d0380462040e0301211107612140c0b0310800c100b4a03099440d5610b10744e07044600383d90360310820408859508054207000e04501c2c1c1c8bd102500b000d101420981c0a0004102402000d00c08280c540c0220308000f2400d4104001c1e0a88207416165503a603280d40702c901a001c40542d011a0143da00481c0312008a005041803010b40c03191200c0044e824814210f0003405400101c01c0e8900ca092400900542201b00400c0e00e010340640104038242182040c410201e00505205d01071f9000920400030402e0011062042d00e030b04494055950188030365180c041d01810001526078000c81d03c442455103611003000049a074140c80b03402d0f001c8841c0b0204050425040e010a40107200c900d07081f00c1846c0300300002d007080d02183c1000543d82 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 614113776 1250 614112526 614112557
    0x507020306070c050c01030507021e07090203090c011205010311010807020102130303090906060509031c0215070c150b031002030603070308120a050105030303010b16060b1306050a061b0b0403 84
    0xc02e41d2040041260b07030280c2402e000051003896180e900c2804d051205082011000b99500d1010ba07100a44507094000ba140e008001d110000c0240281501907449044c07401442e512100840003060105125540c030000c5111580642412250400c040141c09520341d0015604180e0041031201195800c0190055040208491401641c006d0707442c02201c1d0704100d4101d00300d0b580c17608080b05210702406440c045550000c0c0000d0740015121003580480b0f5240416450104044004080c9415040801070a69488030701c907140d850103261043c100e0300e4610311801c200c0c0d401641054042c0c02c003800c045204041500299046400a41241c441170359030f0f11005040d41060031601020100c841c00d0001041d054001c160240100b00e014500d5549031104031503040c491180e00300300010300c40b22610300f4814980e00c03442c520032001e414903805c8480103991b900100541e0003454444c008408020070315038407607551505080c0c290309804100c5241074507021444031006004900300a440480400e61 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 614115026 1250 614113776 614113783
    0x20a0503182106060405060105040e130f0b010b0903010c03060b121009090609022b260307030f0e0606011b0609050a08130e0c0a05031b181e0a05060a05070203 70
    0x800710b41ea4080c100c0350401200700000e4035406400181000012b010031b2104004440c06150030105142c0f104402e200c036032601901400010802920465501c800024041100b02c010080480124002c00003614000342c143d044640d20b00032219406d40600c110010031031602c240a4010b50000d04600b40903035036030440400e4803403440b0129012a00c3d0f0508074210b0401c9450301d04106e40b65659a40002c24100010070344400491000c0c0136252181c0034030341c0c08a445441145c04a6102c3c03003013030340c81c90003100103000380844034100b0000910f0103001d400b00701c07000700d40640a414165030b2150008a60300c141303896040d040e1029078a260b5a00820740010b00100403100ca00340c4038070785070b54803070496902d02c0f00d290405500c1140030a900004001811040d0012a58811145d04107542c0f2615000f40d040e84c1c07100c404003c407101c01700000f10481d615a0500480c0c0305038000b00d486d811001d006c0207011540780800c200490300b00049000a01c1a8a0054080e241842142c6420f0b41085500e4000078903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 614116276 1250 614115026 614115079
    0x60a090204062006010303230918190b090c1803010606030b12121204110a08061902090310020702151305120a020906150c10050105010f020a050318 65
    0x850101c26a18500d03403d50010709400540900140900d50302d1030728040d0983c4284000d0b40c03040d01d8154080c035500b40c80312068902c680c3d406021540301c016900d120aa0002090341da648081d560045451852103890250080c44d80c0060043e140b962281301d004201600810f07210030f9400c8110303a90b50740c2524240303c2c000c0204140d980c0460043c10301424410002c030705c0c0d1654440c42d0040d2030701c82e071440c0440c1b0403950230079a86040686941c0ea03070309180c01040b6100b5065544003400d070344000b070139010005500780940c1401e81048250051f10f4050000c0748aa85a52034040d00202c4007804942140e074050828079001806030703940100d100f503c031111030b48880c0300300143d60b1500c03109000f90f050550b4000045540e0000070480810a03400040d05140300826245c41000d141e000144040c00403803c1e1204024241d04548903202d4401d000006817409004440c005100c40402400b070070b10000c0d4441d1000e07001805180741003c500c0c44001d0300601407501e1034010800030000422083d0407070300c404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 614117526 1250 614116276 614116289
    0x1101140a09030e03120f1612030e0601090c020a14010b09040302150a0605091521071d070c0b07050403020d12090603050c040b030411060a11100903050f03060a090204 73
    0x9001d04107490043c00351565180d400e8001c0e03001115090044103101d084540e02010030580a845003464200d441d509001407000074040300c0c0071701c800300d800307a0990800d50f6284041c02c2590789680c0c880e958902110800d82c0480d0050340b051900201182c400c0e034510440404100000c205841114089850b01106540882c010b0f407000c2500c010745880454410b400c10243c9409004c150b00e40f10001e445490054900804ad038480420340c141e50799140d03200074410801d000001c0400c4101c035070f0b4945503002445001c6602c040d000d0012201201c107201c11344030300010b480e5808030415a0b2a202080310b801094082070000400000c000341e580c40c0c0200399118400d8040d403450100c00c501c000c0000401d17034046c205240c00c10040c441040b9410090301c05403203000584a48a80d5682080c0c0805070107402c0c0c0f1604003100041c4079513416800305a2410400c1c40b034084a000ca0f03c114040411980c1440c40074000803400e200400e00c8060560045800c100001c240180041d100c40304175089a010360b0112 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 614118776 1250 614117526 614117531
    0x40603150e09240606030711011e062102030d12062411060114010e0310020f030403140705060109091b0f05040b030c03030301090c0c1704031505090a031101140a 71
    0x704000c894400342420401c1e94900f11800c54100100800c60314007000c0e2611041c41400c40c11005004825440018941e034401ca5110345005441080130041c0b1460050700c80100c84140b007100309410460500003940d40c0a8010000f2a0207608102d515160100045000507180c110010300402c00c400400f8000701c1c40ca10055031031081c40c001078421041071942440c5900000010445a1158140d001903843d00307003041d14243c002500003d051080d0481940c100170b2011850403444e880c10000b85200e01c1c4603884032000600304102501c2e26000b810f00040999102000600002060380c220b00c0840f441414809007410103c3c1c0300b410140d10a800500701c0090120041100340782500a0851400d402d03000f401e410240240802e4480c40b050050f50421500c45043c406081d10070041d400e0107940000d98084444d280707036002d1165912612003510701403151000280140701501c1a60302900d421802480d02d0283c5e950240c50b01034a048038506207550b91800b001020711800070b00e6110303101501c2d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 614120026 1250 614118776 614118793
    0x290409020a0305071805061e040f0915030f0809060d0203090c03060115050403060e07080a0c03030807141207050c1009050d0306030308130f02060d09031101020906040603150e09 78
    0x1012210f004200c0c60800c00240610b0b20f480c008070101300c00b030704c1d016030309503980c0c9004180065507a0040f5100b4829400006400180070170205010801d4525541003444909a034642d030100101c001e000207030580d9100e049800c00141000024440710300c01901880c10b02011000080c02c0780c00488044010341c00900040c44586002d0203440c0c050440c81006041310320000c400200203004d00d020081590f540c0c0d0340d145a031110304100707030802008007004071102c0c07049a05d4600c1d204409407000f203010440300030101e0035042c000c00d8500008050184180d0901806220302488100060502014010100070300510400d041c00152003000c0103950102e8810030380d10b030080c03505800d207604404052420340240f000076801100c4070b40114540d02d90494501c490b040c0f2105107c05080d00035402400020500c62200840c1c2151030040d001c0c1d00c80c03200c20042030b10b00301d0a0344114001785a020360304202c1801954000c0c0e110800c4507107540b12442803103450b240f80440c0d0724000c1e1000402c90b40134100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 614121276 1250 614120026 614120047
    0x30b0c07050114010b07020f1503190506011b15060504060b040e092b17070f023a030e0d0e15040501080408030402062209061e29040902 60
    0x6040f4290b514620a05180e40c90080700200a00030000000e04c41c5c1c0b503154002509981c2d070700d0041100c4009117812a0741b8101070302405d540c411681a156526400c00000592960040200100726140032218042c00706107555050741c0b004c1044201002c44e0f582e00004141e685452140a000e40410030601d50b4541c1807407d40c071000000201042c1180c0d200090100f08903848041c03034a441829820440b6031400031480c143e80b56405c1c2103130b00f00240020020440c400340e206005208942d8607030240c0740c1362031310941040403044540c3c1050114001411410045018203403a80148062900c0c00140b90180b40c00e40908100b1080d14440c001600c01c135070504513251088e4a008041c802d0510b41d03107000e142030000382141070009c002030704008020000074107540360301c6c007102d40d54000d40ca6070404444002500c0c3c03501d01c071240900c2d80d03a00c3c9040008100540788458000b464020304d501400c885d864010003249030b41c450100d41c503d0528886040c020310000d84007500203001d42140158540c00100d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 614122526 1250 614121276 614121281
    0x12092a0d032d03020c0c0609150913090c14030a0b071b202d1e121510030c15020a08120a0b0a050603040b041b180c020102030c03010618030b0c070501 66
    0x500c0c040c4581420040714440780c1c0c84030390f0b00c09c2e19240d8030300d0300f52180f078410000b40504a45149058020742080c08050401039496584416030314a84030040043d90004281665010745100040401c1445d5012580c0c0901415a0030035401c1d042c0c40707000001c811581c84403060111008150304005001807980c00301e1800f04d000395005c120405081e0204c41082c1c00c0348001d140103c2480c0e00510300042d1444804800d0f03109002890000350440b0580c00241013119a1180c2d4030111031055070214022038001001d80c9480400c03650841c2c0035807051414402c8070511140c10b58500020340c810340341403a00141c5202d001d09619801d80724074440f01d18040500c0819540c0314680380d0700c10b8603d0803040c086c55850405481d0019001031034079070f00c2d649914124071311104958856481c62520384000030100c490310000e4541000244082c007200014580076401c1c0d00064440c4501c46c1024001446594444d6544501d0b20305c203060440342980d52610340030350228095030903200d022000107485080c0315090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 614123776 1250 614122526 614122543
    0x3050103050d03110a0c03180b0a0201050105030610091a03011e05070c0b0c031e01080c040e0a030c021005040b0f0304050f07080d110312092a0d032d03020c 69
    0x203007403e200c0c2500000c00c0341c1c100c0c420856178100340070741005403200f0b25210780e111445000c602c40040078460746450603c242074100c10940c130010340c00c007400401c0d6414040b443c10b00070001c1d54035401c0309608212250001c3c0011410880801c92560709228543c3d50900900c4d40790420344441081c4503244003412016201c00601410074800162905d80002d54554502c591041802144d240c690703e13010301a1014681300c0c40d2041c10b190b469400803030b000d0301c0030504180341c500484d001c1064921080009855203409440035000c21500d0318a040542407007900d26003801c5c2d2920b441d91030152a000019900e801c500d240b43c3c030001d008020001006001c11a048040101e00020485245080052644c40387c9680d802d900300400020214550b090800544845000d000440c01043ca03003d00142d540e92244501003078080c08941103041950002607580c142400081e0404401c200a1740b4190381c4250701c040c039012002130111902d018441c1e64041a0021940c0e50341c003517501c54146204605e0050b69 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 614125026 1250 614123776 614123803
    0x3020f060c0406030f0b0307030803011e0e060f0d05030d05011503140a0e0c1c030311041401080601050415081021020f0d0c061106010608070f0305041b03030305010305 74
    0x100d040c46112080360701a038049408034540420034144084001c0c000e02810701541d40c052140c501d0101c10000f051b0061410780d100f20401070300d030300b00d02454003e40751041c0c0700303940c003481c48130000c10082d0030400c1d4084803401018052035032484040d520b00b4955803103a6030705c80c0c00030f940f000140550548c0c81040c280303404441ca800d00500307412810140c1e01c094040e101c41c04e001c3d46c031140c06141072414468645403010040c0064a0790740d000d1a0301c00c0409042c1c500f10002481c0c2084204c10b01400800d480c2680c08007060328040700c14000042d1080300300604083d0502c0000c3c000000d4415102c64042c0e400c0800341d8840490303041c00501d8200c100400d40103420400703803400382c071038030003005c0d0b401d840680350120f4004e403e00c004003000c42d00000c1c0c002d10280005403214000720720b49030071a2004111152410031a4440e80c0ea40c0b41c1240c5c158000c1e1141d500103440d100d41c540c0c1e0180300b90402d0360464001d4003120101d00072428042071004841d4822408a5150001002400024020000100316 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 614126276 1250 614125026 614125033
    0x50d02011a031e16060203090a1203080103061116050a1424131406011806030b13210f20060c1e0301060e03161a1605011803020f 57
    0x155a00003a121041e051441e01030b0305602403003c2c0c01c21010088140c2e50500400348000700707600c2d00002900ca81c00289614059081031340009040b03440001001900c80d00355450001710b90851b42d802020780f000d181180000c410a0040340a9010740b800100700d110300c40c0009008200880c90310301c2c410310f1061018070b006d030062911214060b5001c200d1021461409a0032115a5200540c0b0700c450724078800f002d800026650700c22180041c00246d2756050700c040c10115040d546030005488140c540d580030003000d460b05d07903004c101c407480780c032482102240c4644007a03040e8410351290280a100d00c2c040c5c00bc0021030040c00e020b0000d030045072400c03690b002c3c111420703248031007080304584d1014040c0580c840207200059256280e50040c20000042d910388812035660b5955640082481290180141c86400780482c88100540c181c5214800c58400325440c2c20003001d5603681c202540c22003078501204d20201141c1000090b001e01c5156080c1c2a001964a000421811b00900d808010200c0703401961 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 614127526 1250 614126276 614126321
    0x307080c030910090810061802210403110601270b040e06270309180414060c0d0c020309010e010302090103020d1103040507050901060507060f110a090311030a0c030209061804050d0201 81
    0x302660255070310074148d0100540d591185a01d0202051042400d00010041c51007d100415a10140d07112240c0d54101c03c50b01544d80f1740c0b80c03042c1c091310041010031440c03141d03078405121407415400414813004001d00001ccc144010b083d002e41000c50845c4c4202c11107015103883c08611501512528889056500860030050382e1408125135080c0081c801c240615110009000c01c5800440525901404815503c2904160051600e250010403020080a0510012154051002080e1000d518050f035690034041c10350760040d0002d41c480c140e0b25040507000c00c800084415940240d00070424000312842c4e5030701d000d0400750b0604509800942c402c0b120403004000c0954410255195550801c0c0c00180c0210640c5240c0010000303c0b00c420340040b004900a07081781e8004904000300c030b00988020307480d00c52490406881e0400310000401010217400c00340054108164065408500030745201c09564900141ca008210200e034101e86560098800550040d420f004094500303804800390001c44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 614128776 1250 614127526 614127539
    0x1080706050403020f060f07060504030f03020a1b150c020a02041a03030711030106121b06031107060e03040503120c0d0216030b15060307050c0106050a03050307080c03091009081006 80
    0x9201e14800a449603040c80c0c4217000c9507540c842142d80c100c9100352101c1c0e8070b403543d02c0d250010b0402194141c000c17810451051000900a0013103c501c0c02c070940d908002182092081d851400c110181a2500b00481241e1b5034000303813510440c054080b040c0c0081c01c41d29050b20400c801d6a5106072154078a1543e80201c100c0e079100001034070180c0da071001d11441151000c2c0d01190061090750303c00c803a403d05d0010a0f2050001c0007407401140058010417105064642c0800c2e000d680040800e4501c80070200300c0070001c1801c65000c0e100d030078104070a9903c0e1980d1400020702d020414400c1c410300c40f40c006a0840c00503001c00c04912448040c1c0040d003456607003d9603a0000c41058030024110390030410020b0741021812000c48400e14000f00100e89130304045c48000e0441d040010031480c1903282a0002c2007900d4460788607030450f6481001113181c0081aa00c4200710341009004420510081c8a031090556540740e0303524080d1001c0c0d41c0d4a6070a858188403901d041101046007a100d40b5140050006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 614130026 1250 614128776 614128787
    0xf120f032a030c150723030604051003230102070b0106020607080114060f0a02100606030e151b0a0c0c09150b09030d05031b0304050c1809062410030f0501080706 71
    0x10300381c0280d4904c66907503401425580c40700e6804010b1424580111401e81040070326000c1c2d8001e11080e14108600e584480d000000d010090002405034120001070f0001c1405510000b142c3c2d4403078400260030a525540c90b020380c0c4100382c00020250f000007080008255110080c20b0041030000f00c141487e403400c20114040d803041326145e0710324804c00260030320500d000304806000d806000c4400c101460341c4287c02002080c021800750300c0d1b80030700800300c001a2984030b90ae0b03024100441411f4101c0095180380c4001e0f50159149105001c23150f455000480e1100e200d07030000301102a000700d0440e8034801501d44150aa401c07608068130140007074030054a0000356541000064200b0b10790303a4845882030a020715011802403200e680000c00c000801c8004188400a41d5040d24986090480844201c004d028119040301c1e05500c00c074001102c015810003800c0d10082440c007501070580208003c1191441c003105140301081c2c413a00b201d80015000e1141c2c50052107010041e00b10300341440d100810 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 614131276 1250 614130026 614130043
    0x4050c010f2307060212090a020a0801060f14030708030d09030207050d0b13080903101d010207021806040b0411181c08030a180f030801090b0f120f032a030c 69
    0xb041e08012486404000c0e0650440340801d0320a18581e14902d4902c6500340c0c0e504a603981280102a5220005802c0c40c050155009a50344001d0204a103401c2103040d450f070b0441c6040c070507410302c01d040d40000d44440c240700909241180d08400b10b808040c905000e45000c1060340000d0054585a40300004030b625141a983c110280700d08006500295080452043c000e651013182d15024070020b40b14112503951140150300240d0001208811070840303900d0803400345c04000307900708954030561745a20080041c110391050008000154100003c00858220b40c4034401c00407081c00300007684230166814010b000d010080840b5004100d00c00c603180030705501c4000b400208903c0020012490070b0700d468002c0b00b52220200580d4070074607140c0c1081d002d01d000c4c00d20280c0205903028004900d40a640c0981c400151020f06a10520f038401d030103000c560004925001098040c135030303207241041d00510007808191032024003070b0a001144c00304200740c00300a60380c01925510400c140d1125a0000ca191a0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 614132526 1250 614131276 614131337
    0x1403060607020f0f03010507021f2d0912090518090c06070309083c0a170d05040b06010306050f0a060f120e0d03061d0411011704050c010f 61
    0x5050400d0000815080c2c2c007600005617140d400c100c03c03c03903030607800554828503603090b1f0380800e81204055007100846141d640ca217032081e140102c000d4444240c104500d0500c500303001e400a042e90054464801d00c58420421800182860310304000500d01082e200503c02a40d085d01c42d02c40c1400080c860b5030b01d49900a5902074000820341c041414020150040200403107410340340c84568800d01031008912402c3d01031442e40c60717803608501320040c540c2c00c2080c18500c20010094080c1340e1b00d41c0b01c2e06052283c0310a40605c010450010303070310518060300307018034490302654241e81840400074007500c481d0b80145024441007402c40324155518140306c42161042d0805044030100003000711812143d1916014425081c10300490103608001000c0c8104000755600304543c0d5218411070105030040302c50115200100d402003008514150b4504252140505005120f00d00c280c416055200003120b080e110340e08111424441960000a240d170844503d10f0000d5002400304081c1103c400c10600340c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 614133776 1250 614132526 614132539
    0x3120105040b0f1206061c05030d0510120f060e011505062a0604051204051011190b01031b050a0603050c070b0a050405160f05120304030b0106080106140306060702 72
    0x20791807a200d604401882e1000507000c3c01d1480f042c6101c469407034038192290b50041c96100e548030700c3c08500e045042500356020303005d1480c22b840703500703400c019003c082c1c054240030414000000d0211400c0c50000d07002480307600040000c2810f818136404807520102149003590401c0e44080e090707529a9480b00c2038613822286a500c0c2c3c3c00103102049c03000d5010007490480301e124485003d9600c400100e55200314070600807164884180c9038440c0081c080e6101d4540c108403030844000c10180980749500001080e00112038856402549094000707140b44025102409110014800d02c074100101d90f800400068914003080d1410001ca103a10550384115020540e03a1000301c1e41482c09031045601c803581100580030241083d0510b0002048290b81c101c80d54031455101188244100b00c450080f50107000303004010b0340c80d01c001d001e5602621020070600c1d001c00c210210000350b10203a00c501a046a6442074403c0d810030101070210010b4141d0b400d81c0c14810303c04c1100b503540307500844102c15810f507540b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 614135026 1250 614133776 614133791
    0x5131a0c04260a0812010506040302130209030a0b0c0a0e0f0604061202090d06390c050c060301090e06150d03260c030a0b01081e090a050316140312010504 68
    0xc92100b100018807548072405031400040c140700c1c41d034002e40b14010310b21030140707540d99840c420014244034900c4000d400000c5c0316800040b80704c0607800b50505840103001c0d10201c48a43d91000c0c5080030032900c13000003600100700c52001da64041000c1c1450103003610032004100f81c10001072140c0c00381d480303058208921410103622144a07501510345150300a0212100b540300341c5421005041c010400005a005451042d8203100c0d042e050301401c1c134140142a190060f034114110741c0e114480d00291400e01c02d000300f144840d21140011802406415400255808070b2100c0c2c1d42070043c00b030005641410300c111449829520402e0164405230f160401c103410744400303126005001980c03605c00c0d240d018918100540c800403100194414048401d08000c420740c0c043c015544a04140e52115102d450110060220f002e04038486420191103070071690744402c550780700c9140d40e0042000c08006085400741100708040a0762441d00040054003840c200400d18200031480d160500c9440d1040703465060 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 614136276 1250 614135026 614135069
    0x31609030c0b03041704031a130b0402091315140117071e051009030c090905031204110306010f0f0902040b030a09111207140f090703021c05131a0c04 66
    0x100f40d18017442800342c0c251602d649041064800d1844115224a25180000a0030300554030b0103009003035a010407400d010f5101d40e024000008402048d06203540d071050086004511030480c40d0068004240c40412141031001808a5655041c1e214000e54483c0040344c0c00403010100341031080e00d40ca0301c1c1801e15002c0c0c61640600e5403c80794805030308988001c25844100e540591005d06a80c001d8162240071581d43c040d2000710781d121200645190030030700000c042c400c603104103903420501401d240071071000c2d4100000c0c200002079121194039207440b0000c00c00c02c481c01005078001d002c0c282c000c508003880e001000c44507100080003507803800c0e5200002020800360400103486070303030040c0c0b01d80c4c1e05503a12400c8580d207488601840101100046181449107002b8044200414015040194584a0030003d8019402c141d42040440f8000003600004c50a0f91040b2407040c040c0c013a046441e00c0030f03410700d05141d14602203846c0900200004001d030f034907600c00854080b03400c0c180383c00171201c08148 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 614137526 1250 614136276 614136293
    0x708090a020a03031706060414060c1e0a05010e030708091c060c2307080f0f040915150c02030d11011b02060403110705030606130f0c05031609030c0b0304 68
    0x840207501a40c220004018141e100b1170102c0311117001034203120140c49000030048140034610900e1003189914410314000d00b89030000e0040005007004a54009150110207030000c04813072a150840c2d4007c0d0309420501c81c0901070001c283c500e020180d0325140d8151505a207a20815071264001e00791084078850320000525a5607600750807a108101c0c04444141c01050040c40c60803190b142c151540191800c46030039011542c079268030009140c540303000404c01d0519500541c0081c80303000c005120026001e80c40340554007081d0031075403842d20094100400601100c892071810b10821011449490041e1000030350744907071f116076090003101c0d0a2450b0b50203000d0801c3c40003242003c3c20a600c03136001c598000940500881c03090b11601038000c1d0358001ca95030f500ca203115155169020a01048050a15203140116410f4a0801091904010300c122003903a0305044000c00141001040007119503440320400b000600a10700b01c021240796856554114260b07001303401a122002011508100860 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 614138776 1250 614137526 614137543
    0x60306050112020c0a0203101506051c110c0f060f0a1a2407050705121227120a020906040c140309010209030a0305071b12060b062a010b0315070809 65
    0x608840c8503010503540038004e0708811010341c0c00303499827280106640c0e0088040c2c3c0c90311404003040074050303000400364801030300240182c030200e101d0402104059102c14084401441d039044000e244508202425029004000b40141c4900c0c1c503000c44c6100e103102c40340001a80c048219048030707c400d1021010035100883c0f81c01440c02c03a0f40081c2e0f500400030301003500e80c102c0e00708031a00c000c100a0000d1282e110101000c882c04c64880402c10380c1c0c040c45c044c00321019860000700300d41b90781c001210013080c4002e001102942803035010f901c4103411480c00c05003959110006540c00c0c40400003007074018003801c840440e0f40c0c107026001300000311030150075030544401405c010300321900d1b00002c2c10003820b940d004440a84441c00407a5610f181e8400340491107017184c5140340d03030b02d5442505480b110b00510000d007056a10100c104289000b01606902404140024031541c0200b440b0720311805d0700f1030720390404482c081c3d01300145d6a0b00c100d0290032800c1d84150907090411407079990100303035801c0c240780 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 614140026 1250 614138776 614138779
    0xd080d0e011e0902032509060e0a05070306051e0d08120f060306010609050f19140109090b0f1302070c03080d05310302030c0102070503090a060306050112020c0a02 72
    0x2403028a0303030921015005042070801c4603403403119003403854200c0d50a540d500301010b9010b40c0100c001b01070812051340c5000382d0b06200b02c100d050041d00d0f14400c0c002c0d291140c0c01000c581c90f51100307000d91003a0501c2840d40190042c03c003040800d10306030101e05500c01400c3c44143c90a040a81c42c20940c03182020115007a500c80700c550f96804034101c43c0140d400301a41c0b42c0484040a60000344035050014256060301e103a86c40c2c840e8498500300400c90700408031108a504020b000761503804200c28000d440d0044d020b5125041c4440c92100001804031480d940400c03030302410402c2e05080c6840e44400441c20900666404040b2148001103102078805d651005100c041d40d80b80000034008000040c00420590303410500142c1c4503038141404000b004031940c0c8405449036040407003110300205e02c91049100c3d005032424021904515422a003000c0000d076129000094040d40030300d042c041c540c0181c402410200000c50606000810311803054610440e00f507030008503448440300401411580c41d50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 614141276 1250 614140026 614140031
    0x50303070b040b0112211209050718061404150b1603090512071e050405040506041a07020309060d06030803040309031502070503191e090f051e0d080d 66
    0x500707141c461044101220240d4440900400228032130114102d0188100c0e0040301c268004884011144140c40c0c0c824440d00a100414184051300650b50040026943c01880500483ca180c40c009001003800a0303032076504585030940c00d104041115000c05c2c00514140ca00050400803004005940c841a40040340111404500500352014800781070981d94400da89840302d599a510521060104c1c0301418074054010b05002d0000849130403000d0031940e071010000280640da0303c0441c0486000751341c161007a8003e80104414808881003182c1220b0300410305a65601c0d004500a4aa0041e280614452000052141442e0000f504000301540d00849211b41d070b800d0518020b0a41c0802e80f0007120503590f118038403188900c5078400d49217100e0300070b00514a03100500015100c00091035810702e003030254250542050b1864022a45a5103c003611307a2000d42d1700b4024000c000b203141d42e1016210700e55201942d4401107800b0389040c90300c0d1050766600c0071950075143c140001e000718000e0409491 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 614142526 1250 614141276 614141287
    0x3070515010609150206071805060c01060914040f030c05010f0c02010f110c030d0f06080706050c33041a0a0603030908060402011e02071203050a03050f010614090406050303 76
    0x410a000504070340850f00e900360616500e00c499508001291420700150b0440d00000d561103014001c3e02c404912190480c0c100c10b911040080d1194000280d804641c2c3e5641750207008602c10352240c01ca850b0841d18125541d4603080d03903840340704029400011f003041034108041041100940100c803410209100c00d000d182c00716a4020b0080107403100e9031112a00704084c42030541000d00c12500703200702201c0650329148050f107043c0c000c5d00b20b005123141000d90314040000e1004040c00804058011596010384d50200d204950380f03881c1000030030710481c40c4200200c0b680040031a0030401d0206c07840000382401c1e0341d1030512a042c4481403100800381d501d09010011503410980c04003060b2071080d00c4032107005480d080c00310b50307442007298001d000c901c1c01c003402c0380445400b903502050498240b04981045840d41d61025049030284001c6010410203e0f01d601c05e141c05003c2c0759408030001310316900e00d40c03600a00070002c08041c0e0009000050004003007241c0c1e1a2600304070081c10700601101c0d0b452 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 614143776 1250 614142526 614142553
    0x18261005070815090c0a050a09050603040c0e10060806010e0619081603020c03031f03050a060219030504020f0f01090b030f090f07030c0e0c040509130b010603110d05060102030705 79
    0x8071040382c003030b03d240722611401c0d822490a80c40c03c80c01042c0018040382440c0d5030f228180c034140d2143d01404280316640c000000c89030364a000440c851442596415621031410540251200f8042c0003054a90065207042c0220ba030701c1445c4545c048070900c6c00700c009548035030110304244541c00302580204c45070004000e003d80c0182134540034440030600010711801c200c1d0120200c0c0200615240180c00c208040345e0031480f003c844031011900d2205054404d6601d56400d481c01041c140c0880c0c0c0031360081104c00200070b010300c1e900345500d0b543c2800c0c003c03071401d5800204100d101c1366880f482a030010703a0311180350340300e895007102030615000310759903a041440000c80d0280048481615a100300d44812030800307000701e00f840859074084030075641ca03401c003174080101480040420b140b0f12070078840068980d44014605000700310214161101130a01e06040032901c105030803030024542800220700b024030f4490100e1321001c5d080c040002c2d442c0c4407400102d041d80300c2c01101030164812152a08110f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 614145026 1250 614143776 614143787
    0x20a1b0b0a031b0908120a020102120a27150f0b03010e011a03120a031a0607030f030b1903020621090f01050601090e0a02090301090c0b0405011826100507 68
    0x20318212500c100d903e4500030b141119011082c1c09000010341049142e11451003410001e445c01701c41d41c0c0009402d00904c444000703507241084544c100881d40701c10110400301098441551503881c210002866031526403140b42c41010a54402005a90368640b41100882c0316070000e00d59500040007401040b43c0088910301808084102c503000e40d00c42a1030307401d00c0c980001c0650310440c0100c4440e0070250208004c0d0018900d4501c840c00e0180310361403140c1030b540c40c0c60040000074486d4480c0c0300c5c2e000c07000900030104c0d880d0340703141801091413420240c001007401c80c1110071240e04691095450b09101c00c0f0010389404e0702c1001140302d010700b080c491000350204610f1390512044008100c41e41e17550004442c100300900c1859000043c0c28045030100c0159001818034a0010f40041402242951420900341990344240000d001c0410140215030740203c40c1100f2007a840780000c8010b0800c034200c0010f0b0140107070042d20081c5940c1c0c8415044003445951010024114204803500d4808005480d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 614146276 1250 614145026 614145041
    0x60203070605010f060c0209150d150c0e0a1a070b0a05041707020f37081911091b03090106032d1103070305060103140c0d03020a1b0b0a03 61
    0x501d1418040041441004603040d60110b80d0240d440c0c04044105030284040d5003c06000c8509801c14852422259182c21600340b8030780d4441d1800a010000c52640345080300d00520440041090743c102245155440c52510420b807420001044c1881308010344140d45842560b900404044c0d409041000c1d0864550015100700d0040c1c01a0000b801c03110714918140c0301d1080001d40c416500a0f442585081c01e0000d841001d4982a84012051b1541064250f01c0c0c1e5460340c1810b413081c074507014008824140300581c1c1d80d0a11000c0450080a513a6980247e11035014107540a41041c46c000361116000300340360800300e40e4203c0f40c940d803810401e00841c040c1c5040e0000752424008894039808021000403c1508500c420400f2640070020ba503a500007800740c0900300c0d80c5482208004004a0030500c02540250320501034100511002d0303040e942030450341441a03100e805030b092040046a000305444400d654000c20041400310080401c020449003038200000c0300001182440c84e46416510218 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 614147526 1250 614146276 614146283
    0xf0d110301050f0d05072601020c060403091203020613080405120c09010e010b03180c130204090c0c08041401020a0c090f06210f080f070b010f08011401060c15020406020307 76
    0x100b41c0030300ca43c00d004003150011001005540118810400300b03080400e204159000c44d1244000300c146406403d00366000f80107840b1068000c581031004041c1c20915203070041c1100c0241107a00c65240e00c019403100d50060658000361100b0a515003041000703822200940340060203802580103918490760b41d016050032072405907180c00000314000c5070441540f812031394007445081c0386680c0e5404c10119040d400c04101c40502c0b582c114282c0f076664040a0429054000d400181c41d07600c2d1100c241c05071143c54407040184000310050b0703004100306404803800d40c0d5a090410031940b1508004074502809100041c190103085031010a808240d41c114401f0b01400d004280065900d42e52980d2610107a020b001d5106040c45d544030b000204400004258a07000300307d0301d8201300e900403404e10168001c1c0030031034410110b2001072110503800c40030840070b0080f00b0020090820064580360103100d040c048c880072b00209810034001c002c80c040c509074280784891002d44d201ca40c2e52001030f40d281c001d0f034003c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 614148776 1250 614147526 614147539
    0xa150810060e0d12020708030a0c05100203060d02011d0306070507061508071208070b01080303040b2809110a0f08010e1603060b0d0b0c0d0f020307020703080f0d11030105 75
    0x200035104250070520407000a04894401101c0e0f55586400c0c101301c2915415402104000500b99006101609040078036495081100341d0500d000740c02c1107004e01c401030f6070a2040c401c4c40a6030722070018554070380740c0c20f0034820604000c82608800905403a01d03d541d052044008111003198070402070401c40740300302e005200709051106105103041c0030740108100e0307a0226404100320511b440b0602192030084c3d0120f443c006464403800040e0001743c004261551001042c001001101019a640100c500d8008084519096110958102410610f202c89511140d03901c05101c080c2d152204007100080c14102a140e40300a00851003940340b08002c1503501c0e10b440803522040c00300d000105031010540c245c0f207031030544d07440030014140c0307541c03a035040907400c6280400109070f82c40042c01035100c094650349551203a8010002d0b1020402080d100ca4014414010b0180e00000c80a0507203038007942ca252108040d0700c09003554059210001d0701a400c02c9841180450904010b6058550503240f5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 614150026 1250 614148776 614148779
    0x1815040c0c030806061305120304060206060105030f04080a200c040e0d0c1e08040914011703070b07031b0306140108011a090105040b0c2407050f0304020a150810 71
    0x80d20098800706018001c41e1072240010f02c0d902d010001055a8841110302120035500c0e50040340040244200001d0f0540c0300040a01095030104002e590050091800700c0c034500e0000840540454042c000801030b40d00402d800ca066805845910103515200103010819900c0500c1103a03220789901f20707103000c1c40c64028550011240801c0d0000d0a45440c2c0b075400b003c035040c0ea00c00706221100318046100158400700100003a0480000b0302c024185a880843d40da104a81c64614901c8180c1c000034082c00d141050b980840b0001c026590030a801101c6654242e540940c2a0042c205040161150030004182c40c506c140d0560b00040a0f038180940030402051000c2c010f403202c000a00440007170008288090f240c41102d00d0040a0f2081d040c50010304042e524400001190069280704400b85c01101c045640f10b8140340d82c01c0300c841480001c104260601c02d001809600c5101c148107000c01000000400b592146020f500007008240e56075080503070281401000140c3c1510030503c2d940704030700c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 614151276 1250 614150026 614150051
    0x111c050306091803160f080309030a0206010609060905131e021201050f0108060d15060605030a1802011b020a050d0b0609070206060a0512010f0507050d0f0608060103020d02181504 79
    0x10740310349451503c000c500d0403803407008840303641e01c54174002c44548a202ca00400040e40640184d401504003c000710b85500c6018000380c101603058124404100301002d040040035800081c40c012a0001d9800b0552803041c882000003411801083d01d000061400141c82d003107400e540180410351040900070b0881c1d0301d490400c0000788203031010600007040c0101185840c40c0c9443d407081814801c54041058113110003043d0155801d95000c40c0c0407038008420049100054080d000c01c001203c00808123103801b0346d0000e8400303c900c3c26900041460030b841901152a8a03441401600000740580c0301500507140400503401d044400d2130150042101144203075000180d1a07026020007010300d040b02d8101014410b584040d0701020300a5920346021210310350352403140e580241e41c9541c1c1c40d6620304001c025040bd483e040c1a4241c40300e413612030100300303071200403a182e03040d603504941d01340106d4040e00014080048a0307000b503454404000078468a03c5080fa8903814800043d10b081c07142021405 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 614152526 1250 614151276 614151301
    0x111518010e1503130b0406060906050603060a03030302030712061712071a061c06060e06030708070905090a020303041e0b030106080f07270302041103070f111c05030609 74
    0x150002e810080e00026102c0c0c00340d111014541c041500004100200b50a40364010b40c40b40c1524203903105a80c491090004240d07a00510003e004152595440c500f0b054001ca113050b10280310180130140d010001c1070880703116940400e19008090410311110307803100c101d00d0421000340300920b09840703241e4100050512030015a1603198001c2420740881600c5134104031040c50080480da4010504a1090300303580740b109410174407c0c0100400600207007429014009040041d003064480e61010340100944900042c17882d0035101e1011000c12030b92a0b40000030714206035600000e501d80404507000c110340340403840c01030f04001120b40c2c0c0d88201e541c13148246514803082c0500000a032220300003030841c40e10080c080c0e400408600d4178014001398132440030244003201d43c030309014108041c001c0065142602030304603800525015941b850030f14040143c0248134482d8607000740140e00251105c03015003070000e4031020411000c4a00e003150041c20040c440d0303200b11201849805004040340c0d0102591 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 614153776 1250 614152526 614152547
    0xc03180a030807080a030f06090203070908013c05010612111608130306020301080c040506060922141003060c0206010311010c11030114041a1005090411151801 70
    0x180c11443d000094840202d198071070800f85050544810a000c440c1e00d46102c0d420091035078220060316410f0480000344100c00c942d0150801d60305202d0001d845d00c00d41510350810314168030420604542d030360991010b09441190b00f00c91a40b401000060b426001040900c1c1084500320030004101c2c4691014454041c99642207aa4000701c80032400040c0c0708401015030354905c20b5030700601640c07540c50909980c4260010003040d00f080001c40320b942024000d41d90410340c125902070403d803208000c515092107190450b800022251500c00002000780c0c0464801050786190302c2084c501680c0080445240303102c222040d03441c0046004280b03202003a0b1360706030f9034060994150045e0300801180e20035800f52084d603200d41010080240741c1c1d070910480948030541d411405140ca4079040070160700c10ad0640f100380ca2600c440400195000b1498070b43d06807003048802c10b400da00c1d80d060420300031000360016500301e050711440c010000c01550151844400c0408408100b200c50801140c103268807 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 614155026 1250 614153776 614153783
    0x519020907050307050a0e0616061e060506090d2f01140a1d120604050106050f1c15322211040b0303030a02030a0516050a080405010b03030c03180a03 66
    0x20301c81500100c2c0f04541c00340c010720000b031180c1d0030042804001c0038298401d01082b54207035510030f0180b088030320601c80546a00c0c5500c01c1000354602d4080440d4140c403d6800440c400d400303190045040009441ca10320700607901c2c0000c0407054440000c4820340e00c41001509011403118220700d2000042e080865072200507540d07502c143c014840c41d00c001040003034200603034002d40c00010f5548018041210520441c0524000f243c11762504090100385c24810301154001da40e50b0600101c03107404080079841c446c0d0f1180c60040f910038400d6428004200140c40c8100040348220505042c50a0203001022002c046918044c0c0e6240c01741043c9012a150b6041c03590000000007a00204038003444d10345804501034400305004120800090565100720b8003203181030f60100901000503c1c91280e07980c010f15a25501204250100d005840703409100380000c1048a480c3c00901081020740001d04881070107400c883e00c0c0c6480d544002c0d169040b900b160031b4048200c0d04802e456141c00c1c0c501c40216a007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 614156276 1250 614155026 614155037
    0xa0c020c030a060b030a14101a0315060312070503120a0b03070b130510080a0f0e0a03080618071e0c0201050d051005040c02101401052101150603020703020c030604030806040b0109030519020907050307 88
    0xc122f030291560b10041070150306000c0d07000503209404c000750080228500c108040d40c0d50348c00d00614211a5440941050f1b940b41c03501e4465a59510001204025201c1c00703100d442c0c81c1d032000840d81203a08025000071303410040140c02c00c42070f140c2042000340103840352041031044503201e49141d0b0442d00d20402140240e80040d00804c0828040e2102e59008100a072220814951010384485908402e4810078005590f92030a04203004e04451074080307e255602d040b20108100da00005c02ca40500040300c10b44950700c0c0041601030070400401f1006141c05801809440e840e20340c0652220a08850010307028104083c0f444001c18002045041e03400041420b00c903801941d04110540c2c070000200fa100b907680d0b091030700c00081c07040c40001c000e040c0303558096901d06403854000d0801180700c41c0c1e40e000340d00c00800c1c840080d8204a4507a032050342070b20005103038130b04000125400642644090403a009034610031030030039049002d00a22a009a0780d0310010b40f1403403401c907041c0c1b1084490400044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 614157526 1250 614156276 614156293
    0x91a0f010c0201020a0c17060705041a030a02090d0602090a050d05030a0f09030f050c150a0818120d02031503070b0f0703030b0303120a0c020c030a060b030a14101a03 73
    0x60007010070000440c010301c1103521940380c0e40d42d503088007171164018041c4d0500d0045640d006d540e00b00600355214207036107881403c01e0b10b084503021114040e01c08103c510000800060341048441d4160303070340c0c4480100704416100303003820180c001f98410445640070307003c030410100b01030520102c09551958084001e44c60011030b06000c694103030312506441c2c01c1000040700080803e05035444108814001c1000d006000e100302e04010350703000c10042c4807040ca40d0500144840a40010b500c942c8545078042858911520040050510a0580f5681450f84000c200c1d0003450540b1760140d44282a483e1481020f290041f08160b507929007403244042c040070800210024006240c0170384040c0c2d10908000c10908100400a42507410006074042c1c598002d404002300301c7d5075800f85401c00e11240c00545140740c08080440c0c1c680c107000340084c100c40d4450155500f26103040188104a54000c01e82000100c680700700e060701d0b40685c0e40f9501d419801e01c06800230021000c404001e00c100010014140714 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 614158776 1250 614157526 614157529
    0x6110c040b0d051e0609030a1d040615050901030f0504210917071811070f0204021303110f011437050712170115140f0903060c07020307031506030516091a0f 69
    0x15162549da4116403200030009000209121303100001043d5100c81d40c55100207000101201c2e020703105603145e542402c0031311010481080c1c0003c800b040710300820b404402008002d854400403580240e024030755039080d000d502040443c801050300d4620021002e1607525820007410b5840ca030301007440e2450b08205039000030f0b501c1002c014026201610250034204980c120501c0c80781c0a90058a0000e808010b424841c40d1078503561101030400d01b0452003a00140c02280d409000306600d080750304140110015454807190103150300d081c8a034229200000070710340018005d400000007210328103e412860803150b030003003900c80e00301d000000c005400ea0781307000301d00b018a03039806d40b410041c4802e541100302c11410741e1004081030140c4066980d50ba10405080c50714060f03008111041e5100c09100b8900140e5002c034070741d000c490308407825101d110946940103006000c9036100402c03d10a209451082c0c3d03890602c0c0e54200d0320040ca082080c03441c0000905040d54640b42800d6202c0607107002509903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 614160026 1250 614158776 614158817
    0x6010914061c082a0604170903010209090103260901020607034b0209060a0c0c0815070305010e04030909051504111306110c040b0d051e0609030a 64
    0x81c2c0d07a070403403603020150903118803500ea800b84030624451000c183e0b044e0b0014030011260360a00c504c0034020302103840d00c0d490b91070f900c00104100c025079000000e035148855909405031221804020904996540c0d2440e000d4200c24046401100810041382d072060fa07840c3d8034098460240040c4c015182a07a15040d00710010003400392800c002604c0308a4100d00b202c014910445034040080b0a10314083c40d01c2417041007082d020940a002c2801040201c070140c43e08029288041410305060038010401d2070452036a4078190800c84541c41002c0031102514000c0040a000b000251070410059807070b900c4500b070b24681110003801050300e5160411081c10076600c00c0f039100d041c486070450a1551200000c0c01e80d0007400359900c101740f01046940c2e5041c2c0c0045920024500d5041540a22406c01d11558503510010780240c0f1685d41e420350398801d51903412190701c18542c0803003901e260901e1503490b03801707250141c45401ca8a10030540090b16500d000402c0b04c0070409283c8440c03001c4a00319400180 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 614161276 1250 614160026 614160049
    0xc0f0c0f1216030806040906051f0801060503031b150403020a030e010c030c12030b031f0c020c01140703020709140703110f1b0f16090b09150f030a050d020a050601091406 75
    0x2001550b400b090008209a48141070007212405c00c6081c5c0f168101c0c10705188005960060020cd916014080000d550300008890124810418035002a9a000c20250a00c251200003610010f00300080004050380402e00c007140500c240c40c0c501091484a0044840220054004000c20b500e03018210100c0e8501254800400107842d001c42c6200111010a00f40000b00c008240c480402c0150410110014002c0e1200e6002c00d2000702241c00c1544002010f26261000130151030340006039490070305200b400700c50041c1001980511005000c400e07040040e00044481d140020702d0020354880c0100c00380121400b215510004c10f04080b0780d40d0b080302152802110012161103214508402c00f14280032080804100d1340e9241c205c4c40c50003d1640c261010844864801c440c4441080392071060307566018072208040d01c250380f078107881102080c5441c0c3e880070050041d1107905100d0318000d1740010902d24141c4103006503105644da580c4c60300c2c103070342413168101154140703d00010202c2c20300b000b035030b01e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 614162526 1250 614161276 614161279
    0x80f01080c15090d1b080601080331030c12050c0a320d0602030f070801180f02070b012402030f120702070e090714120a0303050c0f0c0f1216030806 65
    0x820209a40e4440081845004900307640e505c0c220f10820500106001c0140105045000f071031400416030140c240500c8013100b180741e8220350310300342202801242e03120300182d0b512840c050003142d01d40c1e0f40c00c03649041d5150100c5035446840c0b0440304e94201f02c400c2404070b604804690b030014800350b043c0015100c0c2c01e500c0380c0d8082c0f10688000030a54a8951001001e8001d103401607980c245100c6a14090701e0080500c03091110781c04c0100300d40070141c0280346688520140000380440851700c444007038401d40d040905503c840d400045140c12100c2f260518103904226480d400300741e02c54050340c80340192009140b812030280030250040320644030455101600c2e1040e00c202c141c85482d0f1642c03220083d42c4500d61030340185014041490110020b04144004690888100c010380207595074074104880002e04154480e00412000c2d80d10b542500c41c207403500300101d030311103181003045613172100d030001c03540e0b414440c0e00d41c106410113603c0e00311030300c02807500f0070420351900c9030714155003440c009404070303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 614163776 1250 614162526 614162539
    0xa030212010207150203042303070f14060a0c020c0f1c030e030307030c0309060e030604030e040209030307030c021e0307090e0a021806100306140f130c080f01080c1509 74
    0xf4000104003100502000c1c812050041c3c40b4186070410440c4919880440412403610395402014400000180c4d1b6001d940f00240305860555032504225102214482820b10310a001c02d0000350401a00b001c2c0001d0300c65800c68410b07105410801c80303000c1e845614240c1100291581d4210001008541c2031040c0c060708002628000700404640340d580004400d4001030002e40b0924105540441072030000c14551900003050b049800000351551009400201401000c40003002c8584594041e00c81503600201540d49503041800c0c040c007510101101284035100000003807600c0c1c840c0b4007000d08402001b5000b09a41030400c01940002c1600300c00401d6544164501080141e40b10302d480e03203144c12002010740300d608002c010700c49280c11115040e400e060912200307006c0c81c83c134820101c14842c800c443d04116100d4900c04100c00d00d000143c0780082d14144410240001e8000c403080e40101001c42142070540e03070310042c1c641c0b83d1980d17084140e4050b004200912500442501815038010f0003080d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 614165026 1250 614163776 614163787
    0x61f0b0702120309030327010f0e0d0201020a02090109060e0c0c0a030f0201090206161a07080a090218040303020901020d030e06010b030c2811070503120a0908070b04050f06090a0302120102 83
    0x6d00e036400520451a45d289042c807101d034070100070900080200e20a090070003640810b944068000501038078503034014441c0c09409000d44e031080040c80c00c0c05401400c003069558450421001900e054042c07900c4030b01010020854003ca100304664184413014060301c0031a405940440b02c0b103224a46d40b508640d01ca15100c00540d64090080511140819421100fa2114a4150654a170849c0440742c03d031140402c121140d90040e000c00e03031004d580d0030002003141d803510006858125010504c26402001c0041204054055004080c00c0c40c00742c00b240c4170300d44084401c50643c0c0d000f078400411600200010003201e401d0202071074000c0140500385040031801c0302202011140154544a8904000c2c282c540c201e40100e12030701f0110100018201560801e0b0204e075036044040c0e07000d183c00100080e4203203120f11030700c1c1c070002401d11340c400d5a4059903104540242a04103000d1507100b0070810082c1c0c2d40a00d45001200c102980252403500c19510b946c0810110580c113401c080c0c5555000c010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 614166276 1250 614165026 614165029
    0x7080105011e0806060901090b0d1401140105100c060228090303091a0403020d3e040e2a040c21020406140a03060e09061f0b0702120309 60
    0xc06001e4a41201c440e0701140c1c244002882c0e256103a40f09040c00d8110005000f481c0e11071100080c107449140001245412032800418905004082c1c00f800210498004a1400340f040d0410449a880311840c1c410f281d80f910100107401088503410b00214120800c20000146203801521112262503a50452000701070090501c00041c0150700e400101169418000c246e04062110050500103c1040e2031360003110210919115502000e44544003000c60803041004e80702800c1c0b80040580180304180c1c040103400f8085608a40c025980303080c4188980c00d05090511a00f507000822100924100610081c10007411106107038803c240ca00c1e0348001080c84d00c80740116410300a80c1d40e00c800203000c4254030014103040300f0003904882801080104a01684002c150500b080302c04645a40d85403180c2007903004110503807100b0780da49444410840c003110003007007480c4980001034a41512030015602400d940140d030292400248082c041c10001d420030300ca81801140184045a02e807101400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 614167526 1250 614166276 614166281
    0x150c020d1505071101060501050904020d0617060a0c03050402060711010915050a022407050f0d0f060305060a0b21011d1c0203120c09030c090408130e091905070801 72
    0x880c90340c1516218000d100820303500000104513030502c040200302c290704080000b0114480d000300130380b04e96004140e5011310f161a604c00e10007045c40c1c8564200584207045100d0700e86404484148849260000400e0454080d001d4607125544c0109034501d40a006e542d04a000081c141c1198104280d01e4000f1552014640145011060580390396407500c07110300000340303000f60194002406018001c0340b58030020861580342e410010034184a900c0f141e80c8103201d111402034004060b81c5a0500300548110159070384004190303402001511516a150070852040d2415004000c0d00b0186005400443c035000000e41800c0e10041000810034031045008c402d490601080c030031550f034004003c2c96405412000d083d42c044070302800554108203400d101302d1100131001702088084500021000e096550600002000000c010181080781c102800c1c04240368003c04000103040c02400c00c0412021401c429081c81012140010001c0304240281303001d40c081e070008120361a104541021034000d40c01e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 614168776 1250 614167526 614167553
    0x9050c07050607050301230d061d01090c050f01030e0a12200601330521071709030f071209030210050c010f0615030c02030d060303090e0907150c020d 66
    0x10b54131140c03654109040c0c0c0140c1e100c40060114002a07400a900103078459a00d8041000c0d00442d000618040c140921750441c4c4426060903019481d00812904020000110b0021307510280c07810b485c1c050301d5100650032101c0298480c04a40c1c0030341c0a43c03000800c50380452058080900e4801000e40f40110514107050b06801160102d411003030050156035200c101e003ca1101600d0388215008005001034840c3c0c0240e82d0700360302080720004040410440654010022504084000076203142c184d2000341240c25074400c05402d070b4a10030104842c040d000041d103403a050303a419028600155a03458281415001ca501400c6c00040c4500001607582c0c055a210550754684640b82d840251700221821104200c40b588101c5242c004140104424032003a0801e00c209420001100d00c2c0e80780c01603107503001d803540b40200c690800c1c801004043c0e2007452321044a8091382c0601d4a0b0700c070065400d80368030180c0034685550f1020409042814815504401154000b0340009040e22840e00d407050104c510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 614170026 1250 614168776 614168791
    0x506280312020309011205040305040f060f1404081005061206010b040801052505030709031407050a05100c030818060a05061207030302030406180902040f030203060a1509050c070506 80
    0x145081081031210500c9a6111a0624800382d0320380750b8960b002a00c96103451000302c14140c0d441c8001010107014901300ea010301078500a207003115a440000600840081d504000003407203199004c141601d04000344c800b6903940c48080c15807002d02907008401403400030202c540c170030603180d558401003c06109050280c01b1402d00b4a607940e042916141c00d54101804003554400c1c0c1054131045296010116980380103980740095507a29800c504495585454002509140e4994502c514064000070f40c8821100300b40c55010b036090b6035800300051403038841c000741d01050488414000207031150203180d034808000750703485400c030031072a0905140807422202180c54550b0354044c4900303450031010003086c081203880208021130544c7d800a403280110300c41c242c10300c09042e41030b0606d01041c81c10318014001d46c003011074440e640c0700172256510090740b00a0740a0f011311000300b814480203004042c1e28040002e0890301c0d50b4034003540da00040c840104217250650742445441d0000f5400d21610307015059 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 614171276 1250 614170026 614170099
    0x20c03090402120402151e030a291008010b04150507080d0501091a130f02070f111014040b0a0c05100950031303060617100506 56
    0x1010710500c90359105a14180346c0c9000184480247e00d0028556a62220342400316242c0740d8503000b01c020098980c1000c4010400d46aa84211a146090b22440c86a810844020349680000c1409483c0c090b0b007800303514180301c82080181300c0c081c8000c1801102c081c180c5003d41c50040c85498140081e0042111980f071a901c0c4c07001040303515558010035005c4a80e00050825107081ca078005071402889482814080d0b0b202c0e801d1003661005681030f58100c0350081c0803444c041c3d1940c60305405c01c04105500381d2003601207000880070700c0c0c410104000b404007011103d07841e00341095050103a03030b0040c80a00c010807009070741e000009003040c000e50b01800f20340900400c101707034140380880c403401070744021444140410960744010744195103030480090802104800b4140c1341b9140400310010941c4d060039510000a40c050120207140104080324019403080000c075860300c03c17880036900581181c88840d8444ca03002d83c1c680b4031b00e5215a400100041c04914034400000300c0a0b121202060003801100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 614172526 1250 614171276 614171281
    0x70b090f0c0a0605070b18010c0203091903030207120203010207060c0c110627120d2c092410030b010305010e06150304032303062103030a020c0309040212 68
    0x8100700c0031a003460119120100342c0d0418038010540c1c01100005030007014800045030004450455500961007e01c000348038100c1c1420000c0e5882d4030400515009800d00040c1444000000803103d050742c1d03065018208451900311001e500c00d0800c0420303641075508000b8540020f205106100c031030305013a210071f410710701c03541000500c0464a6034558021102000f151100c0301d90840803c0e9a49120f8010014044d41d20003c61a50441a80d460f00d00d0302ca24046511215001021403450680080703c20321000e411000d50131300c140d007486400f508171600101140020b802d0000f02c20b900200d141b004060210b125000902c981626007400d4013203542c421055a007540e0602075640500b007048000c41560500034045000780340d1682122240850100120301098416040d03072010304500401c010f040051028040c1c029402601c0325441241d03841d58030a40c03e00c0003018621800c08480285040d039a0354001840a50302c210306846590200b00101c00050f66544094040c0f0307542200c0c0101c00f031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 614173776 1250 614172526 614172553
    0x304060509060a1401121505070917070605070f0501140103081e12010501051b010203010b09040501140d12020703050a060c030c080405030a1805130c0e01050702010203040e0606070b09 81
    0x211003d48074030011820b2003e000359040303003015a40c3c1100e4100d050f2007654090380c103059844172011030b5138204403401c050501c00301d607a00107240b40c15246500c40c031003820740404213140c0d07982c5602d04c114008220144800c40205000b03c50080701e4030b0040c400400d0504c0341820641d07800e00240c00c02c5071807a401080c01c1d080c1c41038003440700d00030300417080f10030745401c032266010140b140c014031800c1c5c100b04000841c00710400f400000355250b8030303241000b0b54595071030380c8041d0701d26000700107594041c1d4941400051203001da101540b58084025202601180950f101c0b412514450f528140552143e5100000042ca00300410b04605006075400110308900e10001000e89904062500c20028010300384070100314040100c0d0365000c04c904140f01c1041403100910358030709080d80155444109404014a502144d401409003c0313050782d22010440641d00c0155403500444001a00591081c04280649814000d004e40c01c98402001103050411503039914140300303011503100e00250010700054201 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 614175026 1250 614173776 614173783
    0xf03030304141b0a0509040c030503040b07060f02121308160b0a0506040c080c07150c18090c050d090203030702060a0513120b0a0506040e19031206080a081b030304060509 75
    0x41030380400c01d0f04400902c400660032484500603248201103840c0482c040203402e4089000850744141500e403581e03035441c2841d10720340080700700f0364280342030290300d211030740b031501c201d4610000a45011400d80c4582c402a00140013548080707805000800400301d40d982d09842c40c9540034460389a00041d07240110302d910907074002a0682c0c0c003450505000c065529003141900c0d901401d800440d030345607041810b00105041b4101c0c05182c0c2185404069a4016485000048840505400c0200c2d4682c0d8154250880304401d41c10380000703400740080b400c04910340e0080c561550004003140d0400403180c001900c1640700c2e180c001e0120b000085c1c2855106441042500180100c05024400303c0e46500c891062804c014030220f01f0300e6a030070008003a035032240d1041550000e007800301ea0301040c20750f20a8483c200719070030a40101d00c1b00c9040d198112080c0c0640d0741603a00f100c000c0d20300d41c103c0d55110300268220b01030501c4100010b0f1889141c81034208040d41c40b035070107858081401d040c06a4020308 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 614176276 1250 614175026 614175043
    0x405070519030623060d0503041d010801051506041707031a090609010506030d0f02011407230403020d0f0201093f020907110c060c0d03061508150f0303030414 70
    0x10001e00d0b030740420704500319010410341d1050080e0f070216806c540500d401070645c82240c101218102d40d0300d00c51400701c10b00c4042c4034181c446401c020400c5032508801c40c0600d080d02e203441648458100011700c107014004011354030251003241143c0302a601e039510154201c03900d000a807811100b00c0308002685a08102d503d800c0829074001b040103050400100c0e8852070100109000c3c060303501004581d2a10075071010009040c80d040710803083c03d10690082c0321503210b55510100126500c0c1c11208a0003803012541101ea0050000c512506956600b5035078040c001d40a9050146132400003801c4100c0c2203c0340b090100507000754010b0f40340781040b8504801042c40c2200701140d008541e03001620f460300d500385c0000490a10070500d04031030b1106860810102c0c102500841c0204802144150000e0191000382094906022441d102c0d0320303040003104a080d241000420590203e00b4040c0c0c8880324a21b44030025004c8034004403828003007465980f05650861b10002801100803104030103104884 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 614177526 1250 614176276 614176301
    0x16020313081c111b0d080c0f1e06041202010b0a031119061d040b0616120c0b07050a0c0c0602030c071e050103021c06060f0210020f03070804050705190306 68
    0x42e050b543c003400c07407a510000300071528850b200d0002c00c500250340b0050503c9055a1104800b540c03683c0b4041055110700b04080210460310800300241d06620075110701c5214480f240000f811142e803291282280090b5101d249010365507110610701480d218200b8510246005010200f0140c10301e1081c0000400042c0001031f000d501500b041c400c10380d0000540e82e84081146c040942002c09000142c001d000c010401c40d0b0007030740020765225203a41200c500004501480310380c84102c031216401d032207111501e04010000f003014400070b000380d406000500301418485c44c258281302810f80c3c03109d450079401d401c5440560300100321b500501e08100f00300c0010b010040035800b0411008a501c10011103540501ca042c181c0204031104c10004089080404151a0b58240490360343c6120140004807403948900c01070044110000301a00c42e4001c4840e0b07030245001c10791455881e140115000ba0028204490354001d006c0300007071665a00401c0100b008114410f003840c2031451400c0300c03c0f6047e0f80c220a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 614178776 1250 614177526 614177537
    0x7060609391b060b040609090c0e0c09130e120318010623031203100f0803071e080c070803031501020a02030c10090e04030305060f1816020313081c 65
    0x141c5005500c001100548035003101c0c0800641100d1030f003200941858010540c00c245005000a90340f40682c01804410303028201740107656440c0c090200740040125005500700e5070400075002a4101107550b001040e10301d01c0b000030141003440c815801c0c107480307400030100f408001c000d0140788090040e06258001e00d81c1e008000c15460100c82469400f031200466849441000c840c0a43d83c5050200740e001c1c10060901d10b03500c0c0b410006802c4060340c076010b0700b40e6192041c0804901002c00108881420780c10001024080c0810a443c91300b0380002036017156046414003440342d4082c01041402c003e400c21744050354503440c110380e1074002203051140850456001c00200030251310045a100c0303154105030395800039100182800d8412103001d5101d50405180f085c01c2006041c0e16500250140c24105c400413500c1c1c0700c03441003003103d11000302040f451800e5800070460004540641e8271001005005903402c001001000040707101c03582d4007842c220b41102d0305451800e034ad00c1c01911242c10060811 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 614180026 1250 614178776 614178881
    0x30306170c060309030c1e0c0a0303090509150405040f02030609211e131d0603060601030902040f1a1507080a080c1b101103060f0607060609 62
    0x4a076920100d00c4034890241000102040c84803c0034021100c050f00010121b80301d08600003040403404e5608080080513000b02807400f4038030b04e80520307072004403605559944002410101041a021000340900702035001c92250b241c51a207d500405203d00d004100951082c003990051500f00b0a00402b40c0e0001e4021031411020202070340c6200c0d40740000c1032a0f19841d21000b800000d034003044101d000803030b1303e03011540c88220707134213540c04400f5100340c200c3e0144440041608407080394801d560030741e0306801c50390000c0c13800d501c00d03444543c1c140d0004001113800f48000420341c084402d140b60010380304d50702c00f0402c140e034101244140f001d5140300703480d585801165281c4105038000c00415508001c80100400c004c4a0a5815550b00c80703500010001000c00e4080550343d1040c40c000c01ea00c8940c1401d81502c04003081c1010350344a0b0f6806442d9403d11315401d002c105056100000c04c4803a81e84d901000310b660083c82c41382c14540480640e952003440d00d0045108180c04401c191110710840038000b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 614181276 1250 614180026 614180069
    0x1b0408120c160305030d1113230a0909021e01091e09020a030c08060109050a0501200304030b1e16050703030f0c120f0605090c1b07060804030306 64
    0x86031424445440c09a60325000e04916550030910745441c0742122481400c07021090000110060986501e1880100669100001c00044900803511541c0010090300800c06c0400200100304c480035003140f40001411035000d00080302d54107290032100b042581c40a1060031400c008001c00080000003130080014520079000070a850b400c1d00805030241008410904c21002c042000e601808110b64155152404500000d0082c4554440b80c4009503a40021420650080c8000c078182d840140214200c0ba0401c801541c12801d603407204e015981441e01d194003070040c103101074030245100303044995860030402a980a9101d61189002c9196540c1c0140804005048a04041c00c2e1680c14440c0c1c6030085402e06500600c5c00c0d0040d41c45040c02d00c14044090390b88800c56003105038111104100000050052004417441402956001220000400e080080190103050444584c50032820a84944103000d400d00045911600101e00b8000074003003010380500440029013809041d005503c4500c45 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 614182526 1250 614181276 614181283
    0x14040b03010519120f0308010b0903070b03060a050301020d0902030705092503020708120402150c060c031b160b0c031501030921050c07060906050a2d081b0408 70
    0xc5042d200f407814010119407a00101011002000c071421501030f01d0585007801c0c2290305c5101e204400052180d0004a00c00c14582e05881343c080c000b030f002302566400c01c070800e900c0ea4005401d495003c010b00c90002542d641c00d000030a00301820603008500c518440c814035203400015000144540d00020400c41c2c650700b8852000c65440f1081e03500618801591800d400912444401900407100054201c1d0340f5217444840c03901032072003900d20f01007841601d0064042e5009180a42c4100d8009c0e00104030117500080203141c001007005085111008041040480b41d40303c44c152101060301000140207200300040c205078051074403140d5030301c0c601d05404404103840e08038480ea8141a5100742d9003040c4522116070f00040307004401c945161034160303040903080b90004000f2919910460b100868218810315040003210855203400b81880414202a501151544c0c1d01d0041040502d10903c5c0783e8410b040400b60a50301503c2d482114101001c003038a61070f880d10004840340c84104800c211004000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 614183776 1250 614182526 614182529
    0x40e090c100503040f060603060209010f03111602060405030f0d020c04060f0504151e03140a03020606091b0a050301030213090c0501031a04021b06180c0112020d050103030e0114040b0301 82
    0x2d25040750340356580e2920148829003000041c00f01c6103028800b1080042c41e41c01044000b80c26200e075511014038000c114156511801c0a89009209100170b84045081d010b0f80092544000c1106041a88a402285c40c1c490031004c0c0e498240d000c0018005216014001d000041d202a6418410281402c1491600c0030440c481d00740211303914080200c0040810074060007034002d144800b000c8840099000340902301a01040c3c1d180b560803104800817040000c4c0c0c0d01155580341d0060300d010fa03255010001c0d038101c020188542d01645080e581c40c2400000010318042080783c031002c0c1c42c1c3d4158014001c2c0440c9500031b041000b440c20080360040b4071001d1810f41200d4092070081540030340c48034010300c0c4480180d00250081d0021800d503640d140001d036003404200440085501d281c1d580a0b8000c003541041c800303500d4942041a00048651080d4003802041940c02c1001d407a104000700718108803142607005500150068592103030642c0c0c0685d80341c000b10381c50031119042038284090700c1d04500c010f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 614185026 1250 614183776 614183809
    0x1b02030c0d080711150717040510110d09061b210c03060b0d0b041112040602070212060403170a061802090103150b0405030d050a0806090a110a0302040e090c 69
    0x20b0000a4a000d01c03800e40c1e607428202c1c0c20300f03072101d40000c4424244516401d4401c4404140ca0308144400c85960018062103507801000805101c400410303030900412014041d101c0400c42004100340c1411740d4081c021000380304000010b8210501580b050965501c1882d500801c04204450421060407010b80f014440c0c4100c0e0024408409240640080c030442c1e214104100000c54049072419065000c0d01e1203078000c0d9000d01040501014150080c4101245c00d410070a1140104d0046040c0c0da001d003106078405030981c411801c0c40700e4843d280c8201120120002009603629032083c544080b81d154000484240500c08203007010f0148001070411002c03801070f9580845d011341168825041a4561700702000660b80c0e03241c13034041102c0076501c81c0c01194002e129104402d11540c2c40b5030111003034aa15a0350340c2c00e43d51a06010081f40420141c01c0d000145c4c0c440103c102c2c0940308800500140c1c0103601c2c0180d4a81c9084806045071100800ca07001a4005030060342c481d440d000c8540b81e11142 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 614186276 1250 614185026 614185037
    0x1706070f0203031b090301150801060801020a022a040e0d141602130207120504060908060c0906030a140c12090a0503031b04090203010b041d04080414010c14011b02030c0d 75
    0x13001e80380039540500e4260640c50b42c2040702c0c030070022921900c55415100301c10004d01c4019200d86445080c3d11030f0310900c2005074448400c070003101c140f40707540788000c0010394101c04150f007080e00041c0030b0340c41c45c12200c002500801e00c2da000c1c440d0010160441410000d2125040c02e100d01c8000a010040100290090000f50842190020030341d0469280d00e40c05489803070207800c900c6c0002d00b2070301b09014490101e0301742180410b44400014003107100303254101d00746140298a40500501b50000342c24401c003162103001d0400d02d00b0074076198921030611710040315140d03c098600e00291080c00380c603901c2260407201c0b844000c90004011250b21658034292603d40f15401d0505008510655000d00074151001c800802c6401c10b0f040144123b07049070010225000ca0480740c6070f60040d007901e00500c1c2c14410041002841c031000c0414400c604141400582100035841703030901c2c14840d501d00352950350745440050400c61000b00c9501c022140344020340c104904154000d903200b00e1300700980181310 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 614187526 1250 614186276 614186311
    0x618071502190c030309230105071112010b0a050d1a190908030613050f0411040605180610020f060f06040e0d020f0709090f0206090d0c1706070f020303 67
    0x5000b0045214503902901c4820801e00c142c1c1072942d81c0702c20500044001940400000074008030b030038800501801c0101c00070050646203030040d11640d00400044400a2405102d000b10f503485c0000c0ba0341c501c0f013400020502c414440e04002d41864250007007072141140b051003002040c0084035545d0b019010a200d04017079150b081d04207001303c200100d80340782c03c5d0402c1346200070448142c01860141c0c006552024000c0307100c02c1c4080030344a0844415050004090018010488030321060760b200d04040c100040c1c0c903032640041103000c0303903c00c0030300c6041401200303101c01814248150100340c81d541c80981001d108040da1903850b64009032101611004980c007240080c2c0d100e9010310f071900342c894221f6400c003131001000f80d1240c043c00f0701c05102e07006034400000e43c42e105014500213140d01c060391402424241c0e080060036000401c040b9080078888100c0d0300000e600181e80009000409a101c940005000c5050f2030844020700f1442000464562400029000015a90845035000c54065500c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 614188776 1250 614187526 614187569
    0x604020706110d09050606420a050310050a050a030b091f0903170c1e040b0a170601020d090506030702010b040219021603050a0b090708070303030b03061807 69
    0x4040016100c0ba48903800a90050300b00c26561001c489503210700180d50541c0d68450070481e642414503e901019094000060403030202d100d000014207800408070f4481c1c40f0510703500d42807608559040b002240001081c4030300b1641e600c40190081100719044001141000301088680c041c0380710080001c0031402c0815280380d41441182407032107503a80c0107401d451f40c07006079601901c2000401e40100e100703003900909240000038114843c0d0407000c0587c3c0341c610780c10440b44000d0300030158440c5081040c400402d2849010300144178035040380c0d1790300e0040c880032196200c01a4010749141d040d940b165010600b842c0e0070514130000c540c821500503851750350b040c2040e40941151013801d54040e1000948440103803d00304840030b0340c061917084807020f1040320710003802d0070b055000160041c3d00491003a00007514180019510949820a070398a665594482514003202a0421030110782c40c0c1c1d01d40c618031b0030100b207040c0d844100500c4015600b100003e4040c0c848101d0f004104d2070410344402c0a180 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 614190026 1250 614188776 614188781
    0x20c0d110306042004060609060f110a12080901060e070509040f0c120e0109111c120f030b190b0c0703021903050607081504180b040b010618030b0604020706 69
    0x5200c00501074441c2c614140c9000c04103030440c01d031030295044520f6060303407a03030406114030b80c2580c005407504403d580c00c10340d00362400c842d56181102000201d2108590a841c01c4c8050306003944115400220302541e200044c028000013005010310f6850a40100a081174400d28680c00c0402c0b4100103598035640340200d0302400400e500100028102800003010a52100c0030600000020380104005800d0072200c90a80d1304220340036107082045180580d20380340c22485840070440518038000440c0c01a520701d41114490365086010801c41c0780d81161850f010701420718080f50403656000a00307400a55244617840902a8054454012803102170600e01001007a001e190020410380300c140c2c0d18403005038410106d000803102030103000041001c1c00d000b0f000541c0115030116060b0b52a40d031103000d1000400708640102081e04d4480074001c040b8005040310741c0282d004184520280d81841d1303001d420f0010080700071030140d440c090200701142ca182e1031283c10603012240540e07108800c2c14072802 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 614191276 1250 614190026 614190053
    0xd0e040f0c02070807060219081602030f030a170f0708041104091b0b1e0f19030203060103110405010c1e0204060b040f0f0b0301030b090a060e070303120c020c0d 71
    0x314614000d85800c0aa4002401c1c204039540b12084880c840e4856000700d88483d1120f5080120b0000c4c40a8807000608800150005070b94407075911903014529000a49401e1508001002d01e80000850350055603001d0002c000c6085003040e000d0850504884107504517000424040821901002150401550711074890703810320020014010b008160400c00550703501c106040355201c444040c0000c8140c61041650b140030a240e804910107101407804125584c0700521181d05888104140c0141e0340a00000c1d84050342940c0d001a10303460a000050107c03011204500c0c0360000070b000170400703a0790220b200c0c26100e50240c0400c6000305407601d040c45c00004840002d40c050304059012403074003045800707041203550b0300307905c1020680c2d20303c03c44aa410150294280309402003005001003807940b00e0003600014800111026010030f41c940008540c00c0c084000210303005050208281980000886600d24000c082081802c2d900300d40a0b64560303903982c8160040741141b03103210500000305400c14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 614192526 1250 614191276 614191301
    0x609061e08040f1128081912030e0d03060e070c11040c0c080309061b0c1908070c030533010303030c09030f0c0501030c050901021002031801021611060a020d0e04 71
    0x285902c400810180103030410f01e100000c0e101e207a000000780480c0004e041f100c1c400c8030a03a000d903880401d442e00c442d10100154800c00f495260704062202d41410410f00118518030f1341c0019100c1d040c289020182c280141078203040080c5089810042805c1c001c0c0101081c0342100c0020304070b6003802040e6130741c40f15100090541640403042240035880070407903d21a03001c0f818001e00010300d403008030080c3d0107a0b00481040d64804503842d90300000d00c40b0b030300d1a194041c1a220382055056521410740344403980040301c3c5900f11a0761281046070340c45010060710105803850b444006195041200460144005000c00d6240c000c40301c03107180249100005950840a00201400039050403e25011540b284600203407030242c0c407845191054094138103164059000e001d600110151b00700103500082e003034501e020403440055401d0340092000309004800c0c0702e825910350702d490800c900c12031010300195000b50400c0000c84002076001c00c2c00c480700070403400c069103562125404140241803880408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 614193776 1250 614192526 614192539
    0x30e070b07060b09010503060c03070347010e1e0a0b180a0f06020319090510081915090f1409010912030c0e130b03070609061e08040f11 60
    0x81c244a09a00716a8140740305a94000030b0342d13610018955100c4085405210008041c4042031010303204c1d801409102d2030014000c21451841002070700a840c002101d0442140b44686045000d6000e40300341e20010000d0034100020f140600104109028045103c08840725a404802d07151ba14106098050f20344070301160703125426284841c2c00341011100039481344500a0f40000d4060705070740c086041e40c00030350140d4100b01c002460788480300f9079178001d0350600000c01c101180586403103081040407070544e0350300c0311301b81041c007038640b5502e404462900b40d0364209000d400c02225490800004c868103540001521854000d40d08000c0510704841812032110a090149d00201508081c42042c010f01401c541c0c85074800c801d80c1200c2550403058042004411100c40501c1c0c907072000e102440717213400c0124449400c40c0000741000c0c1c55411900c04a1000c4800b0b0200d568004041103101440d40c0d54603040310720f002d0014118400c01000184680303802030110080140d0591011056800034002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 614195026 1250 614193776 614193787
    0x4060e1f0206070815032e151a03010506072012010f0b0307060e0114070209010314010b09041112030c070b0c070f080a0204020f0c0703150e010b090106260702030a0e030c030706030e070b 82
    0x64450030143c91043c0382c4001c40a1b00c2d142d400140180c0ac5034100c5000500d00c91909a02c0d96400c0c081c1900e03850349808500c9041d14000c2079440b8602241c00d00c403c520700005070144101c400c45d04175035114058a01a90103040148501030704102c0c1c1e001300000c2400c11250009860315402501d01c14054002c4d007000144e4000000c000100340d000210b1415200203020300c10040060092201007250b0181c0301c44030300001403c072414200d400c06401c20403071081e680703080700e809031042c1313409a107504c50030100c00002030744c4050941c10710000c0b005d0301e0203411010025240c0200640e8603420051301038882c40d400904440210400030481d000240110b06441e82c182d520f081150036020900342e03008141d820035001020b0360406204102031000000e003034050990030300c0c0302151041d50b003407020060781000300c148069442800311014414801b0350f00a55854192000c000d1100f05104100c46c020b0b4460102c0e06240e50b03010036030368141c48031803070300040c1c80082c11641c5242c040d00340d000b0103000b5400583d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 614196276 1250 614195026 614195051
    0x60e10171c020c0f1012050606160f14070305070b090105071a0708060d0b04060c020a0f1118090303070807020c100c06110c0304060e1f0206070815032e 67
    0x903e01003a120441d4200401040d0009010f2840703040c007000340c00500b800311001c0341400c0c41c0d80a00d8119002425060038914428803540006c840c00c1e00688000d00003e03c1e01c010481c029101c00300100c000320142c0815861076407116500e114600070007107489804569048240d210b0f04c00e9031480790300403507103200701540c0011014034020251017040003e03d403d400030b00d41d41401c4a1458515600a44000e010364650301d40070000c202481c0203400f1070041c0708150001c18000e42e030078000140103c2c448a0045007150410507600c200790b41c40c96894581c40c040109030200030040c0c0f5409961810724070042d54130400c00b24108a01100038545c0000010102d071021540301c0500d12001348190303000c1041034080d2034090072078012000406c072150b00c104000c1c040188034074243d8000c1c1c40e02411020410001070070892402901d80020070045e4407000c108010b4030b0340b01446503001005440e4001e503800ca0000800d4131105184144040101515011222040e496996003001d881104041280745804031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 614197526 1250 614196276 614196283
    0xd0921050a0f03180b0a021b070f0510051605070302031002180604050303091009150305061807020613170c061803030903030a111b0102090301060e10171c02 69
    0x10308080014028034011024a4000d2040d001300118114825040c03c040d580c4083c2c1c0280010040307440d0b65001e0014528441c6039030100100040f4403000b0f04141070504248039680c2c03500d98856440344580e85e85c0151031075040300860f41700d000c901140031444982814031529003029940001d4041c41041e03640c02000c0e2070f0342d029005844400e50078032041c045600421216000d1030265a5268004216034420b602c0c0180c180b500382a4541407260b4181d0b650304c818410301030a1500100400e80341c9003003110b0b030320b8000da90f8180015017034500701e00d43c104000000d59400c0c00500c1a9207000c4140c2140d0240051074840118525000c103060760390700b07125054641c0b45c0b8000c0d20055a0406e03850151103c00c1c901100352480354140b54000c604682d2940700d080090000441d400080150400c16004568202d051030400300c0f5200f0005030781d0f00c459209040c2164020350114403140a12420b1085210341070000c80d04440088008800d080c2101c140c580c02c0240d86008000b005104e007110582140c0c010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 614198776 1250 614197526 614197537
    0x250204091b140d02060f0c0a050d0512010902070c0608060411030411010212030f06090402040212040606030314040308090f1f0801060906050a0e1207050a090e06090307080d092105 79
    0xc45000d49091140b200740714148200040003035111806104040451030014003421a4003201001c85010114645420f8240b10380d0718103210000304000f40f0100c10f0290200c1c10703401070076038140440c60f202150b2105441c0c9501800b9003070400c400c060100e031081d515504000f608404050249075070b801d01d45480789030517800c031648901600442482c1d40841c5024800e42e44034030030301c4072101d0550343c0314810408010401130040b68410b6090007542007200000008900c2a0720890300045c6150a43c20046c00707000c408000180c05c0d80040006100050b049402d0b2001910140e808020b02c1000e00c0c0001d81d4030600c9080020b00380c4e041c00004a1283d03201510303e040340d0480e111032007078075101d00044a6034800c2c441064041405900c134401c45050040740900a65841c0003130346c4c1d00380d803980001442c500256001e100ca4039141c5258540401050050a811544d00d00041d0f140c0a210b030340d0507241e030041040d8043c0311581d400c0038006004201100075207541003644031a022410f034881c00303016038000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 614200026 1250 614198776 614198789
    0x190b0304060c080402010210201c0f1803050d0b091317040e1807030b0916150e151603120524041109060301030c051203250204091b 58
    0x186400702d6555805440b40e1400785406074040d00140400400e1138002d44032440a020610102c1004042a00400d8000d42140d040c0d814030b103035a11070070b2121441620710401e49200302e14608120044800b90303c048403010035074942403103926455030400f10b0005110300520240c00014030010410aa1907403444109268400d1100921306600540c000c0300134019406221035a1900130081500c02c0b003030206103042200d03150101c81c266074407036a4043c210702e01030340c180c290755204480380014055901244d0000d00300d0410300c600c1e0b50900c018010040e6413100030180c0241e0b0f21484090301901074004641d142012a514100510072034074000b00381c5009500540341007031400d03001c01c03581902e071440c1d080000801000d00c20340300e880b103081100038240c3c15401c003404101040440c1c12500d407071001d98002c40c02124030060140c5031406000c400c3c442403a6123446038200700680700c0d003000300c080100b040c80e140c810002c11080740352012600400c40d01030040e11084000740d803040d4010f80040d900c001d4805 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 614201276 1250 614200026 614200031
    0x606090617010308070212030d290111030f1605070e04230a060e0106030c0e0a111c0b01090306021b0f01020a050306060d20072f0906190b030406 64
    0xc8001c0d01a08064082c00001c1c0030710302c1000600094600001c103584260440403c0e80d25000c0482d4118084032842c005114600301c0108206000c0340142e0180c588500080c2441203101745086030207500c0f40b082e03c800c04102e410100d84920340d25070340c1d40000e02480d484001c484c007054590101007407140081324220344500c5441c16104030182c1d1958515280003182d0000c1290070718542c0c0c1c980280c07000440324181ca40d680c490010104218030001d500400b114280fa09180c00c2524001054801000c0ca0aa00303010400012110481c041d41c9681c0d00550345c200001ea501c90380d4012a442d586682c03000d03280a00104951130140c841003600602d070382c540401c072903a100100c0c0c0344a090340500c00e00c110100e00107100045550030600c0061408021040300002c1a80c5005060301c0c80c580b842c460b030f208080d0003007190401c111404100c2c04641c291035020040c0302c80d00c0103082c40305508c0401e0300c50182c0c402c10041106600c40c041203164919140131040f05440e11002d21003440e8004a4081e520b0740d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 614202526 1250 614201276 614201297
    0x30706030f0b06090603160e0a09061a0304020307120f0602041401110c131d0f0d030b0108060d060c110628050609010e130501021305040c0801230d020406060906 71
    0x20f410402c444000c0d4000e4001c5066560b0100701186115251681c0c0c000c1c0301c02c03450248041e548102420019210352200000e925062084903400c01e68500440d04070440708005000160b0307000070f1208102c684000005c580340d448c6280014602607e030a0052001d40003280100700000742444c000900d21082c2c1e80d070250500d910700501c0d51610a10480c13500694442d201d0046450a900701400801e003150f04d511150005649c1c85240c05c468041c20300d00c507000405c030514020f40c5030044c00c00c444000d00c0c20004600b0048005840201503600042035650b503041e055000e0740c021400e01c00200400400d41d002d078544103486141203c000c1366501c1d5003400030014841e0a12043c440c0c140942e001a07c25211a0300f09103c6440b04000501401d00f0447c40c40191000210709000810b4004a06014005007074500000d000940e5012413101d01032105010042c80000c680d01d00401c1c030003c910300c854456040c05c0c0003150640f184403074060b4000303080440109403950410850f01c210341956072005501c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 614203776 1250 614202526 614202529
    0x2130b0102060901140a0f0612030503010617040231060b1c1802010c0c1211090c1c0b0d08030f010314030313020904060b04020c060702010609020f030a05040f02030706030f0b 77
    0xf01e48170b140f03a0040000440120382e1442c05a1300c02d0b610180f03214000160385445d440c444040841018089001640000041c064580d21480000c0c01180c080c640f100359007029400a0345809e421449201146040545652882102c1800c1d4440b540050b000b00503081d1110558034695016200c0c80f0720011f4054102c41045842c0d00c2908012000144034500c400025401181c0c40200410291080c450188000c618103107400c000c0c804180c4280ca09040311601d000c2848021000186021104681840b0700c1d01d481c00c1114032050042030540c0300040c09400d00e400a0045078000c41c0140c003580020042224404401d10703400d050301c5c000c5100a00340050a1202552440101d03421181c1d0642c00080d18010305000009941080c071503e804202c0c0d81861000c28104e0f00091220a080d92140c014001000c0c1c080c410007002d0901048194034004000c1c440e141c09210190600070f41542d9400058113020319502c1c40c0794926030040550b040702d90740741e5005018101c0180b0705801c4070300d490800c1d01079 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 614205026 1250 614203776 614203781
    0x2060108060709060c0209060a03050601180c030e03070204050903040909030201240f15050d020f07150c05071506050306040503030103120801050108041101020703050715090b03010b121302130b0102060901 90
    0x80b203c82d940e6805c900c0c2c48560a00080d6180a807225822542184020001070014018175001e08a025580b8001c10300d01068907060395405003040d400e06180c00c8410f03200b20700c00b20840d2081c0e40c0603903021a150702c60b40c9072a46140f240e80d015503202443c1c454144200756040d005005940b100f40d0f105045c41d14003150240700d42c0030078402c207942d03400390420420100c007003003506101c003124078100b00d42050807001c400c5050381c0c04040c2c1c0200442c400a0300c0c100300f004200040c28498032881c8104050039214401505610801401415441000a03a0505021940c00c414050100541600e00c1810603241c5203503203030003c0c002107450b6409812408081d5100b420030b1030403500140d56842c11602c45032198180040c0300c1456a0440c0101c3c0ca020020910400c01d02004007984060540110360003c00181155116080055013074010001081803403d84400e8a8989030740d2a0f1085241d124041407400e20382c500c3c40001e403c8000990720340c0100350154030040c0e6060081c0c00340c0d2403d580da20010380c01c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 614206276 1250 614205026 614205029
    0xa02040f0b03010f05010c060f061403010f0606020721020a51030b0307180c031505011413090c030606020f2109090a05061203120721020a02060108060709 68
    0x1407441c0c0e41c030350030801c640c030a00421f41103e0246900064112200740704400751051900500800e10700a81403440c28207007407040640010302d2440c104a11414414000c1d2240414030074064502412a83c1c595210403011911460590051071081819911a8100c8030b01c1e80950111a605000811144003a244d810f4035413941c900610f98081408441500321150004800c00c1c0c2c420595552400748407510108200e001404040a580300440d00704070f9560f02382c6421184a104040c1045180d690840d0884580303400d0300c1c030900f04203072400e50f1841c41c0340040c0290744c5103400c5100e02540014800507d40c1c48410f09107016682488500e48504003641e903051078124522199201c500e4550340c0c5140e084003518003205683c0030600d802c000900080040390152529003d095441040c4082d41c9041d00303044d8103440144014500b84086d00300e005000380b000030165410b001c00400d10400060310b1b07009190005c00e040008546451030034400035550002405014220b02c00d441c0890b41c501e0280e200d030710 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 614207526 1250 614206276 614206289
    0x40c081605070f060e0606040b0f0303071205090d1202011b050d09080426071d16090306020c03130605090307090b03100516090504050c1b0f060a02040f0b0301 70
    0x80051100c24048406500158055504040210702c540c0050058055070b0025040b0302c3c000c02c0c882c102041000221400e001d510f03845041c114201514031f84000c41a039442903004210303036100840400d010340340e07880b412281c20303845443c81040398100000703490612440e129543c0200510240b1f4840c5010201c00c80c880c500109609002010003018260011500c4910402c40300d402c0c1035540710707442c501313051842c060503400100c08400f0300418010004a0024180550400507107020905001c0724030300050884480c1d008030117102d254060103004076a0055900c540304640c1e4441d2880c619440360841c0140809100000400082103441481511880c00009000e052640e280518002c001d1900c0d408440d0503015211800c420310140d481417600c06c88650b290070740010b04400700203040c0100b07074100b184100e240000b0b00c4001d40c001e00a44048442c11b8009420441040024074582412034000002500c2500308100100c41690051320885101901e070050260302d8901c0c48030390380024000c08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 614208633 1107 614207526 614207551
    0x15010e0a0915020d230103120c030e090a0c0e03120a03090f02060c0a0b011706040b0c0c06070e10030b0303071106040305010c1e170708060307180b040c08 68
    0x4100c011079481d89040c1759819951030110018004200208011001d00c01204250203000ca0807502d00008200c0324441c90040d603100b025006425140c00080c01440110300c80303040000d4442181180210100d0811000b20802c80040c08204010b9480c00351058200016840c0c104c010a40703205ca00c0090b0003140300500304808195010780c810610320280d0440c1058102d004641c9903000baa03c0451171449454905460500d4081c0700841ea40c8d500078001405502030304000040b0364050291150304201c14040016401c9542504100f40c05070803c110b41230008441c02c1c99046081030040c6002d040649a0300c0340b03400c6070340c941040300c0072540021504c0001d100340b60400800c2d20182c503000414000d02c000142c9110340c00340844c0103000c40d540108559507401d000800240c802d40011401d09842d030710600019141020071240204e140510b030350f0003a440394a0f658802c0002465070f = true := by decide +kernel

theorem cover : BRFrame.Cov 614028776 614208633 := by
  have h0 := BRFrame.cov_init 614028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 614028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 614028776 ≤ n) (h2 : n < 614208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
